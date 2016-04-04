/*
 * Yusuf Roohani - yhr
 * This is the main code for a caching web proxy. It waits for clients
 * and creates a new thread for each client. The thread detaches and the
 * proxy does not wait for its completion. There are several error 
 * handling functions to deal with badly formed requests.
 *
 * The cache contains objects of uniform size. For each new connection,
 * the proxy checks whether the response to a similar request is present
 * in the cache or not. If it is, this response is returned and no new
 * connection to the server is initiated.
 *
 * If the response does not exist in the cache. Then a new buffer is 
 * allocated on the heap for each connection and the response is written into 
 * it. This procedure is independent to each thread and is thus thread safe. 
 * Once the size of each buffer has been determined to be less than the cache 
 * object limit, it is inserted into the cache queue (this must wait for the
 * completion of all queued cache reading operations). If there are too many 
 * objects in the cache, then the least recently usd object (i.e. the front)
 * is evicted.
 *
 * The cache allows multiple readers to traverse its queue and read the
 * contents of any element. However, only one element is allowed to write to
 * the cache. When this occurs, all readers must wait In case of a cache hit, 
 * the element used needs to be moved to the rear of the queue - this 
 * operation is treated similar to a write operation.
 *
 * v4
 */

#include <stdio.h>
#include <signal.h>
#include "csapp.h"
#include "cache.h"
/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* Misc macros */
#define L2R 0
#define R2L 1

/* Request and response data structures */
typedef struct{
   char proto[MAXLINE], serv_add[MAXLINE];
   char method[8], content[MAXLINE], port[MAXLINE];
   char misc_header[MAXLINE];
   char serv_hostname[MAXLINE];
   char serv_string[MAXLINE];
   char addenda[MAXLINE];
   int clientfd;
   int no_host;
}req_info;

typedef struct{
   int bin_flag;
   int content_flag;
   ssize_t content_len;
   char* buf;
   ssize_t fpos;
}resp_info;

/* Function prototypes */

/* Main proxy implementation and request handling*/
void* read_req(void* connfdp);
int handle_req(int clientfd, char* in_buf, int no_host);
int connct(rio_t* rio, req_info* req, char* buf, int* serverfd, ssize_t len);
ssize_t get_cont(rio_t* rio, int clientfd, resp_info* resp); 

/* Parsing functions */
ssize_t parse_req(req_info* req, char* buf);
ssize_t parse_resp(rio_t* rio, int clientfd, resp_info* resp); 
int parse_addr(req_info* req, char* buf, ssize_t* byte_left);

/* Request modifications and error handling */
void change_req(char* client_buf, int* no_host, ssize_t* size);
int check_req(char* method, char* misc, int fd);
void req_error(int fd, char* cause);
void clienterror(int fd, char *cause, char *shortmsg, char *longmsg);
void str_sep(char* full, char* b, char sep, int flag); 

/* Cache globals */
ssize_t cache_size = 0;
int readcnt = 0;

/*
 * main - Initializes cache, mutexes, signal handler. Waits for clients and
 * dispatches new threads.
 */
int main(int argc, char **argv)
{
   int listenfd;
   int *connfdp;
   char hostname[MAXLINE], port[MAXLINE];
   socklen_t clientlen;
   struct sockaddr_storage clientaddr;
   pthread_t tid;
   
   /* Initialize the cache. Inserting an empty element so that future
    * additions to the cache become smoother.  */
   struct cache_entry* empty = malloc(sizeof(struct cache_entry));
   empty -> size = (ssize_t) 0;
   empty -> next = NULL;
   empty -> prev = NULL;
   empty -> content = "Empty";
   rear = empty;
   front = rear;

   /* Initiazlise read and write mutexes */
   Sem_init(&rd_mutex, 0, 1);
   Sem_init(&wr_mutex, 0, 1);

   /* Ignore SIGPIPE, let I/O functions deal with it as per situation*/
   Signal(SIGPIPE, SIG_IGN);  
    
    /* Check command line args */
    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(1);
    }
    
    /* Check listening port availability */
    if ((listenfd = Open_listenfd(argv[1])) < 0){
	printf ("Bad listening port, please try again \n");
        return 0 ;
	}
    
    /* Wait for requests */
    while (1) {
        clientlen = sizeof(clientaddr);
        connfdp = malloc(sizeof(int));
        if ((*connfdp = Accept(listenfd, (SA *)&clientaddr, &clientlen)) < 0 ){
        	continue;
	}
	Getnameinfo((SA *) &clientaddr, clientlen, hostname, MAXLINE,
                    port, MAXLINE, 0);
        Pthread_create(&tid, NULL, read_req, (void*)connfdp);
    }

   return 0;
}

/*
 * read_req - Read HTTP request into a buffer, and send read buffer to 
 * request handler
 */
void* read_req(void* connfdp)
{   
    /* Deal with thread detachment and free arguments*/
    pthread_detach(pthread_self());
    int fd = *((int *)connfdp);
    Free(connfdp);

    char buf[MAXLINE],client_buf[MAXLINE];
    rio_t rio;
    ssize_t size;
    int no_host = 1;
    Rio_readinitb(&rio, fd);

    /* Read request line and headers from client.
     * Make changes if needed (easier to make now than later) */  
    Rio_readlineb(&rio, client_buf, MAXLINE);
    strcpy(buf, client_buf);
    while(strcmp(client_buf, "\r\n")) { 
        size = Rio_readlineb(&rio, client_buf, MAXLINE);
        change_req(client_buf, &no_host, &size);
        strncat(buf, client_buf, size);
    }
    strcat(buf, "\r\n");

    /* Handle request */
    handle_req(fd, buf, no_host);

    /* Close connection and detach */
    Close(fd);
    return NULL;
}

/*
 * handle req - Handles all aspects of a paritcular request including server
 * interactions. Calls functions to parse request, check cache or connect to
 * server, and return response to client.
 */
int handle_req(int clientfd, char* in_buf, int no_host)
{
   req_info req;
   resp_info resp;
   resp.buf = NULL;
   resp.fpos = 0;
   rio_t rio;
   int caching = 1;
   int serverfd;    
   ssize_t len;

   /* Parse request */
   if (strlen(in_buf) < 6){
	return 0;
    }
   else{
      req.clientfd = clientfd;
      req.no_host = no_host;
      if (!(len = parse_req(&req, in_buf))){
      return 0;
      }
   }
  
   /* Set up request details and connect to server if needed */ 
   switch (connct(&rio, &req, in_buf, &serverfd, len)){
      case 2: {caching = 0;
              break;}
      case 1: {caching = 1;
              break;}
      default: close(serverfd);
	       return 0;
   }

   /* Read response header and set appropriate flags*/
   resp.bin_flag = 0;
   resp.content_flag = 0;
   resp.content_len = 0;
   if (caching){
      if ((resp.buf = (char*)(malloc(MAX_OBJECT_SIZE))) == NULL){
         caching = -1;
      }
      else if ((parse_resp(&rio, req.clientfd, &resp)) == 0){
         caching = -1;
      }
   }

   /* Read content if attached */
   if (resp.content_flag){
	 if ((get_cont(&rio, req.clientfd, &resp)) == 0)
           caching = -1;
   }

   /* Add new cache entry if needed */
   switch (caching){
      case 0: break;
      case 1:  {P(&wr_mutex);
		  add_entry(in_buf, resp.buf, resp.fpos);
		  V(&wr_mutex);
	       }
      case -1: Close(serverfd); 
   }
   return 0;
}

/*
 * connct - Checks if response to current request may already be cached. If so,
 * reads back from the cache. Otherwise connects to server.
 */
int connct(rio_t* rio, req_info* req, char* buf, int* serverfd, ssize_t len){
   struct cache_entry* cached = NULL;
   int cache_flag = 1;

   /* Check cache - read shared memory then update LRU(modify shared memory) */
   if ((cache_flag = sync_read(cached, &req->clientfd, buf)) == 1){
      return 2;
      }
   /* Cache MISS - Connect to server and make reques */
   else {
      if ((*serverfd = Open_clientfd(req->serv_hostname,req->port)) < 0 ){
	 req_error(req->clientfd, "Address");
	 return -1;
      }
      Rio_readinitb(rio, *serverfd);
      if (Rio_writen(*serverfd, req->serv_string, len) == -2){
	 return -(*serverfd);
      }
   }
   return 1;
}

/*
 * get_cont - Read from rio and write to clientfd content_len bytes of text
 * or binary content.
 */
ssize_t get_cont(rio_t* rio, int clientfd, resp_info* resp){
   ssize_t s_cnt = 0;    // short count
   ssize_t tot_read = 0;
   char buf[MAXLINE];
   int caching = 1;
   int leave = 0;

   if (resp->content_len){  
      while((tot_read < resp->content_len) && (!leave)) {
	 if ((s_cnt = Rio_readnb(rio, buf, MAXLINE)) <= 0){
	    leave = 1;
	 }
       
         /* Check if cache block isn't already full or if no bytes were read */
	 if ((caching) && (!leave))
	    caching = cache_write(resp->buf, buf, s_cnt, resp->fpos + tot_read);
	 
         /* Write to client anyway */
         if (Rio_writen(clientfd, buf, s_cnt) == -2){
	    return 0;
	 }
	 tot_read += s_cnt;
      }
   }
   else
      do{
	 if ((s_cnt = Rio_readnb(rio, buf, MAXLINE)) <= 0){
                  leave = 1;
	}	

          /* Check if cache block isn't already full or if no bytes were read */
	 if ((caching) && (!leave))
	    caching = cache_write(resp->buf, buf, s_cnt, resp->fpos + tot_read);
	 
         /* Write to client anyway */
         if (Rio_writen(clientfd, buf, s_cnt) == -2){
	    return 0;
	 }
	 tot_read += s_cnt;
      }while (!leave);
   resp->fpos += tot_read;

   /* Discard cache buffer if exceeds the size limit */
   if (discard(resp->buf, caching, resp->fpos))
        return 1;
   else
       return 0;
}

/*
 * parse_req - Parses request into appropriate sections of the req_info struct
 * Makes some changes if needed.
 */
ssize_t parse_req(req_info* req, char* buf){
   ssize_t byte_left, len;
   ssize_t add_len = 0;
   
   if ((parse_addr(req, buf, &byte_left)) == 0)
      return 0;
   
   /* Create HTTP request line to send server */
   sprintf(req->serv_string, "GET /%s HTTP/1.0 ", req->content);
   len = strlen(req->serv_string);
   if (byte_left>2){
      memcpy(req->serv_string + len, req->misc_header, byte_left);
      len += byte_left;
   }
   memcpy(req->serv_string + len, "\r\n", 2);
   len += 2;

   if (!req->no_host){
      add_len = sprintf(req->addenda,"Proxy-Connection: close\r\n\r\n");
   }
   else{
      add_len = sprintf(req->addenda,
      "Host: %s\r\nProxy-Connection: close\r\n\r\n", req->serv_hostname);
   }
   memcpy(req->serv_string + len, req->addenda, add_len);
   len += add_len;

   return len;
}

/*
 * parse_addr - Called by parse_req. Parses the address information.
 */   
int parse_addr(req_info* req, char* buf, ssize_t* byte_left){
   ssize_t tot_len;
   char* sep_ptr = NULL;
  
   /* Get moethod, address and protocol */
   sscanf(buf, "%s %s %s", req->method, req->serv_add, req->proto);
   tot_len = strlen(req->method) + strlen(req->serv_add) 
      + strlen(req->proto) + 3;   
   *byte_left = (strstr(((char*)buf+tot_len),"\r\n\r\n") - 
	 ((char*)buf+tot_len));

   /* Get other headers sent by browser */
   memcpy(req->misc_header, (buf + tot_len), *byte_left);

   /* If address has http:// attached to it  */
   if (strstr(req->serv_add, "http://") != req->serv_add){
      strcpy(req->serv_hostname,req->serv_add);
   }
   else
      sscanf(req->serv_add, "http://%s", req->serv_hostname);
   
   /* Check request method and badly formed request */
   if (check_req(req->method, req->proto, req->clientfd) != 1)
      return 0;

   /* Separate port number and content request*/
   /* If there is a content request */
   if((sep_ptr = index(req->serv_hostname,'/')) != NULL){    
      /* With port number */   
      if ((index(req->serv_hostname, ':') != 0) &&
            (index(req->serv_hostname,':') < index(req->serv_hostname,'/'))){
	 str_sep(req->serv_hostname, req->port, ':', L2R);
	 str_sep(req->port, req->content, '/', L2R);
      }
      /* Wthout port number */
      else {
	 str_sep(req->serv_hostname, req->content, '/', L2R);
	 strcpy(req->port,"80");
      }
      *sep_ptr ='\0';
   }
   
   /* If there is no content request*/
   else {
      /* With port number */
      if ((index(req->serv_hostname, ':') != 0)){
	 str_sep(req->serv_hostname, req->port, ':', L2R);
	 str_sep(req->port, req->content, '/', L2R);
      }
      /* Without port number */
      else {
	 strcpy(req->port,"80");
      }
   }
   return 1;
}


/*
 * parse_resp - Reads headers labels and header data. Determines presence of
 * content, its length and type
 */
ssize_t parse_resp(rio_t* rio, int clientfd, resp_info* resp){
   char buf[MAXLINE];
   char header_label[MAXLINE], header_data[MAXLINE];
   char type[MAXLINE];
   ssize_t s_cnt = 0;        // Bytes read per line
   int caching =1;
   ssize_t tot_read= 0;     // Total bytes read/buffer pointer

   while(strcmp(buf,"\r\n")){
      /* Read from server */
      s_cnt = Rio_readlineb(rio, buf, MAXLINE);
      /* Write to cache buffer*/
      if (caching)     
	 caching = cache_write(resp->buf, buf, s_cnt, tot_read);

      /* Parse headers */
      sscanf(buf, "%s %s", header_label, header_data); 
      if (strstr("Content-Type:Content-type:", header_label)){
	 resp->content_flag = 1;
	 str_sep(header_data, type, '/', 0);
	 if (strstr("Imageimage",header_data) || strstr("plainPlain", type)){
	    resp->bin_flag = 1;
	 }
      }
      if (strstr("Content-Length:Content-length:", header_label)){
	 resp->content_flag = 1;
	 resp->content_len = atoi(header_data);
      }

      /* Write to client */
      if (Rio_writen(clientfd, buf, s_cnt) == -2){
	 return 0;
      }
      tot_read += s_cnt;
   }

   resp->fpos = tot_read; 
   if (discard(resp->buf, caching, tot_read))
	return 1;
   else
        return 0;
}


/*
 * change_req - Modifies connection header if needed. Checks if host
 * information needs to be added later.
 */
void change_req(char* client_buf, int* no_host, ssize_t* size){
      if (!strncmp(client_buf,"Connection:",11)){
         strncpy(client_buf+11," close\r\n",8);
         *size=11+8;
       }
       else if (!(strncmp(client_buf,"host:",5)) ||
             (!strncmp(client_buf,"Host:",5))){
         *no_host = 0;

       }
}

/* 
 * check_req - Checks for illegal methods or badly formed requests 
 */
int check_req(char* method, char* misc, int fd){
   if (strncmp(method, "GET", 3)){
      req_error(fd, "Method");
      return 0;
   }
   if (strncmp(misc, "HTTP/", 5)){
      req_error(fd, "Protocol");
      return 0;
   }
   return 1;
}

/*
 * str_sep - Useful routine for separating strings using a symbol
 * Can specifiy whether read should be L2R or R2L
 */
void str_sep(char* full, char* b, char sep, int flag){
   char* sep_ptr;
   if (flag == L2R){
      sep_ptr = index(full, sep);
   }
   else{
      sep_ptr = rindex(full, sep);
   }
   if(sep_ptr) {
      strcpy(b, sep_ptr+1);
      *sep_ptr ='\0';
   }
}

/*
 * req_error - Calls clienterror with commonly used input strings when 
 * there is a badly formed request
 */
void req_error(int fd, char* cause){
   clienterror(fd, cause, "Bad request",
    "Format [method] http://[addr]:[port]/[content] [protocol] [headers]");
} 

/* 
 * clienterror - Prints a browser firnedly error message 
 */
void clienterror(int fd, char *cause,
      char *shortmsg, char *longmsg)
{
   char buf[MAXLINE], body[MAXBUF];

   /* Build the HTTP response body */
   strcat(body, "15-213 Proxy Error! <body bgcolor=""ffffff"">\r\n");
   sprintf(body, "%s %s !! Check %s !\n \r\n", body, shortmsg, cause);
   sprintf(body, "%s<p>%s\r\n", body, longmsg);

   /* Print the HTTP response */
   sprintf(buf, "HTTP/1.0 %s\r\n", shortmsg);
   Rio_writen(fd, buf, strlen(buf));
   sprintf(buf, "Content-type: text/html\r\n");
   Rio_writen(fd, buf, strlen(buf));
   sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
   Rio_writen(fd, buf, strlen(buf));
   Rio_writen(fd, body, strlen(body));
}
