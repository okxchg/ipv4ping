/* IPv4 ping
 * 
 * Based on example in Unix Network Programming with few minor and major
 * differences:
 *  * uses select as a timer (as in freebsd ping), not SIGALRM
 *  * doesn't call async-unsafe functions from within a signal handlers
 *  * uses SO_TIMESTAMP
 *  * doesn't support IPv6
 *  * doesn't use libraries and functions from the book
 *
 * This is also much less portable, mainly because it's relying on select to
 * update it's timeout know and the only platform I know of with this behaviour
 * is Linux.
 *
 * Copyright (c) Oliver Kindernay 
 * */
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include <unistd.h>
#include <errno.h>
#include <sys/time.h>

#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/ip_icmp.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <strings.h>
#include <signal.h>

#define MAXIPHDRLEN 60
#define MAXICMPHDRLEN 8
#define MAXDATALEN 56

static volatile sig_atomic_t finish_up;
static int pid;

static void usage()
{
    puts(
        "USAGE: ping [-h] [-d] <host>\n"
        "       where <host> is IPv(4|6) address or domain name"
        "\n"
        "OPTIONS:\n"
        "   -h  print help\n"
        "   -d  debug mode on"
    );
}

static void sys_error_quit(const char *s)
{
    perror(s);
    exit(EXIT_FAILURE);
}

static void sys_error(const char *s)
{
    perror(s);
}

static void error(const char *fmt, ...)
{
    va_list vl;

    va_start(vl, fmt);
    vfprintf(stderr, fmt, vl);
    va_end(vl);

    exit(EXIT_FAILURE);
}

static void fatal(const char *fmt, ...)
{
    va_list vl;

    va_start(vl, fmt);
    vfprintf(stderr, fmt, vl);
    va_end(vl);

    abort();
}

static int do_debug;

#define debug(s) debug__("%s:%d " s "\n", __FILE__, __LINE__)
#define vdebug(fmt, ...) debug__("%s:%d " fmt "\n", \
                            __FILE__, __LINE__, __VA_ARGS__)

static void debug__(const char *fmt, ...)
{
    if (do_debug) {
        va_list vl;

        va_start(vl, fmt);
        vfprintf(stderr, fmt, vl);
        va_end(vl);
    }
}

void finishit(int signo)
{
    finish_up = 1;
}

/*
 * from bsdping
 *
 * tvsub --
 *	Subtract 2 timeval structs:  out = out - in.  Out is assumed to
 * be >= in.
 */
static void tvsub(struct timeval *out, struct timeval *in)
{
    if ((out->tv_usec -= in->tv_usec) < 0) {
        --out->tv_sec;
        out->tv_usec += 1000000;
    }
    out->tv_sec -= in->tv_sec;
}

static void proc(unsigned char *buf, size_t buflen, struct msghdr *msg)
{
    struct ip *iphdr;
    int iphdr_len;
    struct icmp *icmphdr;
    struct cmsghdr *cmsg;
    struct timeval *tv_send;
    struct timeval tv_recv;
    double rtt;

    if (buflen < 20) {
        error("packet with invalid length recieved (%d bytes)", buflen);
        return;
    }
        
    iphdr = (struct ip *)buf;
    iphdr_len = iphdr->ip_hl << 2;
    if (iphdr->ip_p != IPPROTO_ICMP)
        return;

    if (iphdr_len+8+MAXDATALEN > buflen) {
        error("ip length field doesn't seem to be right (%d)", iphdr_len);
        return;
    }

    icmphdr = (struct icmp *)(buf + iphdr_len);
    if (icmphdr->icmp_id == pid && icmphdr->icmp_type == ICMP_ECHOREPLY) {
        for (cmsg = CMSG_FIRSTHDR(msg); cmsg != NULL; cmsg = CMSG_NXTHDR(msg, cmsg)) {
            if (cmsg->cmsg_level == SOL_SOCKET &&
                    cmsg->cmsg_type == SCM_TIMESTAMP &&
                    cmsg->cmsg_len == CMSG_LEN(sizeof tv_recv)) {
                /* Copy to avoid alignment problems: */
                memcpy(&tv_recv, CMSG_DATA(cmsg), sizeof(tv_recv));
                break;
            }
        }
        tv_send = (struct timeval *)icmphdr->icmp_data;
        tvsub(&tv_recv, tv_send);
        rtt = tv_recv.tv_sec * 1000.0 + tv_recv.tv_usec / 1000.0;
        printf("%d bytes from %s: req=%d ttl=%.3d time=%.3f ms\n", buflen,
                inet_ntoa(((struct sockaddr_in *)msg->msg_name)->sin_addr),
                icmphdr->icmp_seq, iphdr->ip_ttl, rtt);
    }
}

/* 
 * Taken from bsdping/unp
 *
 * in_cksum --
 *	Checksum routine for Internet Protocol family headers (C Version)
 */
static uint16_t in_cksum(uint16_t *addr, int len)
{
    int	nleft = len;
    uint32_t sum = 0;
    uint16_t *w = addr;
    uint16_t answer = 0;

    /*
     * Our algorithm is simple, using a 32 bit accumulator (sum), we add
     * sequential 16 bit words to it, and at the end, fold back all the
     * carry bits from the top 16 bits into the lower 16 bits.
     */
    while (nleft > 1)  {
        sum += *w++;
        nleft -= 2;
    }

    /* 4mop up an odd byte, if necessary */
    if (nleft == 1) {
        *(unsigned char *)(&answer) = *(unsigned char *)w;
        sum += answer;
    }

    /* 4add back carry outs from top 16 bits to low 16 bits */
    sum = (sum >> 16) + (sum & 0xffff); /* add hi 16 to low 16 */
    sum += (sum >> 16);                 /* add carry */
    answer = ~sum;                      /* truncate to 16 bits */
    return(answer);
}

static void ping(int sock, struct sockaddr *addr, size_t addrlen)
{
    struct icmp *icmphdr;
    static int seq = 0;
    static unsigned char sendbuf[MAXICMPHDRLEN+MAXDATALEN];

    icmphdr = (struct icmp *)sendbuf;
    icmphdr->icmp_type = ICMP_ECHO;
    icmphdr->icmp_code = 0;
    icmphdr->icmp_id = pid;
    icmphdr->icmp_seq = seq++;

    memset(icmphdr->icmp_data, 0xa5, MAXDATALEN);
    if (gettimeofday((struct timeval *)icmphdr->icmp_data, NULL) == -1)
        sys_error("gettimeofday");

    icmphdr->icmp_cksum = 0;
    icmphdr->icmp_cksum = in_cksum((uint16_t *)icmphdr,
            MAXICMPHDRLEN+MAXDATALEN);

    if (sendto(sock, sendbuf, sizeof(sendbuf), 0, addr, addrlen) !=
            (ssize_t)sizeof(sendbuf)) {
        sys_error("sendto");
    }

    vdebug("echo seq=%d sent", icmphdr->icmp_seq);
}

static void pong(int sock, size_t addrlen)
{
    unsigned char ctrl[CMSG_SPACE(sizeof(struct timeval))];
    unsigned char recvbuf[MAXIPHDRLEN+MAXICMPHDRLEN+MAXDATALEN];
    struct msghdr msg = {0};
    struct iovec iov;
    int readb;

    iov.iov_base = recvbuf;
    iov.iov_len = sizeof(recvbuf);
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = ctrl;
    msg.msg_name = calloc(1, addrlen);
    if (!msg.msg_name)
        fatal("Out of memory");

    for (;;) {
        msg.msg_namelen = addrlen;
        msg.msg_controllen = sizeof(ctrl);
        readb = recvmsg(sock, &msg, 0);
        if (readb > 0) {
            proc(recvbuf, readb, &msg);
            break;
        }
        else if (errno != EINTR)
            sys_error("recvmsg");
    }
}

int main(int argc, char * const argv[])
{
    int opt;
    int ret;
    int sock;
    const char *host;
    struct sigaction act;
    struct timeval timeout;
    struct addrinfo hints;
    struct addrinfo *ainfo;
    struct sockaddr *addr;
    size_t addrlen;
    fd_set rfds;

    while ((opt = getopt(argc, argv, "hd")) != -1) {
        switch (opt) {
            case 'h':
                usage();
                return EXIT_SUCCESS;
            case 'd':
                do_debug = 1;
                break;
            /* let getopt handle error messages */
            default:
                return EXIT_FAILURE;
        }
    }

    if (optind >= argc)
        error("You have to specify a host\n");
    host = argv[optind];

    bzero(&hints, sizeof(hints));
    hints.ai_flags = AI_CANONNAME;
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_RAW;
    hints.ai_protocol = IPPROTO_ICMP;

    ret = getaddrinfo(host, NULL, &hints, &ainfo);
    if (ret != 0)
        error("getaddrinfo(%s): %s\n", host, gai_strerror(ret));

    if (ainfo->ai_next)
        vdebug("%s translated to more than one address", host);

    addr = ainfo->ai_addr;
    addrlen = ainfo->ai_addrlen;

    sock = socket(ainfo->ai_family, ainfo->ai_socktype, ainfo->ai_protocol);
    if (sock == -1)
        sys_error_quit("socket");
  
    { int on = 1;
        if (setsockopt(sock, SOL_SOCKET, SO_TIMESTAMP, &on, sizeof(on)) == -1)
            sys_error_quit("setsockopt SO_TIMESTAMP");
    }

    /* 16 bit ident for icmp packets */
    pid = getpid() & 0xffffff;

    /* setup signal handlers */
    act.sa_handler = finishit;
    sigemptyset(&act.sa_mask);
    act.sa_flags = 0;
    act.sa_flags |= SA_RESTART;
    if (sigaction(SIGINT, &act, NULL) == -1)
        sys_error("sigaction");

    /* drop privs */
    setgid(getgid());
    setuid(getuid());

    printf("PING %s (%s)\n", ainfo->ai_canonname,
            inet_ntoa(((struct sockaddr_in *)addr)->sin_addr));

    /* ping pong */
    timerclear(&timeout);
    while (!finish_up) {
        FD_ZERO(&rfds);
        FD_SET(sock, &rfds);
        ret = select(sock+1, &rfds, NULL, NULL, &timeout);
        if (ret == 0) {
            ping(sock, addr, addrlen);
            timeout.tv_sec = 1;
            timeout.tv_usec = 0;
        }
        else if (ret == 1) {
            pong(sock, addrlen);
        }
        else {
            if (errno != EINTR) {
                sys_error("select");
                timerclear(&timeout);
            }
        }
    }
    return 0;
}
