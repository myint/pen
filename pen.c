/*
   Copyright (C) 2000-2014  Ulric Eriksson <ulric@siag.nu>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston,
   MA 02111-1307, USA.
*/

#include "config.h"

#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <netdb.h>
#include <sys/types.h>
#include <assert.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <signal.h>
#include <stdlib.h>
#include <stdarg.h>
#include <ctype.h>
#include <time.h>
#ifdef TIME_WITH_SYS_TIME
#include <sys/time.h>
#endif
#include <sys/wait.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/stat.h>
#ifdef HAVE_POLL
#include <sys/poll.h>
#endif	/* HAVE_POLL */
#ifdef HAVE_KQUEUE
#include <sys/event.h>
#endif
#include <fcntl.h>
#include <unistd.h>
#include <syslog.h>
#include <string.h>
#include <pwd.h>

#ifdef HAVE_SSL
#include <openssl/ssl.h>
#include <openssl/err.h>

#define SRV_SSL_V23 0
#define SRV_SSL_V2 1
#define SRV_SSL_V3 2
#define SRV_SSL_TLS1 3

static char ssl_compat;
static char require_peer_cert;
static char ssl_protocol;
static char *certfile;
static char *keyfile;
static char *cacert_dir;
static char *cacert_file;
static SSL_CTX *ssl_context = NULL;
#endif  /* HAVE_SSL */

#ifdef HAVE_GEOIP
#include <GeoIP.h>
GeoIP *geoip4, *geoip6;
#endif

#define ACE_IPV4 (1)
#define ACE_IPV6 (2)
#define ACE_GEO (3)

#define BUFFER_MAX 	(32*1024)

#define CLIENTS_MAX	2048	/* max clients */
#define SERVERS_MAX	16	/* max servers */
#define ACLS_MAX	10	/* max acls */
#define CONNECTIONS_MAX	256	/* max simultaneous connections */
#define TIMEOUT		5	/* default timeout for non reachable hosts */
#define BLACKLIST_TIME	30	/* how long to shun a server that is down */
#define TRACKING_TIME	0	/* how long a client is remembered */
#define KEEP_MAX	100	/* how much to keep from the URI */
#define WEIGHT_FACTOR	256	/* to make weight kick in earlier */

typedef struct {
	int downfd, upfd;
	unsigned char *downb, *downbptr, *upb, *upbptr;
	int downn, upn;		/* pending bytes */
	unsigned long ssx, srx;	/* server total sent, received */
	unsigned long csx, crx;	/* client total sent, received */
	int clt;
	int index;		/* server index */
#ifdef HAVE_KQUEUE
	int i;			/* connection index */
#endif
#ifdef HAVE_SSL
	SSL *ssl;
#endif
} connection;

typedef struct {
	int status;		/* last failed connection attempt */
	int acl;		/* which clients can use this server */
	struct sockaddr_storage addr;
	int c;			/* connections */
	int weight;		/* default 1 */
	int prio;
	int maxc;		/* max connections, soft limit */
	int hard;		/* max connections, hard limit */
	unsigned long long sx, rx;	/* bytes sent, received */
} server;

typedef struct {
	time_t last;		/* last time this client made a connection */
	struct sockaddr_storage addr;
	int cno;		/* server used last time */
	long connects;
	long long csx, crx;
} client;

typedef struct {
	unsigned int ip, mask;
} ace_ipv4;

typedef struct {
	struct in6_addr ip;
	unsigned char len;
} ace_ipv6;

typedef struct {
	char country[2];
} ace_geo;

typedef struct {
	unsigned char class;
	unsigned char permit;
	union {
		ace_ipv4 ipv4;
		ace_ipv6 ipv6;
		ace_geo geo;
	} ace;
} acl;

static int multi_accept = 100;
static int nservers;		/* number of servers */
static int current;		/* current server */
static int nacls[ACLS_MAX];
static client *clients;
static server *servers;
static acl *acls[ACLS_MAX];
static int emerg_server = -1;	/* server of last resort */
static int emergency = 0;	/* are we using the emergency server? */
static int abuse_server = -1;	/* server for naughty clients */
static connection *conns;

static int debuglevel;
static int asciidump;
static int foreground;
static int loopflag;
static int exit_enabled = 0;

static int hupcounter = 0;
static int clients_max = CLIENTS_MAX;
static int servers_max = SERVERS_MAX;
static int connections_max = CONNECTIONS_MAX;
static int connections_used = 0;
static int connections_last = 0;
static int timeout = TIMEOUT;
static int blacklist_time = BLACKLIST_TIME;
static int tracking_time = TRACKING_TIME;
static int roundrobin = 0;
static int weight = 0;
static int prio = 0;
static int hash = 0;
static int stubborn = 0;
static int nblock = 1;
static int delayed_forward = 0;
static int do_stats = 0;
static int do_restart_log = 0;
static int use_poll = 0;
static int use_kqueue = 0;
static int http = 0;
static int client_acl, control_acl;
static int udp = 0;
static int protoid = SOCK_STREAM;

static int port;

static char *cfgfile = NULL;
static char *logfile = NULL;
static FILE *logfp = NULL;
static struct sockaddr_in logserver;
static int logsock = -1;
static char *pidfile = NULL;
static FILE *pidfp = NULL;
static char *webfile = NULL;
static char *listenport = NULL;
static char *ctrlport = NULL;
static int listenfd, ctrlfd = -1;
static char *e_server = NULL;
static char *a_server = NULL;
static char *jail = NULL;
static char *user = NULL;
static char *proto = "tcp";

static struct sigaction alrmaction, hupaction, termaction, usr1action;

static unsigned char mask_ipv6[129][16];

static void close_conn(int);

static void debug(char *fmt, ...)
{
	time_t now;
	struct tm *nowtm;
	char nowstr[80];
	char b[4096];
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(b, sizeof b, fmt, ap);
	now=time(NULL);
	nowtm = localtime(&now);
	strftime(nowstr, sizeof(nowstr), "%Y-%m-%d %H:%M:%S", nowtm);
	if (foreground) {
		fprintf(stderr, "%s: %s\n", nowstr, b);
	} else {
		openlog("pen", LOG_CONS, LOG_USER);
		syslog(LOG_DEBUG, "%s\n", b);
		closelog();
	}
	va_end(ap);
}

static void error(char *fmt, ...)
{
	char b[4096];
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(b, sizeof b, fmt, ap);
	if (foreground) {
		fprintf(stderr, "%s\n", b);
	} else {
		openlog("pen", LOG_CONS, LOG_USER);
		syslog(LOG_ERR, "%s\n", b);
		closelog();
	}
	va_end(ap);
	exit(1);
}

static void *pen_malloc(size_t n)
{
	void *q = malloc(n);
	if (!q) error("Can't malloc %ld bytes", (long)n);
	return q;
}

static void *pen_calloc(size_t n, size_t s)
{
	void *q = calloc(n, s);
	if (!q) error("Can't calloc %ld bytes", (long)n*s);
	return q;
}

static void *pen_realloc(void *p, size_t n)
{
	void *q = realloc(p, n);
	if (!q) error("Can't realloc %ld bytes", (long)n);
	return q;
}

static char *pen_strdup(char *p)
{
	size_t len = strlen(p);
	char *b = pen_malloc(len+1);
	memcpy(b, p, len);
	b[len] = '\0';
	return b;
}

static int pen_strncasecmp(const char *p, const char *q, size_t n)
{
	size_t i = 0;
	int c = 0;

	while ((i < n) && !(c = toupper(*p)-toupper(*q)) && *p) {
		p++;
		q++;
		i++;
	}
	return c;
}

static char *pen_strcasestr(const char *haystack, const char *needle)
{
	char *p = (char *)haystack;
	int n = strlen(needle);

	while (*p) {
		if (!pen_strncasecmp(p, needle, n)) return p;
		p++;
	}
	return NULL;
}

static void init_mask(void)
{
	unsigned char m6[16];
	int i, j;

	memset(m6, 0, sizeof m6);
	for (i = 0; i < 129; i++) {
		for (j = 15; j >= 0; j--) {
			mask_ipv6[i][j] = m6[j];
			m6[j] >>= 1;
			if (j > 0) {
				m6[j] |= (m6[j-1] << 7);
			} else {
				m6[j] |= (1 << 7);
			}
		}
	}
}

static int pen_hash(struct sockaddr_storage *a)
{
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;
	unsigned char *u;

	switch (a->ss_family) {
	case AF_INET:
		si = (struct sockaddr_in *)a;
		return si->sin_addr.s_addr % nservers;
	case AF_INET6:
		si6 = (struct sockaddr_in6 *)a;
		u = (unsigned char *)(&si6->sin6_addr);
		return u[15] % nservers;
	default:
		return 0;
	}
}

/* Takes a struct sockaddr_storage and returns the port number in host order.
   For a Unix socket, the port number is 1.
*/
static int pen_getport(struct sockaddr_storage *a)
{
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;

	switch (a->ss_family) {
	case AF_UNIX:
		return 1;
	case AF_INET:
		si = (struct sockaddr_in *)a;
		return ntohs(si->sin_port);
	case AF_INET6:
		si6 = (struct sockaddr_in6 *)a;
		return ntohs(si6->sin6_port);
	default:
		debug("pen_getport: Unknown address family %d", a->ss_family);
	}
	return 0;
}

static int pen_setport(struct sockaddr_storage *a, int port)
{
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;

	switch (a->ss_family) {
	case AF_UNIX:
		/* No port for Unix domain sockets */
		return 1;
	case AF_INET:
		si = (struct sockaddr_in *)a;
		si->sin_port = htons(port);
		return 1;
	case AF_INET6:
		si6 = (struct sockaddr_in6 *)a;
		si6->sin6_port = htons(port);
		return 1;
	default:
		debug("pen_setport: Unknown address family %d", a->ss_family);
	}
	return 0;
}

/* Takes a struct sockaddr_storage and returns the name in a static buffer.
   The address can be a unix socket path or an ipv4 or ipv6 address.
*/
static char *pen_ntoa(struct sockaddr_storage *a)
{
	static char b[1024];
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;
	struct sockaddr_un *su;

	switch (a->ss_family) {
	case AF_INET:
		si = (struct sockaddr_in *)a;
		snprintf(b, sizeof b, "%s", inet_ntoa(si->sin_addr));
		break;
	case AF_INET6:
		si6 = (struct sockaddr_in6 *)a;
		if (inet_ntop(AF_INET6, &si6->sin6_addr, b, sizeof b) == NULL) {
			debug("pen_ntoa: can't convert address");
			strcpy(b, "(cannot convert address)");
		}
		break;
	case AF_UNIX:
		su = (struct sockaddr_un *)a;
		snprintf(b, sizeof b, "%s", su->sun_path);
		break;
	default:
		debug("pen_ntoa: unknown address family %d", a->ss_family);
		sprintf(b, "(unknown address family %d", a->ss_family);
	}
	return b;
}

static void pen_dumpaddr(struct sockaddr_storage *a)
{
	switch (a->ss_family) {
	case AF_INET:
		debug("Family: AF_INET");
		debug("Port: %d", pen_getport(a));
		debug("Address: %s", pen_ntoa(a));
		break;
	case AF_INET6:
		debug("Family: AF_INET6");
		debug("Port: %d", pen_getport(a));
		debug("Address: %s", pen_ntoa(a));
		break;
	case AF_UNIX:
		debug("Family: AF_UNIX");
		debug("Path: %s", pen_ntoa(a));
		break;
	default:
		debug("pen_dumpaddr: Unknown address family %d", a->ss_family);
	}
}

static int pen_ss_size(struct sockaddr_storage *ss)
{
	switch (ss->ss_family) {
	case AF_UNIX:
		return sizeof(struct sockaddr_un);
	case AF_INET:
		return sizeof(struct sockaddr_in);
	case AF_INET6:
		return sizeof(struct sockaddr_in6);
	default:
		debug("pen_ss_size: unknown address family %d", ss->ss_family);
		return sizeof(struct sockaddr_storage);
	}
}

/* Takes a name and fills in a struct sockaddr_storage. The port is left alone.
   The address can be a unix socket path, a host name, an ipv4 address or an ipv6 address.
   Returns 0 for failure and 1 for success.
*/
static int pen_aton(char *name, struct sockaddr_storage *addr)
{
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;
	struct sockaddr_un *su;
	struct addrinfo *ai;
	struct addrinfo hints;
	int n, result;

	if (debuglevel) {
		debug("pen_aton(%s, %p)", name, addr);
	}
	/* Deal with Unix domain sockets first */
	if (strchr(name, '/')) {
		addr->ss_family = AF_UNIX;
		su = (struct sockaddr_un *)addr;
		snprintf(su->sun_path, sizeof su->sun_path, "%s", name);
		return 1;
	}
	memset(&hints, 0, sizeof(hints));
	hints.ai_flags = AI_ADDRCONFIG;
	hints.ai_socktype = SOCK_STREAM;
	n = getaddrinfo(name, NULL, &hints, &ai);
	if (n != 0) {
		debug("getaddrinfo: %s", gai_strerror(n));
		return 0;
	}
	if (debuglevel) {
		debug("family = %d", ai->ai_family);
		debug("socktype = %d", ai->ai_socktype);
		debug("protocol = %d", ai->ai_protocol);
		debug("addrlen = %d", (int)ai->ai_addrlen);
		debug("sockaddr = %p", ai->ai_addr);
		debug("canonname = %s", ai->ai_canonname);
	}
	addr->ss_family = ai->ai_family;
	switch (ai->ai_family) {
	case AF_INET:
		si = (struct sockaddr_in *)addr;
		/* ai->ai_addr is a struct sockaddr * */
		/* (struct sockaddr_in *)ai->ai_addr is a struct sockaddr_in * */
		/* ((struct sockaddr_in *)ai->ai_addr)->sin_addr is a struct in_addr */
		si->sin_addr = ((struct sockaddr_in *)ai->ai_addr)->sin_addr;
		result = 1;
		break;
	case AF_INET6:
		si6 = (struct sockaddr_in6 *)addr;
		/* ai->ai_addr is a struct sockaddr * */
		/* (struct sockaddr_in6 *)ai->ai_addr is a struct sockaddr_in6 * */
		/* ((struct sockaddr_in6 *)ai->ai_addr)->sin6_addr is a struct in6_addr */
		si6->sin6_addr = ((struct sockaddr_in6 *)ai->ai_addr)->sin6_addr;
		result = 1;
		break;
	default:
		debug("Unknown family %d", ai->ai_family);
		result = 0;
		break;
	}
	freeaddrinfo(ai);
	return result;
}

#ifdef HAVE_SSL
static int ssl_verify_cb(int ok, X509_STORE_CTX *ctx)
{
	char buffer[256];

	X509_NAME_oneline(X509_get_issuer_name(ctx->current_cert),
			buffer, sizeof(buffer));
	if (ok) {
		debug("SSL: Certificate OK: %s", buffer);
	} else {
		switch (ctx->error) {
		case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT:
			debug("SSL: Cert error: CA not known: %s", buffer);
			break;
		case X509_V_ERR_CERT_NOT_YET_VALID:
			debug("SSL: Cert error: Cert not yet valid: %s",
				buffer);
			break;
		case X509_V_ERR_ERROR_IN_CERT_NOT_BEFORE_FIELD:
			debug("SSL: Cert error: illegal \'not before\' field: %s",
				buffer);
			break;
		case X509_V_ERR_CERT_HAS_EXPIRED:
			debug("SSL: Cert error: Cert expired: %s", buffer);
			break;
		case X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD:
			debug("SSL: Cert error: invalid \'not after\' field: %s",
				buffer);
			break;
		default:
			debug("SSL: Cert error: unknown error %d in %s",
				ctx->error, buffer);
			break;
		}
	}
	return ok;
}

static RSA *ssl_temp_rsa_cb(SSL *ssl, int export, int keylength)
{
	static RSA *rsa = NULL;

	if (rsa == NULL)
		rsa = RSA_generate_key(512, RSA_F4, NULL, NULL);
	return rsa;
}

static int ssl_init(void)
{
	int err;

	SSL_load_error_strings();
	SSLeay_add_ssl_algorithms();
	switch (ssl_protocol) {
#if 0
	case SRV_SSL_V2:
		ssl_context = SSL_CTX_new(SSLv2_method());
		break;
#endif
	case SRV_SSL_V3:
		ssl_context = SSL_CTX_new(SSLv3_method());
		break;
	default:
	case SRV_SSL_V23:
		ssl_context = SSL_CTX_new(SSLv23_method());
		break;
	case SRV_SSL_TLS1:
		ssl_context = SSL_CTX_new(TLSv1_method());
		break;
	}
	if (ssl_context == NULL) {
		err = ERR_get_error();
		error("SSL: Error allocating context: %s",
			ERR_error_string(err, NULL));
	}
	if (ssl_compat) {
		SSL_CTX_set_options(ssl_context, SSL_OP_ALL);
	}
	if (certfile == NULL || *certfile == 0) {
		debug("SSL: No cert file specified in config file!");
		error("The server MUST have a certificate!");
	}
	if (keyfile == NULL || *keyfile == 0)
		keyfile = certfile;
	if (certfile != NULL && *certfile != 0) {
		if (!SSL_CTX_use_certificate_file(ssl_context, certfile,
						SSL_FILETYPE_PEM)) {
			err = ERR_get_error();
			error("SSL: error reading certificate from file %s: %s",
				certfile, ERR_error_string(err, NULL));
		}
		if (!SSL_CTX_use_PrivateKey_file(ssl_context, keyfile,
						SSL_FILETYPE_PEM)) {
			err = ERR_get_error();
			error("SSL: error reading private key from file %s: %s",
				keyfile, ERR_error_string(err, NULL));
		}
		if (!SSL_CTX_check_private_key(ssl_context)) {
			error("SSL: Private key does not match public key in cert!");
		}
	}
	if (cacert_dir != NULL && *cacert_dir == 0)
		cacert_dir = NULL;
	if (cacert_file != NULL && *cacert_file == 0)
		cacert_file = NULL;
	if (cacert_dir != NULL || cacert_file != NULL) {
		if (!SSL_CTX_load_verify_locations(ssl_context,
					cacert_file, cacert_dir)) {
			err = ERR_get_error();
			debug("SSL: Error error setting CA cert locations: %s",
				ERR_error_string(err, NULL));
			cacert_file = cacert_dir = NULL;
		}
	}
	if (cacert_dir == NULL && cacert_file == NULL) {  /* no verify locations loaded */
		debug("SSL: No verify locations, trying default");
		if (!SSL_CTX_set_default_verify_paths(ssl_context)) {
			err = ERR_get_error();
			debug("SSL: Error error setting default CA cert location: %s",
				ERR_error_string(err, NULL));
			debug("continuing anyway...");
		}
	}
	SSL_CTX_set_tmp_rsa_callback(ssl_context, ssl_temp_rsa_cb);
	if (require_peer_cert) {
		SSL_CTX_set_verify(ssl_context,
			SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT,
			ssl_verify_cb);
	} else {
		SSL_CTX_set_verify(ssl_context,
			SSL_VERIFY_NONE,
			ssl_verify_cb);
	}

	SSL_CTX_set_client_CA_list(ssl_context,
			SSL_load_client_CA_file(certfile));

	/* permit large writes to be split up in several records */
	SSL_CTX_set_mode(ssl_context, SSL_MODE_ENABLE_PARTIAL_WRITE);

#if 1	/* testing */
	debug("SSL_CTX_get_session_cache_mode() returns %d",
		SSL_CTX_get_session_cache_mode(ssl_context));
	SSL_CTX_set_session_cache_mode(ssl_context, 0);
#endif

	return 0;
}

#endif  /* HAVE_SSL */

/* allocate ace and fill in the generics */
static int add_acl(int a, unsigned char permit)
{
	int i;
	if (a < 0 || a >= ACLS_MAX) {
		debug("add_acl: %d outside (0,%d)", a, ACLS_MAX);
		return -1;
	}
	i = nacls[a]++;
	acls[a] = pen_realloc(acls[a], nacls[a]*sizeof(acl));
	acls[a][i].permit = permit;
	return i;
}

static void add_acl_ipv4(int a, unsigned int ip, unsigned int mask, unsigned char permit)
{
	int i = add_acl(a, permit);

	if (i == -1) return;

	if (debuglevel) {
		debug("add_acl_ipv4(%d, %x, %x, %d)", a, ip, mask, permit);
	}
	acls[a][i].class = ACE_IPV4;
	acls[a][i].ace.ipv4.ip = ip;
	acls[a][i].ace.ipv4.mask = mask;
}

static void add_acl_ipv6(int a, unsigned char *ipaddr, unsigned char len, unsigned char permit)
{
	int i = add_acl(a, permit);

	if (i == -1) return;

	if (debuglevel) {
		debug("add_acl_ipv6(%d, %x, %d, %d)", a, ipaddr, len, permit);
		debug("%x:%x:%x:%x:%x:%x:%x:%x/%d",
			256*ipaddr[0]+ipaddr[1], 256*ipaddr[2]+ipaddr[3], 256*ipaddr[4]+ipaddr[5], 256*ipaddr[6]+ipaddr[7],
			256*ipaddr[8]+ipaddr[9], 256*ipaddr[10]+ipaddr[11], 256*ipaddr[12]+ipaddr[13], 256*ipaddr[14]+ipaddr[15],  len);
	}
	acls[a][i].class = ACE_IPV6;
	memcpy(acls[a][i].ace.ipv6.ip.s6_addr, ipaddr, 16);
	acls[a][i].ace.ipv6.len = len;
}

static void add_acl_geo(int a, char *country, unsigned char permit)
{
	int i = add_acl(a, permit);

	if (i == -1) return;

	if (debuglevel) {
		debug("add_acl_geo(%d, %s, %d", a, country, permit);
	}
	acls[a][i].class = ACE_GEO;
	strncpy(acls[a][i].ace.geo.country, country, 2);
}

static void del_acl(int a)
{
	if (debuglevel) {
		debug("del_acl(%d)", a);
	}
	if (a < 0 || a >= ACLS_MAX) {
		debug("del_acl: %d outside (0,%d)", a, ACLS_MAX);
		return;
	}
	free(acls[a]);
	acls[a] = NULL;
	nacls[a] = 0;
}

static int match_acl_unix(int a, struct sockaddr_un *cli_addr)
{
	(void)a;
	(void)cli_addr;

	if (debuglevel) debug("Unix acl:s not implemented");
	return 1;
}

static int match_acl_ipv4(int a, struct sockaddr_in *cli_addr)
{
	unsigned int client = cli_addr->sin_addr.s_addr;
	int i;
	int permit = 0;
	acl *ap = acls[a];
#ifdef HAVE_GEOIP
	const char *country = NULL;
	int geo_done = 0;
#endif
	if (debuglevel) {
		debug("match_acl_ipv4(%d, %u)", a, client);
	}
	for (i = 0; i < nacls[a]; i++) {
		permit = ap[i].permit;
		switch (ap[i].class) {
		case ACE_IPV4:
			if ((client & ap[i].ace.ipv4.mask) == ap[i].ace.ipv4.ip) {
				return permit;
			}
			break;
		case ACE_GEO:
#ifdef HAVE_GEOIP
			if (geoip4 == NULL) break;
			if (!geo_done) {
				country = GeoIP_country_code_by_addr(geoip4,
						pen_ntoa((struct sockaddr_storage *)cli_addr));
				if (debuglevel) {
					if (country) debug("Country = %s", country);
					else debug("Country unknown");
				}
				geo_done = 1;
			}
			if (country && !strncmp(country,
						ap[i].ace.geo.country, 2)) {
				return permit;
			}
#else
			debug("ACE_GEO: Not implemented");
#endif
			break;
		default:
			/* ignore other ACE classes (ipv6 et al) */
			break;
		}
	}
	return !permit;
}

/* The most straightforward way to get at the bytes of an ipv6 address
   is to take the pointer to the in6_addr and cast it to a pointer to
   unsigned char.
*/
static int match_acl_ipv6(int a, struct sockaddr_in6 *cli_addr)
{
	unsigned char *client = (unsigned char *)&(cli_addr->sin6_addr);
	unsigned char *ip;
	unsigned char *mask;
	int len;
	int i, j;
	int permit = 0;
	acl *ap = acls[a];
#ifdef HAVE_GEOIP
	const char *country = NULL;
	int geo_done = 0;
#endif

	if (debuglevel) {
		debug("match_acl_ipv6(%d, %u)", a, client);
	}
	for (i = 0; i < nacls[a]; i++) {
		permit = ap[i].permit;
		switch (ap[i].class) {
		case ACE_IPV6:
			len = ap[i].ace.ipv6.len;
			ip = (unsigned char *)&(ap[i].ace.ipv6.ip);
			mask = mask_ipv6[len];
			if (debuglevel > 1) {
				debug("Matching %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x against %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x / %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x",
					client[0], client[1], client[2], client[3], client[4], client[5], client[6], client[7], client[8], client[9], client[10], client[11], client[12], client[13], client[14], client[15],
					ip[0], ip[1], ip[2], ip[3], ip[4], ip[5], ip[6], ip[7], ip[8], ip[9], ip[10], ip[11], ip[12], ip[13], ip[14], ip[15],
					mask[0], mask[1], mask[2], mask[3], mask[4], mask[5], mask[6], mask[7], mask[8], mask[9], mask[10], mask[11], mask[12], mask[13], mask[14], mask[15]);
			}
			for (j = 0; j < 16; j++) {
				if ((client[j] & mask[j]) != ip[j]) break;
			}
			if (j == 16) return permit;
			break;
		case ACE_GEO:
#ifdef HAVE_GEOIP
			if (geoip6 == NULL) break;
			if (!geo_done) {
				country = GeoIP_country_code_by_addr_v6(geoip6,
						pen_ntoa((struct sockaddr_storage *)cli_addr));
				if (debuglevel) {
					if (country) debug("Country = %s", country);
					else debug("Country unknown");
				}
				geo_done = 1;
			}
			if (country && !strncmp(country,
						ap[i].ace.geo.country, 2)) {
				return permit;
			}
#else
			debug("ACE_GEO: Not implemented");
#endif
			break;
		default:
			/* ignore other ACE classes (ipv4 et al) */
			break;
		}
	}
	return !permit;
}

static int match_acl(int a, struct sockaddr_storage *cli_addr)
{
	switch (cli_addr->ss_family) {
	case AF_UNIX:
		return match_acl_unix(a, (struct sockaddr_un *)cli_addr);
	case AF_INET:
		return match_acl_ipv4(a, (struct sockaddr_in *)cli_addr);
	case AF_INET6:
		return match_acl_ipv6(a, (struct sockaddr_in6 *)cli_addr);
	default:
		debug("match_acl: unknown address family %d", cli_addr->ss_family);
	}
	return 0;
}

static int webstats(void)
{
	FILE *fp;
	int i;
	time_t now;
	struct tm *nowtm;
	char nowstr[80];

	if (webfile == NULL) {
		debug("Don't know where to write web stats; see -w option");
		return 0;
	}
	fp = fopen(webfile, "w");
	if (fp == NULL) {
		debug("Can't write to %s", webfile);
		return 0;
	}
	now=time(NULL);
	nowtm = localtime(&now);
	strftime(nowstr, sizeof(nowstr), "%Y-%m-%d %H:%M:%S", nowtm);
	fprintf(fp,
		"<html>\n"
		"<head>\n"
		"<title>Pen status page</title>\n"
		"</head>\n"
		"<body bgcolor=\"#ffffff\">"
		"<h1>Pen status page</h1>\n");
	fprintf(fp,
		"Time %s, %d servers, %d current<p>\n",
		nowstr, nservers, current);
	fprintf(fp,
		"<table bgcolor=\"#c0c0c0\">\n"
		"<tr>\n"
		"<td bgcolor=\"#80f080\">server</td>\n"
		"<td bgcolor=\"#80f080\">address</td>\n"
		"<td bgcolor=\"#80f080\">status</td>\n"
		"<td bgcolor=\"#80f080\">port</td>\n"
		"<td bgcolor=\"#80f080\">connections</td>\n"
		"<td bgcolor=\"#80f080\">max soft</td>\n"
		"<td bgcolor=\"#80f080\">max hard</td>\n"
		"<td bgcolor=\"#80f080\">sent</td>\n"
		"<td bgcolor=\"#80f080\">received</td>\n"
		"<td bgcolor=\"#80f080\">weight</td>\n"
		"<td bgcolor=\"#80f080\">prio</td>\n"
		"</tr>\n");
	for (i = 0; i < nservers; i++) {
		fprintf(fp,
			"<tr>\n"
			"<td>%d</td>\n"
			"<td>%s</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%llu</td>\n"
			"<td>%llu</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"</tr>\n",
			i, pen_ntoa(&servers[i].addr),
			servers[i].status, pen_getport(&servers[i].addr),
			servers[i].c, servers[i].maxc, servers[i].hard,
			servers[i].sx, servers[i].rx,
			servers[i].weight, servers[i].prio);
	}
	fprintf(fp, "</table>\n");

	fprintf(fp, "<h2>Active clients</h2>");
	fprintf(fp, "Max number of clients: %d<p>", clients_max);
	fprintf(fp,
		"<table bgcolor=\"#c0c0c0\">\n"
		"<tr>\n"
		"<td bgcolor=\"#80f080\">client</td>\n"
		"<td bgcolor=\"#80f080\">address</td>\n"
		"<td bgcolor=\"#80f080\">age(secs)</td>\n"
		"<td bgcolor=\"#80f080\">last server</td>\n"
		"<td bgcolor=\"#80f080\">connects</td>\n"
		"<td bgcolor=\"#80f080\">sent</td>\n"
		"<td bgcolor=\"#80f080\">received</td>\n"
		"</tr>\n");
	for (i = 0; i < clients_max; i++) {
		if (clients[i].last == 0) continue;
		fprintf(fp,
			"<tr>\n"
			"<td>%d</td>\n"
			"<td>%s</td>\n"
			"<td>%ld</td>\n"
			"<td>%d</td>\n"
			"<td>%ld</td>\n"
			"<td>%lld</td>\n"
			"<td>%lld</td>\n"
			"</tr>\n",
			i, pen_ntoa(&clients[i].addr),
			(long)(now-clients[i].last), clients[i].cno, clients[i].connects,
			clients[i].csx, clients[i].crx);
	}
	fprintf(fp, "</table>\n");

	fprintf(fp, "<h2>Active connections</h2>");
	fprintf(fp, "Number of connections: %d max, %d used, %d last<p>",
		connections_max, connections_used, connections_last);
	fprintf(fp,
		"<table bgcolor=\"#c0c0c0\">\n"
		"<tr>\n"
		"<td bgcolor=\"#80f080\">connection</td>\n"
		"<td bgcolor=\"#80f080\">downfd</td>\n"
		"<td bgcolor=\"#80f080\">upfd</td>\n"
		"<td bgcolor=\"#80f080\">pending data down</td>\n"
		"<td bgcolor=\"#80f080\">pending data up</td>\n"
		"<td bgcolor=\"#80f080\">client</td>\n"
		"<td bgcolor=\"#80f080\">server</td>\n"
		"</tr>\n");
	for (i = 0; i < connections_max; i++) {
		if (conns[i].downfd == -1) continue;
		fprintf(fp,
			"<tr>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"<td>%d</td>\n"
			"</tr>\n",
			i, conns[i].downfd, conns[i].upfd,
			conns[i].downn, conns[i].upn,
			conns[i].clt, conns[i].index);
	}
	fprintf(fp, "</table>\n");
	fprintf(fp,
		"</body>\n"
		"</html>\n");
	fclose(fp);
	return 1;
}

static void textstats(void)
{
	int i;
	time_t now;
	struct tm *nowtm;
	char nowstr[80];

	now=time(NULL);
	nowtm = localtime(&now);
	strftime(nowstr, sizeof(nowstr), "%Y-%m-%d %H:%M:%S", nowtm);

	debug("Time %s, %d servers, %d current",
		nowstr, nservers, current);
	for (i = 0; i < nservers; i++) {
		debug("Server %d status:\n"
			"address %s\n"
			"%d\n"
			"port %d\n"
			"%d connections (%d soft, %d hard)\n"
			"%llu sent, %llu received\n",
			i, pen_ntoa(&servers[i].addr),
			servers[i].status, pen_getport(&servers[i].addr),
			servers[i].c, servers[i].maxc, servers[i].hard,
			servers[i].sx, servers[i].rx);
	}
	debug("Max number of clients: %d", clients_max);
	debug("Active clients:");
	for (i = 0; i < clients_max; i++) {
		if (clients[i].last == 0) continue;
		debug("Client %d status:\n"
			"address %s\n"
			"last used %ld\n"
			"last server %d\n",
			"connects  %ld\n",
			"sent  %llu\n",
			"received  %llu\n",
			i, pen_ntoa(&clients[i].addr),
			(long)(now-clients[i].last), clients[i].cno, clients[i].connects,
			clients[i].csx, clients[i].crx);
	}
	debug("Max number of connections: %d", connections_max);
	debug("Active connections:");
	for (i = 0; i < connections_max; i++) {
		if (conns[i].downfd == -1) continue;
		debug("Connection %d status:\n"
			"downfd = %d, upfd = %d\n"
			"pending data %d down, %d up\n"
			"client %d, server %d\n",
			i, conns[i].downfd, conns[i].upfd,
			conns[i].downn, conns[i].upn,
			conns[i].clt, conns[i].index);
	}
}


static void stats(int dummy)
{
	(void)dummy;

	if (debuglevel) debug("Caught USR1, will save stats");
	do_stats=1;
	sigaction(SIGUSR1, &usr1action, NULL);
}

static void restart_log(int dummy)
{
	(void)dummy;

	if (debuglevel) debug("Caught HUP, will read cfg");
	do_restart_log=1;
	sigaction(SIGHUP, &hupaction, NULL);
}

static void quit(int dummy)
{
	(void)dummy;

	if (debuglevel) {
		debug("Quitting");
		debug("Read configuration %d times", hupcounter);
	}
	loopflag = 0;
}

/* Return index of known client, otherwise -1 */
static int lookup_client(struct sockaddr_storage *cli)
{
	int i;
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;
	int family = cli->ss_family;
	unsigned long ad;
	void *ad6;
	time_t now = time(NULL);

	if (family == AF_INET) {
		si = (struct sockaddr_in *)cli;
		ad = si->sin_addr.s_addr;
	} else if (family == AF_INET6) {
		si6 = (struct sockaddr_in6 *)cli;
		ad6 = &si6->sin6_addr;
	}
	for (i = 0; i < clients_max; i++) {
		if (family != clients[i].addr.ss_family) continue;
		if (family == AF_UNIX) break;	/* no good way to distinguish clients */
		if (family == AF_INET) {
			si = (struct sockaddr_in *)&clients[i].addr;
			if (ad == si->sin_addr.s_addr) break;
		}
		if (family == AF_INET6) {
			si6 = (struct sockaddr_in6 *)&clients[i].addr;
			if (!memcmp(ad6, &si6->sin6_addr, sizeof *ad6)) break;
		}
	}
	if (i == clients_max) i = -1;
	else if (tracking_time > 0 && clients[i].last+tracking_time < now) {
		/* too old, recycle */
		clients[i].last = 0;
		i = -1;
	}
	if (debuglevel) debug("Client %s has index %d", pen_ntoa(cli), i);
	return i;
}

/* Store client and return index */
static int store_client(int clino, struct sockaddr_storage *cli, int ch)
{
	int i;
	int empty = -1;		/* first empty slot */
	int oldest = -1;	/* in case we need to recycle */
	struct sockaddr_in *si;
	struct sockaddr_in6 *si6;
	int family = cli->ss_family;
	unsigned long ad;
	void *ad6;

	if (family == AF_INET) {
		si = (struct sockaddr_in *)cli;
		ad = si->sin_addr.s_addr;
	} else if (family == AF_INET6) {
		si6 = (struct sockaddr_in6 *)cli;
		ad6 = &si6->sin6_addr;
	}
	if (clino == -1) {
		for (i = 0; i < clients_max; i++) {
			/* require same family and address */
			if (family == clients[i].addr.ss_family) {
				if (family == AF_UNIX) break;
				if (family == AF_INET) {
					si = (struct sockaddr_in *)&clients[i].addr;
					if (ad == si->sin_addr.s_addr) break;
				}
				if (family == AF_INET6) {
					si6 = (struct sockaddr_in6 *)&clients[i].addr;
					if (!memcmp(ad6, &si6->sin6_addr, sizeof *ad6)) break;
				}
			}

			if (empty != -1) continue;
			if (clients[i].last == 0) {
				empty = i;
				continue;
			}
			if (oldest == -1 || (clients[i].last < clients[oldest].last)) {
				oldest = i;
			}
		}

		if (i == clients_max) {
			if (empty != -1) i = empty;
			else i = oldest;
		}
		clients[i].connects = 0;
		clients[i].csx = 0;
		clients[i].crx = 0;
	} else {
		i = clino;
	}

	clients[i].last = time(NULL);
	clients[i].addr = *cli;
	clients[i].cno = ch;
	clients[i].connects++;

	if (debuglevel) {
		debug("Client %s has index %d and server %d",
			pen_ntoa(cli), i, ch);
	}
	servers[ch].c++;

	return i;
}

static void dump(unsigned char *p, int n)
{
	int i;

	fprintf(stderr, "%d: ", n);
	for (i = 0; i < n; i++) {
		if (asciidump) {
			fprintf(stderr, "%c",
				(isprint(p[i])||isspace(p[i]))?p[i]:'.');
		} else {
			fprintf(stderr, "%02x ", (int)p[i]);
		}
	}
	fprintf(stderr, "\n");
}

/* return port number in host byte order */
static int getport(char *p, char *proto)
{
	struct servent *s = getservbyname(p, proto);
	if (s == NULL) {
		return atoi(p);
	} else {
		return ntohs(s->s_port);
	}
}

/* Introduce the new format "[address]:port:maxc:hard:weight:prio"
   in addition to the old one.
*/
static void setaddress(int server, char *s, int dp, char *proto)
{
	char address[1024], pno[100];
	int n;
	char *format;
	int port;

	if (s[0] == '[') {
		format = "[%999[^]]]:%99[^:]:%d:%d:%d:%d";
	} else {
		format = "%999[^:]:%99[^:]:%d:%d:%d:%d";
	}
	n = sscanf(s, format, address, pno,
		&servers[server].maxc, &servers[server].hard,
		&servers[server].weight, &servers[server].prio);

	if (n > 1) port = getport(pno, proto);
	else port = dp;
	if (n < 3) servers[server].maxc = 0;
	if (n < 4) servers[server].hard = 0;
	if (n < 5) servers[server].weight = 0;
	if (n < 6) servers[server].prio = 0;

	if (debuglevel)
		debug("n = %d, address = %s, pno = %d, maxc1 = %d, hard = %d, weight = %d, prio = %d, proto = %s ",
			n, address, port, servers[server].maxc,
			servers[server].hard, servers[server].weight,
			servers[server].prio, proto);

	if (pen_aton(address, &servers[server].addr) == 0) {
		error("unknown or invalid address [%s]", address);
	}
	pen_setport(&servers[server].addr, port);
}

/* Log format is:

   + client_ip server_ip request
*/
static void netlog(int fd, int i, unsigned char *r, int n)
{
	int j, k;
	char b[1024];
	if (debuglevel) debug("netlog(%d, %d, %p, %d)", fd, i, r, n);
	strcpy(b, "+ ");
	k = 2;
	strcpy(b+k, pen_ntoa(&clients[conns[i].clt].addr));
	k += strlen(b+k);
	b[k++] = ' ';
	strcpy(b+k, pen_ntoa(&servers[conns[i].index].addr));
	k += strlen(b+k);
	b[k++] = ' ';

	/* We have already used k bytes from b. This means that we want
	   no more than (sizeof b-(k+1)) bytes from r. The +1 is for the
	   trailing newline.
	*/
	j = sizeof b-(k+1);
	if (n > j) n = j;
	for (j = 0; j < n && r[j] != '\r' && r[j] != '\n'; j++) {
		b[k++] = r[j];
	}
	b[k++] = '\n';
	sendto(fd, b, k, 0, (struct sockaddr *)&logserver, sizeof logserver);
}

/* Log format is:

    client_ip timestamp server_ip request
*/
static void log_request(FILE *fp, int i, unsigned char *b, int n)
{
	int j;
	if (n > KEEP_MAX) n = KEEP_MAX;
	fprintf(fp, "%s ", pen_ntoa(&clients[conns[i].clt].addr));
	fprintf(fp, "%ld ", (long)time(NULL));
	fprintf(fp, "%s ", pen_ntoa(&servers[conns[i].index].addr));
	for (j = 0; j < n && b[j] != '\r' && b[j] != '\n'; j++) {
		fprintf(fp, "%c", isascii(b[j])?b[j]:'.');
	}
	fprintf(fp, "\n");
}

static int rewrite_request(int i, int n, char *b)
{
	char *q;
	char p[BUFFER_MAX];
	int pl;

	b[n] = '\0';

	if (debuglevel > 1) debug("rewrite_request(%d, %d, %s)", i, n, b);

	if (pen_strncasecmp(b, "GET ", 4) &&
	    pen_strncasecmp(b, "POST ", 5) &&
	    pen_strncasecmp(b, "HEAD ", 5)) {
		return n;	/* You can't touch this */
	}
	if (debuglevel) debug("Looking for CRLFCRLF");
	q = strstr(b, "\r\n\r\n");
	/* Steve Hall <steveh@intrapower.com.au> tells me that
	   apparently some clients send \n\n instead */
	if (!q) {
		if (debuglevel) debug("Looking for LFLF");
		q = strstr(b, "\n\n");
	}
	if (!q) return n;		/* not a header */
#if 0	/* how is that supposed to happen? */
	if (q >= b+n) return n;		/* outside of buffer */
#endif
	/* Look for existing X-Forwarded-For */
	if (debuglevel) debug("Looking for X-Forwarded-For");

	if (pen_strcasestr(b, "\nX-Forwarded-For:")) return n;

	if (debuglevel) debug("Adding X-Forwarded-For");
	/* Didn't find one, add our own */
	sprintf(p, "\r\nX-Forwarded-For: %s",
		pen_ntoa(&clients[conns[i].clt].addr));
	pl=strlen(p);
	if (n+pl > BUFFER_MAX) return n;

	memmove(q+pl, q, b+n-q);
	memmove(q, p, pl);

	n += pl;
	return n;
}

static int copy_up(int i)
{
	int rc;
	int from = conns[i].downfd;
	int to = conns[i].upfd;
	int serverindex = conns[i].index;

	unsigned char b[BUFFER_MAX];

#ifdef HAVE_SSL
	SSL *ssl = conns[i].ssl;

	if (ssl) {
		rc = SSL_read(ssl, b, BUFFER_MAX);
		if (debuglevel) debug("SSL_read returns %d\n", rc);
		if (rc < 0) {
			int err = SSL_get_error(ssl, rc);
			if (debuglevel) debug("SSL_read returns %d (SSL error %d)\n", rc, err);
			if (err == SSL_ERROR_WANT_READ ||
			    err == SSL_ERROR_WANT_WRITE) {
				return 0;
			}
		}
	} else {
		rc = read(from, b, BUFFER_MAX);
	}
#else

	rc = read(from, b, BUFFER_MAX);

#endif  /* HAVE_SSL */

	if (debuglevel > 1) debug("copy_up(%d) %d bytes", i, rc);

	if (rc <= 0) {
		return -1;
	} else {
		int n;

		if (http) {
			rc = rewrite_request(i, rc, (char *)b);
		}

		if (debuglevel > 2) dump(b, rc);

		if (logfp) {
			log_request(logfp, i, b, rc);
			if (debuglevel > 2) log_request(stderr, i, b, rc);
		}
		if (logsock != -1) {
			netlog(logsock, i, b, rc);
		}

		if (delayed_forward) n = 0;
		else {
			n = write(to, b, rc);	/* no ssl here */
		}

		if (n < 0) {
			if (!nblock || errno != EAGAIN) return -1;
			n = 0;
		}
		if (n != rc) {
			if (debuglevel > 1) {
				debug("copy_up saving %d bytes in up buffer",
					rc-n);
			}
			conns[i].upn = rc-n;	/* remaining to be copied */
			conns[i].upbptr = conns[i].upb = pen_malloc(rc-n);
			memcpy(conns[i].upb, b+n, rc-n);
		}
		servers[serverindex].sx += rc;	/* That's not right? Should be n */
		clients[conns[i].clt].crx += rc;
		conns[i].crx += rc;	/* rewritten bytes read from client */
		conns[i].ssx += n;	/* actual bytes written to server */
	}
	return 0;
}

/* this function may have to deal with udp */
static int copy_down(int i)
{
	int rc;
	int from = conns[i].upfd;
	int to = conns[i].downfd;
	int serverindex = conns[i].index;
#ifdef HAVE_SSL
	SSL *ssl = conns[i].ssl;
#endif

	unsigned char b[BUFFER_MAX];

	/* we called connect from add_client, so this works for udp and tcp */
	rc = read(from, b, BUFFER_MAX);	/* no ssl here */

	if (debuglevel > 1) debug("copy_down(%d) %d bytes", i, rc);
	if (debuglevel > 2) dump(b, rc);


	if (rc <= 0) {
		return -1;
	} else {
		int n;

		if (udp) {
			struct sockaddr_storage *ss = &clients[conns[i].clt].addr;
			socklen_t sss = pen_ss_size(ss);
			if (debuglevel) debug("copy_down sending %d bytes to socket %d", rc, to);
			n = sendto(to, b, rc, 0, (struct sockaddr *)ss, sss);
			close_conn(i);
			return 0;
		}

		if (delayed_forward) {
			n = 0;
		} else {
#ifdef HAVE_SSL
			if (ssl) {
				/* can't write more than 32000 bytes at a time */
				int ssl_rc;
				if (rc > 32000) ssl_rc = 32000;
				else ssl_rc = rc;
				n = SSL_write(ssl, b, ssl_rc);
				if (debuglevel) debug("SSL_write returns %d\n", n);
				if (n < 0) {
					int err = SSL_get_error(ssl, n);
					if (debuglevel) debug("SSL error %d\n", err);
					if (err == SSL_ERROR_WANT_READ ||
					    err == SSL_ERROR_WANT_WRITE) {
						return 0;
					}
				}
			} else {
				n = write(to, b, rc);
			}
#else

			n = write(to, b, rc);
#endif
		}

		if (n < 0) {
			if (!nblock || errno != EAGAIN) return -1;
			n = 0;
		}
		if (n != rc) {
			if (debuglevel > 1) {
				debug("copy_down saving %d bytes in down buffer",
					rc-n);
			}
			conns[i].downn = rc-n;
			conns[i].downbptr = conns[i].downb = pen_malloc(rc-n);
			memcpy(conns[i].downb, b+n, rc-n);
		}
		servers[serverindex].rx += rc;
		clients[conns[i].clt].csx += n;
		conns[i].srx += rc;
		conns[i].csx += n;
	}
	return 0;
}

static void alarm_handler(int dummy)
{
	if (debuglevel) debug("alarm_handler(%d)", dummy);
}

#ifdef HAVE_SSL
static void store_conn(int downfd, SSL *ssl, int upfd, int clt, int index)
#else
static void store_conn(int downfd, int upfd, int clt, int index)
#endif
{
	int i, fl;

	if (nblock) {
		if ((fl = fcntl(downfd, F_GETFL, 0)) == -1)
			error("Can't fcntl, errno = %d", errno);
		if (fcntl(downfd, F_SETFL, fl | O_NONBLOCK) == -1)
			error("Can't fcntl, errno = %d", errno);
		if ((fl = fcntl(upfd, F_GETFL, 0)) == -1)
			error("Can't fcntl, errno = %d", errno);
		if (fcntl(upfd, F_SETFL, fl | O_NONBLOCK) == -1)
			error("Can't fcntl, errno = %d", errno);
	}
	i = connections_last;
	do {
		if (conns[i].upfd == -1) break;
		i++;
		if (i >= connections_max) i = 0;
	} while (i != connections_last);
	/* The next test is not necessary, because we don't call
	   store_conn unless there are empty connection slots.
	   Keep the test anyway for now. */
	if (conns[i].upfd == -1) {
		connections_last = i;
		connections_used++;
		conns[i].upfd = upfd;
		conns[i].downfd = downfd;
#ifdef HAVE_SSL
		conns[i].ssl = ssl;
#endif
		conns[i].clt = clt;
		conns[i].index = index;

#ifdef HAVE_KQUEUE
		/* kqueue can store a pointer to arbitrary data with each
		 * event, but it must be a pointer. We store a pointer to
		 * conns[i]. copy_up/down then require i again, which we
		 * can't get without storing i within the struct itself. */
		conns[i].i = i;
#endif
		current = index;
		conns[i].srx = conns[i].ssx = 0;
		conns[i].crx = conns[i].csx = 0;
	} else {
		if (debuglevel)
			debug("Connection table full (%d slots), can't store connection.\n"
			      "Try restarting with -x %d",
			      connections_max, 2*connections_max);
		close(downfd);
		close(upfd);
	}
	if (debuglevel) debug("store_conn: conn = %d, upfd = %d, downfd = %d, connections_used = %d",
				i, upfd, downfd, connections_used);
}

static void close_conn(int i)
{
	int index = conns[i].index;
	servers[index].c -= 1;
	if (servers[index].c < 0) servers[index].c = 0;

	if (conns[i].upfd > listenfd) {
		close(conns[i].upfd);
	}
	if (conns[i].downfd > listenfd) {
		close(conns[i].downfd);
	}
	conns[i].upfd = conns[i].downfd = -1;
	if (conns[i].downn) {
		free(conns[i].downb);
		conns[i].downn=0;
	}
	if (conns[i].upn) {
		free(conns[i].upb);
		conns[i].upn=0;
	}
#ifdef HAVE_SSL
	if (conns[i].ssl) {
		SSL_free(conns[i].ssl);
		conns[i].ssl = 0;
	}
#endif
	connections_used--;
	if (connections_used < 0) connections_used = 0;
	if (debuglevel) {
		debug("close_conn: Closing connection %d to server %d; connections_used = %d",
				i, index, connections_used);
		debug("\tRead %ld from client, wrote %ld to server",
				conns[i].crx, conns[i].ssx);
		debug("\tRead %ld from server, wrote %ld to client",
				conns[i].srx, conns[i].csx);
	}
}


static void usage(void)
{
	printf("usage:\n"
	       "  pen [-C addr:port] [-X] [-b sec] [-S N] [-c N] [-e host[:port]]\n"
	       "      [-t sec] [-x N] [-w dir] [-HPWadfhrs]\n"
	       "      [-o option]\n"
	       "      [-E certfile] [-K keyfile]\n"
	       "      [-G cacertfile] [-A cacertdir]\n"
	       "      [-Z] [-R] [-L protocol]\n"
	       "      [host:]port h1[:p1[:maxc1[:hard1[:weight1[:prio1]]]]] [h2[:p2[:maxc2[:hard2[:weight2[:prio2]]]]]] ...\n"
	       "\n"
	       "  -B host:port abuse server for naughty clients\n"
	       "  -C port   control port\n"
	       "  -T sec    tracking time in seconds (0 = forever) [%d]\n"
	       "  -H	add X-Forwarded-For header in http requests\n"
	       "  -U	use udp protocol support\n"
	       "  -P	use poll() rather than select()\n"
	       "  -W    use weight for server selection\n"
	       "  -X	enable 'exit' command for control port\n"
	       "  -a	debugging dumps in ascii format\n"
	       "  -b sec    blacklist time in seconds [%d]\n"
	       "  -S N      max number of servers [%d]\n"
	       "  -c N      max number of clients [%d]\n"
	       "  -d	debugging on (repeat -d for more)\n"
	       "  -e host:port emergency server of last resort\n"
	       "  -f	stay in foregound\n"
	       "  -h	use hash for initial server selection\n"
	       "  -j dir    run in chroot\n"
	       "  -F file   name of configuration file\n"
	       "  -l file   logging on\n"
	       "  -n	do not make sockets nonblocking\n"
	       "  -r	bypass client tracking in server selection\n"
	       "  -s	stubborn selection, i.e. don't fail over\n"
	       "  -t sec    connect timeout in seconds [%d]\n"
	       "  -u user   run as alternative user\n"
	       "  -p file   write pid to file\n"
	       "  -x N      max number of simultaneous connections [%d]\n"
	       "  -w file   save statistics in HTML format in a file\n"
	       "  -o option use option in penctl format\n"
	       "  -E certfile   use the given certificate in PEM format\n"
	       "  -K keyfile    use the given key in PEM format (may be contained in cert)\n"
	       "  -G cacertfile file containing the CA's certificate\n"
	       "  -A cacertdir  directory containing CA certificates in hashed format\n"
	       "  -Z	    use SSL compatibility mode\n"
	       "  -R	    require valid peer certificate\n"
	       "  -L protocol   ssl23 (default), ssl2, ssl3 or tls1\n"
	       "\n"
	       "example:\n"
	       "  pen smtp mailhost1:smtp mailhost2:25 mailhost3\n"
	       "\n",
	       TRACKING_TIME, BLACKLIST_TIME, SERVERS_MAX, CLIENTS_MAX, TIMEOUT, CONNECTIONS_MAX);

	exit(0);
}

static void background(void)
{
#ifdef HAVE_DAEMON
	daemon(0, 0);
#else
	int childpid;
	if ((childpid = fork()) < 0) {
		error("Can't fork");
	} else {
		if (childpid > 0) {
			exit(0);	/* parent */
		}
	}
	int devnull_fd = open("/dev/null", O_RDWR);
	dup2(devnull_fd,0); /* stdin */
	dup2(devnull_fd,1); /* stdout */
	dup2(devnull_fd,2); /* stderr */
	setsid();
	signal(SIGCHLD, SIG_IGN);
#endif
}

static void init(int argc, char **argv)
{
	int i;
	int server;

	conns = pen_calloc(connections_max, sizeof *conns);
	clients = pen_calloc(clients_max, sizeof *clients);
	/* one extra server slot for the emergency server */
	/* and one for the abuse server */
	/* Check that servers_max is big enough for the command line */
	if ((argc-1) > servers_max) {
		debug("command line specifies %d servers, max is %d; attempting to compensate",
			argc-1, servers_max);
		servers_max = argc-1;
	}
	servers = pen_calloc(servers_max+2, sizeof *servers);

	nservers = 0;
	current = 0;

	server = 0;

	for (i = 1; i < argc; i++) {
		servers[server].status = 0;
		servers[server].c = 0;	/* connections... */
		setaddress(server, argv[i], port, proto);
		servers[server].sx = 0;
		servers[server].rx = 0;

		nservers++;
		server++;
	}
	while (nservers < servers_max) {
		servers[server].status = 0;
		servers[server].c = 0;	/* connections... */
		setaddress(server, "0.0.0.0", 0, proto);
		servers[server].sx = 0;
		servers[server].rx = 0;

		nservers++;
		server++;
	}
	if (e_server) {
		emerg_server = server;
		servers[server].status = 0;
		servers[server].c = 0;	/* connections... */
		setaddress(server, e_server, port, proto);
		servers[server].sx = 0;
		servers[server].rx = 0;
		server++;
	}

	if (a_server) {
		abuse_server = server;
		servers[server].status = 0;
		servers[server].c = 0;	/* connections... */
		setaddress(server, a_server, port, proto);
		servers[server].sx = 0;
		servers[server].rx = 0;
		server++;
	}

	for (i = 0; i < clients_max; i++) {
		clients[i].last = 0;
		memset(&clients[i].addr, 0, sizeof(clients[i].addr));
		clients[i].cno = 0;
		clients[i].connects = 0;
		clients[i].csx = 0;
		clients[i].crx = 0;
	}
	for (i = 0; i < connections_max; i++) {
		conns[i].upfd = -1;
		conns[i].downfd = -1;
		conns[i].upn = 0;
		conns[i].downn = 0;
	}

	if (debuglevel) {
		debug("%s starting", PACKAGE_STRING);
		debug("servers:");
		for (i = 0; i < nservers; i++) {
			debug("%2d %s:%d:%d:%d:%d:%d", i,
				pen_ntoa(&servers[i].addr), pen_getport(&servers[i].addr),
				servers[i].maxc, servers[i].hard,
				servers[i].weight, servers[i].prio);
		}
	}
}

/* return upstream file descriptor */
/* sticky = 1 if this client has used the server before */
static int try_server(int index, int sticky, struct sockaddr_storage *cli_addr)
{
	int upfd;
	int n = 0;
	int now = (int)time(NULL);
	int optval = 1;
	struct sockaddr_storage *addr = &servers[index].addr;

	if (debuglevel) debug("Trying server %d at time %d", index, now);
	if (pen_getport(addr) == 0) {
		if (debuglevel) debug("No port for you!");
		return -1;
	}
	if (now-servers[index].status < blacklist_time) {
		if (debuglevel) debug("Server %d is blacklisted", index);
		return -1;
	}
	if (servers[index].maxc != 0 &&
	    (servers[index].c >= servers[index].maxc) &&
	    (sticky == 0 || servers[index].c >= servers[index].hard)) {
		if (debuglevel)
			debug("Server %d is overloaded: sticky=%d, maxc=%d, hard=%d",
				index, sticky,
				servers[index].maxc, servers[index].hard);
		return -1;
	}
	if (!match_acl(servers[index].acl, cli_addr)) {
		if (debuglevel) debug("try_server: denied by acl");
		return -1;
	}

	upfd = socket(addr->ss_family, protoid, 0);
	if (upfd < 0) error("Error opening socket: %d", errno);

	setsockopt(upfd, SOL_SOCKET, SO_KEEPALIVE, &optval, sizeof optval);

	sigaction(SIGALRM, &alrmaction, NULL);
	alarm(timeout);
	if (debuglevel) {
		debug("Connecting to %s", pen_ntoa(addr));
		pen_dumpaddr(addr);
	}
	n = connect(upfd, (struct sockaddr *)addr, pen_ss_size(addr));
	alarm(0);	/* cancel scheduled timeout, if there is one */
	if (n == -1) {
		if (servers[index].status == 0)
			debug("Server %d failed, retry in %d sec: %s", index, blacklist_time, strerror(errno));
		servers[index].status = (int)time(NULL);
		close(upfd);
		return -1;
	}
	if (servers[index].status) {
		servers[index].status=0;
		if (debuglevel) debug("Server %d ok", index);
	}
	if (debuglevel) debug("Successful connect to server %d", index);
	return upfd;
}

static void open_log(char *logfile)
{
	if (logfp) {
		fclose(logfp);
		logfp = NULL;
	}
	if (logsock >= 0) {
		close(logsock);
		logsock = -1;
	}
	if (logfile) {
		char *p = strchr(logfile, ':');
		if (p && logfile[0] != '/') {	/* log to net */
			struct hostent *hp;
			if (debuglevel) debug("net log to %s", logfile);
			*p++ = '\0';
			logsock = socket(PF_INET, SOCK_DGRAM, 0);
			if (logsock < 0) error("Can't create log socket");
			logserver.sin_family = AF_INET;
			hp = gethostbyname(logfile);
			if (hp == NULL) error("Bogus host %s", logfile);
			memcpy(&logserver.sin_addr.s_addr,
				hp->h_addr, hp->h_length);
			logserver.sin_port = htons(atoi(p));
		} else {	/* log to file */
			if (debuglevel) debug("file log to %s", logfile);
			logfp = fopen(logfile, "a");
			if (!logfp) error("Can't open logfile %s", logfile);
		}
	}
}

static void read_cfg(char *);

static void write_cfg(char *p)
{
	int i, j;
	struct in_addr ip;
	char ip_str[INET6_ADDRSTRLEN];
	time_t now;
	struct tm *nowtm;
	char nowstr[80];
	FILE *fp = fopen(p, "w");
	if (!fp) {
		debug("Can't open file '%s'", p);
		return;
	}
	now = time(NULL);
	nowtm = localtime(&now);
	strftime(nowstr, sizeof(nowstr), "%Y-%m-%d %H:%M:%S", nowtm);
	fprintf(fp, "# Generated by pen %s\n", nowstr);
	fprintf(fp, "# pen");
	if (udp) fprintf(fp, " -U");
	if (foreground) fprintf(fp, " -f");
	if (exit_enabled) fprintf(fp, " -X");
	if (servers_max != SERVERS_MAX)
		fprintf(fp, " -S %d", servers_max);
	if (clients_max != CLIENTS_MAX)
		fprintf(fp, " -c %d", clients_max);
	if (e_server) fprintf(fp, " -e %s", e_server);
	if (a_server) fprintf(fp, " -B %s", a_server);
	if (jail) fprintf(fp, " -j '%s'", jail);
	if (pidfile) fprintf(fp, " -p '%s'", pidfile);
	if (user) fprintf(fp, " -u '%s'", user);
	if (connections_max != CONNECTIONS_MAX)
		fprintf(fp, " -x %d", connections_max);
	fprintf(fp, " -F '%s' -C %s %s\n", p, ctrlport, listenport);
	for (i = 0; i < ACLS_MAX; i++) {
		fprintf(fp, "no acl %d\n", i);
		for (j = 0; j < nacls[i]; j++) {
			fprintf(fp, "acl %d %s ", i,
				acls[i][j].permit?"permit":"deny");
			switch (acls[i][j].class) {
			case ACE_IPV4:
				memcpy(&ip, &acls[i][j].ace.ipv4.ip, 4);
				fprintf(fp, "%s ", inet_ntoa(ip));
				memcpy(&ip, &acls[i][j].ace.ipv4.mask, 4);
				fprintf(fp, "%s\n", inet_ntoa(ip));
				break;
			case ACE_IPV6:
				fprintf(fp, "%s/%d\n",
					inet_ntop(AF_INET6,
						&acls[i][j].ace.ipv6.ip,
						ip_str, sizeof ip_str),
					acls[i][j].ace.ipv6.len);
				break;
			case ACE_GEO:
				fprintf(fp, "country %c%c\n",
					acls[i][j].ace.geo.country[0],
					acls[i][j].ace.geo.country[1]);
				break;
			default:
				debug("Unknown ACE class %d (this is probably a bug)",
					acls[i][j].class);
			}
		}
	}
	if (asciidump) fprintf(fp, "ascii\n");
	else fprintf(fp, "no ascii\n");
	fprintf(fp, "blacklist %d\n", blacklist_time);
	if (nblock) fprintf(fp, "no block\n");
	else fprintf(fp, "block\n");
	fprintf(fp, "client_acl %d\n", client_acl);
	fprintf(fp, "control_acl %d\n", control_acl);
	fprintf(fp, "debug %d\n", debuglevel);
	if (delayed_forward) fprintf(fp, "delayed_forward\n");
	else fprintf(fp, "no delayed_forward\n");
	if (hash) fprintf(fp, "hash\n");
	else fprintf(fp, "no hash\n");
	if (http) fprintf(fp, "http\n");
	else fprintf(fp, "no http\n");
	if (logfile) fprintf(fp, "log %s\n", logfile);
	else fprintf(fp, "no log\n");
	if (roundrobin) fprintf(fp, "roundrobin\n");
	else fprintf(fp, "no roundrobin\n");
	for (i = 0; i < nservers; i++) {
		fprintf(fp,
			"server %d acl %d address %s port %d max %d hard %d",
			i, servers[i].acl,
			pen_ntoa(&servers[i].addr), pen_getport(&servers[i].addr),
			servers[i].maxc, servers[i].hard);
		if (weight) fprintf(fp, " weight %d", servers[i].weight);
		if (prio) fprintf(fp, " prio %d", servers[i].prio);
		fprintf(fp, "\n");
	}
	if (stubborn) fprintf(fp, "stubborn\n");
	else fprintf(fp, "no stubborn\n");
	fprintf(fp, "timeout %d\n", timeout);
	fprintf(fp, "tracking %d\n", tracking_time);
	if (webfile) fprintf(fp, "web_stats %s\n", webfile);
	else fprintf(fp, "no web_stats\n");
	if (weight) fprintf(fp, "weight\n");
	else fprintf(fp, "no weight\n");
	if (prio) fprintf(fp, "prio\n");
	else fprintf(fp, "no prio\n");
	fclose(fp);
}

static void do_cmd(char *b, void (*output)(char *, void *), void *op)
{
	char *p, *q;
	int n, fl;
	FILE *fp;

	if (debuglevel) {
		debug("do_cmd(%s, %p, %p)", b, output, op);
	}
	p = strchr(b, '\r');
	if (p) *p = '\0';
	p = strchr(b, '\n');
	if (p) *p = '\0';
	p = strtok(b, " ");
	if (p == NULL) return;
	if (!strcmp(p, "acl")) {
		char *no, *pd, *ip, *ma;
		/* acl N permit|deny ipaddr [mask] */
		if ((no = strtok(NULL, " ")) &&
		    (pd = strtok(NULL, " ")) &&
		    (ip = strtok(NULL, " "))) {
			int a = atoi(no);
			int permit;
			if (!strcmp(pd, "permit")) permit = 1;
			else if (!strcmp(pd, "deny")) permit = 0;
			else {
				debug("acl: expected permit|deny");
				return;
			}
			if (!strcmp(ip, "country")) {
				char *country = strtok(NULL, " ");
				if (!country) {
					debug("acl: expected country");
					return;
				}
				add_acl_geo(a, country, permit);
			} else if (strchr(ip, ':')) {
				unsigned char ipaddr[INET6_ADDRSTRLEN];
				ma = strchr(ip, '/');
				if (ma) {
					*ma++ = '\0';
				} else {
					ma = "128";
				}
				if (inet_pton(AF_INET6, ip, ipaddr) != 1) {
					debug("acl: can't convert address %s", ip);
					return;
				}
				add_acl_ipv6(a, ipaddr, atoi(ma), permit);
			} else {
				struct in_addr ipaddr, mask;
				ma = strtok(NULL, " ");
				if (!ma) ma = "255.255.255.255";
				if (!inet_aton(ip, &ipaddr)) {
					debug("acl: bogus address '%s'\n", ip);
					return;
				}
				if (!inet_aton(ma, &mask)) {
					debug("acl: bogus mask '%s'\n", ma);
					return;
				}
				add_acl_ipv4(a, ipaddr.s_addr, mask.s_addr, permit);
			}
		}
	} else if (!strcmp(p, "ascii")) {
		asciidump = 1;
	} else if (!strcmp(p, "blacklist")) {
		p = strtok(NULL, " ");
		if (p) blacklist_time = atoi(p);
		sprintf(b, "%d\n", blacklist_time);
		output(b, op);
	} else if (!strcmp(p, "block")) {
		nblock = 0;
		fl = fcntl(listenfd, F_GETFL, 0);
		fcntl(listenfd, F_SETFL, fl & ~O_NONBLOCK);
		fl = fcntl(ctrlfd, F_GETFL, 0);
		fcntl(ctrlfd, F_SETFL, fl & ~O_NONBLOCK);
	} else if (!strcmp(p, "client_acl")) {
		p = strtok(NULL, " ");
		if (p) client_acl = atoi(p);
		if (client_acl < 0 || client_acl >= ACLS_MAX)
			client_acl = 0;
		sprintf(b, "%d\n", client_acl);
		output(b, op);
	} else if (!strcmp(p, "clients_max")) {
		sprintf(b, "%d\n", clients_max);
		output(b, op);
	} else if (!strcmp(p, "conn_max")) {
		sprintf(b, "%d\n", connections_max);
		output(b, op);
	} else if (!strcmp(p, "control")) {
		sprintf(b, "%s\n", ctrlport);
		output(b, op);
	} else if (!strcmp(p, "control_acl")) {
		p = strtok(NULL, " ");
		if (p) control_acl = atoi(p);
		if (control_acl < 0 || control_acl >= ACLS_MAX)
			control_acl = 0;
		sprintf(b, "%d\n", control_acl);
		output(b, op);
	} else if (!strcmp(p, "debug")) {
		p = strtok(NULL, " ");
		if (p) debuglevel = atoi(p);
		sprintf(b, "%d\n", debuglevel);
		output(b, op);
	} else if (!strcmp(p, "delayed_forward")) {
		delayed_forward = 1;
	} else if (!strcmp(p, "exit")) {
		if (exit_enabled) {
			quit(0);
		} else {
			sprintf(b,
				"Exit is not enabled; restart with -X flag\n");
			output(b, op);
		}
	} else if (!strcmp(p, "hash")) {
		hash = 1;
	} else if (!strcmp(p, "http")) {
		http = 1;
	} else if (!strcmp(p, "include")) {
		p = strtok(NULL, " ");
		if (p) {
			read_cfg(p);
		} else {
			debug("Usage: include filename");
		}
	} else if (!strcmp(p, "listen")) {
		sprintf(b, "%s\n", listenport);
		output(b, op);
	} else if (!strcmp(p, "log")) {
		p = strtok(NULL, " ");
		if (p) {
			free(logfile);
			logfile = pen_strdup(p);
			open_log(logfile);
		}
		if (logfile) {
			sprintf(b, "%s\n", logfile);
			output(b, op);
		}
	} else if (!strcmp(p, "mode")) {
		sprintf(b, "%sblock %sdelayed_forward %shash %sroundrobin %sstubborn %sweight %sprio\n",
			nblock?"no ":"",
			delayed_forward?"":"no ",
			hash?"":"no ",
			roundrobin?"":"no ",
			stubborn?"":"no ",
			weight?"":"no ",
			prio?"":"no ");
		output(b, op);
	} else if (!strcmp(p, "no")) {
		p = strtok(NULL, " ");
		if (p == NULL) return;
		if (!strcmp(p, "acl")) {
			int a;
			p = strtok(NULL, " ");
			a = atoi(p);
			del_acl(a);
		} else if (!strcmp(p, "ascii")) {
			asciidump = 0;
		} else if (!strcmp(p, "block")) {
			nblock = 1;
			fl = fcntl(listenfd, F_GETFL, 0);
			fcntl(listenfd, F_SETFL, fl | O_NONBLOCK);
			fl = fcntl(ctrlfd, F_GETFL, 0);
			fcntl(ctrlfd, F_SETFL, fl | O_NONBLOCK);
		} else if (!strcmp(p, "delayed_forward")) {
			delayed_forward = 0;
		} else if (!strcmp(p, "hash")) {
			hash = 0;
		} else if (!strcmp(p, "http")) {
			http = 0;
		} else if (!strcmp(p, "log")) {
			logfile = NULL;
			if (logfp) fclose(logfp);
			logfp = NULL;
		} else if (!strcmp(p, "prio")) {
			prio = 0;
		} else if (!strcmp(p, "roundrobin")) {
			roundrobin = 0;
		} else if (!strcmp(p, "stubborn")) {
			stubborn = 0;
		} else if (!strcmp(p, "web_stats")) {
			webfile = NULL;
		} else if (!strcmp(p, "weight")) {
			weight = 0;
		}
	} else if (!strcmp(p, "pid")) {
		sprintf(b, "%ld\n", (long)getpid());
		output(b, op);
	} else if (!strcmp(p, "prio")) {
		prio = 1;
	} else if (!strcmp(p, "recent")) {
		time_t when = time(NULL);
		p = strtok(NULL, " ");
		if (p) when -= atoi(p);
		else when -= 300;
		for (n = 0; n < clients_max; n++) {
			if (clients[n].last < when) continue;
			sprintf(b, "%s connects %ld sx %lld rx %lld\n",
				pen_ntoa(&clients[n].addr),
				clients[n].connects,
				clients[n].csx, clients[n].crx);
			output(b, op);
		}
	} else if (!strcmp(p, "roundrobin")) {
		roundrobin = 1;
	} else if (!strcmp(p, "server")) {
		p = strtok(NULL, " ");
		if (p == NULL) return;
		n = atoi(p);
		if (n < 0 || n >= nservers) return;
		while ((p = strtok(NULL, " ")) && (q = strtok(NULL, " "))) {
			if (!strcmp(p, "acl")) {
				servers[n].acl = atoi(q);
			} else if (!strcmp(p, "address")) {
				int result;
				debug("do_cmd: server %d address %s", n, q);
				result = pen_aton(q, &servers[n].addr);
				if (debuglevel) {
					debug("pen_aton returns %d", n);
					debug("address family = %d", servers[n].addr.ss_family);
				}
				if (debuglevel > 1) pen_dumpaddr(&servers[n].addr);
				if (result != 1) return;
			} else if (!strcmp(p, "port")) {
				pen_setport(&servers[n].addr, atoi(q));
			} else if (!strcmp(p, "max")) {
				servers[n].maxc = atoi(q);
			} else if (!strcmp(p, "hard")) {
				servers[n].hard = atoi(q);
			} else if (!strcmp(p, "blacklist")) {
				servers[n].status = time(NULL)+atoi(q)-blacklist_time;
			} else if (!strcmp(p, "weight")) {
				servers[n].weight = atoi(q);
			} else if (!strcmp(p, "prio")) {
				servers[n].prio = atoi(q);
			}
		}
	} else if (!strcmp(p, "servers")) {
		for (n = 0; n < nservers; n++) {
			sprintf(b, "%d addr %s port %d conn %d max %d hard %d weight %d prio %d sx %llu rx %llu\n",
				n, pen_ntoa(&servers[n].addr), pen_getport(&servers[n].addr),
				servers[n].c, servers[n].maxc, servers[n].hard,
				servers[n].weight, servers[n].prio,
				servers[n].sx, servers[n].rx);
			output(b, op);
		}
	} else if (!strcmp(p, "status")) {
		if (webstats()) {
			fp = fopen(webfile, "r");
			if (fp == NULL) {
				debug("Can't read webstats");
				return;
			}
			while (fgets(b, sizeof b, fp)) {
				output(b, op);
			}
			fclose(fp);
		} else {
			debug("Unable to create webstats");
		}
	} else if (!strcmp(p, "stubborn")) {
		stubborn = 1;
	} else if (!strcmp(p, "timeout")) {
		p = strtok(NULL, " ");
		if (p) timeout = atoi(p);
		sprintf(b, "%d\n", timeout);
		output(b, op);
	} else if (!strcmp(p, "tracking")) {
		p = strtok(NULL, " ");
		if (p) tracking_time = atoi(p);
		sprintf(b, "%d\n", tracking_time);
		output(b, op);
	} else if (!strcmp(p, "web_stats")) {
		p = strtok(NULL, " ");
		if (p) {
			free(webfile);
			webfile = pen_strdup(p);
		}
		if (webfile) {
			sprintf(b, "%s\n", webfile);
			output(b, op);
		}
	} else if (!strcmp(p, "weight")) {
		weight = 1;
	} else if (!strcmp(p, "write")) {
		p = strtok(NULL, " ");
		if (!p) p = cfgfile;
		if (p) {
			write_cfg(p);
		} else {
			debug("write: no file");
		}
	} else {
		debug("do_cmd: ignoring command starting with '%s'", p);
	}
}

static void output_net(char *b, void *op)
{
	int *fp = op;
	int n;
	n = write(*fp, b, strlen(b));
	if (n == -1) {
		debug("output_net: write failed");
	}
}

static void output_file(char *b, void *op)
{
	FILE *fp = op;
	fputs(b, fp);
}

static void do_ctrl(int downfd, struct sockaddr_storage *cli_addr)
{
	char b[4096];
	int n, max_b = sizeof b;

	if (!match_acl(control_acl, cli_addr)) {
		debug("do_ctrl: not from there");
	} else {
		n = read(downfd, b, max_b-1);
		if (n != -1) {
			b[n] = '\0';
			do_cmd(b, output_net, &downfd);
		}
	}
	close(downfd);
}

static void read_cfg(char *cf)
{
	FILE *fp;
	char b[4096];

	if (debuglevel) debug("read_cfg(%s)", cf);
	hupcounter++;
	if (cf == NULL) return;

	fp = fopen(cf, "r");
	if (fp == NULL) {
		debug("Can't read config file '%s'\n", cf);
		return;
	}
	while (fgets(b, sizeof b, fp)) {
		do_cmd(b, output_file, stdout);
	}
	fclose(fp);
}

static int server_by_weight(void)
{
	int best_server = -1;
	int best_load = -1;
	int i, load;
	int now = (int)time(NULL);

	if (debuglevel) debug("server_by_weight()");
	for (i = 0; i < nservers; i++) {
		if (now-servers[i].status < blacklist_time || servers[i].weight == 0) {
			continue;
		}
		load = (WEIGHT_FACTOR*servers[i].c)/servers[i].weight;
		if (best_server == -1 || load < best_load) {
			if (debuglevel)
				debug("Server %d has load %d",
					i, load);
			best_load = load;
			best_server = i;
		}
	}
	if (debuglevel) debug("Least loaded server = %d", best_server);
	return best_server;
}

static int server_by_prio(void)
{
	int best_server = -1;
	int best_prio = -1;
	int i, prio;
	int now = (int)time(NULL);

	if (debuglevel) debug("server_by_prio()");
	for (i = 0; i < nservers; i++) {
		if (now-servers[i].status < blacklist_time) {
			continue;
		}
		prio = servers[i].prio;
		if (best_server == -1 || prio < best_prio) {
			if (debuglevel)
				debug("Server %d has prio %d", i, prio);
			best_prio = prio;
			best_server = i;
		}
	}
	if (debuglevel) debug("Best prio server = %d", best_server);
	return best_server;
}

static void add_client(int downfd, struct sockaddr_storage *cli_addr)
{
	int upfd = -1, clino = -1, index = -1, n, pd, rc = 0;
	unsigned char b[BUFFER_MAX];
#ifdef HAVE_SSL
	SSL *ssl = NULL;

	/* check the ssl stuff before picking servers */
	if (ssl_context) {
		ssl = SSL_new(ssl_context);
		if (ssl == NULL) {
			int err = ERR_get_error();
			debug("SSL: error allocating handle: %s",
				ERR_error_string(err, NULL));
			goto Failure;
		}
		SSL_set_fd(ssl, downfd);
		SSL_set_accept_state(ssl);
	}
#endif

	/* we don't know the client address for udp until we read the message */
	if (udp) {
		socklen_t len = sizeof *cli_addr;
		rc = recvfrom(listenfd, b, sizeof b, 0, (struct sockaddr *)cli_addr, &len);
		if (debuglevel) debug("add_client: received %d bytes from client",
					rc);
		if (rc < 0) {
			if (errno != EINTR)
				perror("Error receiving data");
			goto Failure;
		}
	}
	pd = match_acl(client_acl, cli_addr);

	if (!pd) {
		if (debuglevel) debug("add_client: denied by acl");
		if (abuse_server != -1) {
			upfd = try_server(abuse_server, 0, cli_addr);
			if (upfd != -1) goto Success;
		}
		goto Failure;
	}

	if (!roundrobin) {
		// Load balancing with memory == No roundrobin
		clino = lookup_client(cli_addr);
		if (debuglevel) debug("lookup_client returns %d", clino);
		if (clino != -1) {
			index = clients[clino].cno;
			if (index != emerg_server && index != abuse_server) {
				upfd = try_server(index, 1, cli_addr);
				if (upfd != -1) goto Success;
			}
		}
	}
	if (prio) {
		index = server_by_prio();
		if (index != -1) {
			upfd = try_server(index, 0, cli_addr);
			if (upfd != -1) goto Success;
		}
	}
	if (weight) {
		index = server_by_weight();
		if (index != -1) {
			upfd = try_server(index, 0, cli_addr);
			if (upfd != -1) goto Success;
		}
	}
	if (hash) {
		index = pen_hash(cli_addr);
		upfd = try_server(index, 0, cli_addr);
		if (upfd != -1) goto Success;
	}

	if (!stubborn) {
		index = current;
		do {
			index = (index + 1) % nservers;
			if ((upfd = try_server(index, 0, cli_addr)) != -1) goto Success;
		} while (index != current);
		if (upfd == -1) goto Failure;
	}
	/* if we get here, we're dead */
	if (emerg_server != -1) {
		if (!emergency)
			debug("Using emergency server");
		emergency=1;
		if ((upfd = try_server(emerg_server, 0, cli_addr)) != -1) goto Success2;
	}
	debug("Couldn't find a server for client");
Failure:
	if (!udp){
	if (downfd != -1) close(downfd);
	if (upfd != -1) close(upfd);
	}
	return;
Success:
	emergency=0;
Success2:
	n = store_client(clino, cli_addr, index);
#ifdef HAVE_SSL
	store_conn(downfd, ssl, upfd, n, index);
#else
	store_conn(downfd, upfd, n, index);
#endif
	if (udp && rc > 0) {	/* pass on the message */
		/* we are "connected" and don't need sendto */
		rc = write(upfd, b, rc);
		if (debuglevel) debug("add_client: wrote %d bytes to socket %d",
					rc, upfd);
	}
	return;
}

static int open_unix_listener(char *a)
{
	int listenfd;
	struct sockaddr_un serv_addr;

	remove(a);
	memset(&serv_addr, 0, sizeof serv_addr);
	serv_addr.sun_family = AF_UNIX;
	snprintf(serv_addr.sun_path, sizeof serv_addr.sun_path, "%s", a);
	if ((listenfd = socket(AF_UNIX, SOCK_STREAM, 0)) < 0) {
		error("can't open stream socket");
	}
	if (bind(listenfd, (struct sockaddr *)&serv_addr, sizeof serv_addr) != 0) {
		error("can't bind local address");
	}
	listen(listenfd, 50);
	return listenfd;
}

static int open_listener(char *a)
{
	int listenfd;
	struct sockaddr_storage ss;

	char b[1024], *p;
	int one = 1;
	int fl;
	int optval = 1;
	int port;

	/* Handle Unix domain sockets separately */
	if (strchr(a, '/')) return open_unix_listener(a);

	memset(&ss, 0, sizeof ss);
	p = strrchr(a, ':');	/* look for : separating address from port */
	if (p) {
		/* found one, extract parts */
		if ((p-a) >= sizeof b) {
			error("Address %s too long", a);
			return -1;
		}
		strncpy(b, a, p-a);
		b[p-a] = '\0';
		port = getport(p+1, proto);
	} else {
		strcpy(b, "0.0.0.0");
		port = getport(a, proto);
	}

	if (!pen_aton(b, &ss)) {
		debug("Can't convert address '%s'", b);
		return -1;
	}
	pen_setport(&ss, port);

	if ((listenfd = socket(ss.ss_family, protoid, 0)) < 0) {
		error("can't open stream socket");
	}

	if (debuglevel) debug("local address=[%s:%d]", b, port);

	setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, (char *)&one, sizeof one);
	setsockopt(listenfd, SOL_SOCKET, SO_KEEPALIVE, &optval, sizeof optval);

	if (bind(listenfd, (struct sockaddr *)&ss, pen_ss_size(&ss)) < 0) {
		error("can't bind local address");
	}

	if (nblock) {
		if ((fl = fcntl(listenfd, F_GETFL, 0)) == -1)
			error("Can't fcntl, errno = %d", errno);
		if (fcntl(listenfd, F_SETFL, fl | O_NONBLOCK) == -1)
			error("Can't fcntl, errno = %d", errno);
	}
	listen(listenfd, 50);
	return listenfd;
}

static int flush_down(int i)
{
	int n;

#ifdef HAVE_SSL
	SSL *ssl = conns[i].ssl;

	if (ssl) {
		n = SSL_write(ssl, conns[i].downbptr, conns[i].downn);
		if (debuglevel) debug("SSL_write returns %d\n", n);
		if (n < 0) {
			int err = SSL_get_error(ssl, n);
			if (debuglevel) debug("SSL_write returns %d (SSL error %d)", n, err);
			if (err == SSL_ERROR_WANT_READ ||
			    err == SSL_ERROR_WANT_WRITE) {
				return 0;
			}
		}
	} else {
		n = write(conns[i].downfd, conns[i].downbptr, conns[i].downn);
	}
#else
	struct sockaddr name;
	size_t size = sizeof(struct sockaddr);

	if (!udp)
		n = write(conns[i].downfd, conns[i].downbptr, conns[i].downn);
	else
		n = sendto(conns[i].downfd, conns[i].downbptr, conns[i].downn, 0,
			(struct sockaddr *) &name, size);
#endif  /* HAVE_SSL */

	if (debuglevel > 1) debug("flush_down(%d) %d bytes", i, n);
	if (n > 0) {
		conns[i].downn -= n;
		if (conns[i].downn == 0)
			free(conns[i].downb);
		else
			conns[i].downbptr += n;
		clients[conns[i].clt].csx += n;
		conns[i].csx += n;
	}
	return n;
}

/* This only talks upstream and does not need ssl */
static int flush_up(int i)
{
	int n;

       struct sockaddr name;
       size_t size = sizeof(struct sockaddr);

	if (!udp)
		n = write(conns[i].upfd, conns[i].upbptr, conns[i].upn);
	else
		n = sendto(conns[i].upfd, conns[i].upbptr, conns[i].upn, 0,
			(struct sockaddr *) &name, size);

	if (debuglevel > 1) debug("flush_up(%d) %d bytes", i, n);
	if (n > 0) {
		conns[i].upn -= n;
		if (conns[i].upn == 0)
			free(conns[i].upb);
		else
			conns[i].upbptr += n;
		conns[i].ssx += n;
	}
	return n;
}

static void dump_fd_set(char *p, fd_set *s)
{
	int i;
	for (i = 0; i < 100; i++) {
		if (FD_ISSET(i, s)) debug("%s %d is set", p, i);
	}
}

/* For UDP, connection attempts to unreachable servers would sit in the
   connection table forever unless we remove them by force.
   This function is pretty brutal, it simply vacates the next slot
   after the most recently used one. This will always succeed.
*/
static void recycle_connection(void)
{
	int i;

	i = connections_last+1;
	if (i >= connections_max) i = 0;
	close_conn(i);
}

static void mainloop_select(void)
{
	int downfd;
	socklen_t clilen;
	fd_set w_read, w_write, w_error;
	int i, w_max, imax;
	usr1action.sa_handler = stats;
	sigemptyset(&usr1action.sa_mask);
	usr1action.sa_flags = 0;
	sigaction(SIGUSR1, &usr1action, NULL);

	hupaction.sa_handler = restart_log;
	sigemptyset(&hupaction.sa_mask);
	hupaction.sa_flags = 0;
	sigaction(SIGHUP, &hupaction, NULL);

	termaction.sa_handler = quit;
	sigemptyset(&termaction.sa_mask);
	termaction.sa_flags = 0;
	sigaction(SIGTERM, &termaction, NULL);

	alrmaction.sa_handler = alarm_handler;
	sigemptyset(&alrmaction.sa_mask);
	alrmaction.sa_flags = 0;
	signal(SIGPIPE, SIG_IGN);

	loopflag = 1;

	if (debuglevel) debug("mainloop_select()");
	while (loopflag) {
		int n;

		if (do_stats) {
			if (webfile) webstats();
			else textstats();
			do_stats=0;
		}
		if (do_restart_log) {
			if (logfp) {
				fclose(logfp);
				logfp = fopen(logfile, "a");
				if (!logfp)
					error("Can't open logfile %s", logfile);
			}
			read_cfg(cfgfile);
			do_restart_log=0;
		}
		FD_ZERO(&w_read);
		FD_ZERO(&w_write);
		FD_ZERO(&w_error);
		if (debuglevel) {
			debug("After zero");
			dump_fd_set("w_read", &w_read);
			dump_fd_set("w_write", &w_write);
		}
		w_max = 0;
		/* no point accepting connections we can't handle */
		if (debuglevel > 1) debug("last = %d, used = %d, max = %d",
					connections_last,
					connections_used,
					connections_max);

		if (udp && (connections_used >= connections_max)) recycle_connection();

		if (connections_used < connections_max) {
			FD_SET(listenfd, &w_read);  /* new connections */
			w_max = listenfd+1;
		} else {
			if (debuglevel) debug("Not listening");
		}
		if (ctrlfd != -1) {
			FD_SET(ctrlfd, &w_read);
			if (ctrlfd > listenfd) w_max = ctrlfd+1;
		}

		/* add sockets from open connections */

		imax = connections_max;

		for (i = 0; i < imax; i++) {
			/* downfd == -1 means this connection slot is unused */
			if (debuglevel > 1) debug("downfd == %d means connection slot %d is unused", conns[i].downfd, i);
			if (conns[i].downfd == -1) continue;

			/* we are never interested in additional udp data from the client */
			if (!udp) {
				if (conns[i].upn == 0) {
					if (debuglevel) debug("interested in reading from downstream socket %d of connection %d", conns[i].downfd, i);
					FD_SET(conns[i].downfd, &w_read);
					if (conns[i].downfd+1 > w_max) {
						w_max = conns[i].downfd+1;
					}
				} else {
					if (debuglevel) debug("interested in writing to upstream socket %d of connection %d", conns[i].upfd);
					FD_SET(conns[i].upfd, &w_write);
					if (conns[i].upfd+1 > w_max) {
						w_max = conns[i].upfd+1;
					}
				}
			}

			/* tcp and udp processing upstream is handled the same here */
			if (conns[i].downn == 0) {
				if (debuglevel) debug("interested in reading data from upstream socket %d of connection %d", conns[i].upfd, i);
				FD_SET(conns[i].upfd, &w_read);
				if (conns[i].upfd+1 > w_max) {
					w_max = conns[i].upfd+1;
				}
			} else {
				if (debuglevel) debug("interested in writing data to downstream socket %d of connection %d", conns[i].downfd, i);
				FD_SET(conns[i].downfd, &w_write);
				if (conns[i].downfd+1 > w_max) {
					w_max = conns[i].downfd+1;
				}
			}
		}
		if (debuglevel) {
			debug("After setting fd_sets");
			dump_fd_set("w_read", &w_read);
			dump_fd_set("w_write", &w_write);
		}

		/* Wait for a connection from a client process. */
		n = select(w_max, &w_read, &w_write, /*&w_error*/0, 0);
		if (n < 0 && errno != EINTR) {
			perror("select");
			error("Error on select");
		}
		if (n <= 0) continue;

		if (debuglevel) {
			debug("After select");
			dump_fd_set("w_read", &w_read);
			dump_fd_set("w_write", &w_write);
		}

		if (FD_ISSET(listenfd, &w_read)) {
			struct sockaddr_storage cli_addr;
			clilen = sizeof cli_addr;
#if 0	/* single accept */
			if (!udp) {
				downfd = accept(listenfd,
					(struct sockaddr *) &cli_addr, &clilen);
				if (downfd < 0) {
					if (debuglevel) perror("accept");
					continue;
				}
				if (clilen == 0) {
					if (debuglevel) perror("clilen");
					continue;
				}

			} else {
				downfd = listenfd;
			}
			add_client(downfd, &cli_addr);
#else	/* multi-accept */
			/* special case for udp */
			if (udp) {
				downfd = listenfd;
				add_client(downfd, &cli_addr);
			} else {
			/* process tcp connection(s) */
				for (i = 0; i < multi_accept; i++) {
					if (connections_used >= connections_max) break;
					downfd = accept(listenfd,
						(struct sockaddr *)&cli_addr, &clilen);
					if (downfd < 0) {
						if (debuglevel && errno != EAGAIN) {
							perror("accept");
						}
						break;
					}
					if (clilen == 0) {
						if (debuglevel) perror("clilen");
						break;
					}
					add_client(downfd, &cli_addr);
				}
				if (debuglevel) debug("accepted %d connections", i);
			}
#endif
		}

		/* check control port */
		if (ctrlfd != -1 && FD_ISSET(ctrlfd, &w_read)) {
			struct sockaddr_storage cli_addr;
			clilen = sizeof cli_addr;
			downfd = accept(ctrlfd,
				(struct sockaddr *) &cli_addr, &clilen);
			if (downfd < 0) {
				if (debuglevel) perror("accept");
				continue;
			}
			if (clilen == 0) {
				if (debuglevel) perror("clilen");
				continue;
			}
			do_ctrl(downfd, &cli_addr);
		}

		/* check sockets from open connections */
		if (debuglevel) debug("checking sockets from open connections");
		for (i = 0; i < connections_max; i++) {
			if (conns[i].downfd == -1) continue;
			if (debuglevel) {
				debug("checking connection slot %d", i);
				debug("\tfrom %s", pen_ntoa(&clients[conns[i].clt].addr));
				debug("\tto %s", pen_ntoa(&servers[conns[i].index].addr));
			}
			if (!udp && FD_ISSET(conns[i].downfd, &w_read)) {
				if (debuglevel) debug("want to read from downstream socket %d of connection %d", conns[i].downfd, i);
				if (copy_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (FD_ISSET(conns[i].upfd, &w_read)) {
				if (debuglevel) debug("want to read from upstream socket %d of connection %d", conns[i].upfd, i);
				if (copy_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (!udp && FD_ISSET(conns[i].downfd, &w_write)) {
				if (debuglevel) debug("want to write to downstream socket %d of connection %d", conns[i].downfd, i);
				if (flush_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (debuglevel > 1) debug("conns = %p; upfd = %d; i = %d", conns, conns[i].upfd, i);
			if (conns[i].upfd > 0 && FD_ISSET(conns[i].upfd, &w_write)) {
				if (debuglevel) debug("want to write to upstream socket %d of connection %d", conns[i].upfd, i);
				if (flush_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
		}
	}
}

#ifdef HAVE_POLL
static void dump_pollfd(struct pollfd *ufds, int nfds)
{
	int i;
	for (i = 0; i < nfds; i++) {
		debug("%d: <%d,%d,%d>", i,
			ufds[i].fd, (int)ufds[i].events, (int)ufds[i].revents);
	}
}

static void mainloop_poll(void)
{
	int downfd;
	socklen_t clilen;
	struct sockaddr_storage cli_addr;
	struct pollfd *ufds;
	int i, j, nfds;
	short downevents, upevents;
	signal(SIGUSR1, stats);
	signal(SIGHUP, restart_log);
	signal(SIGTERM, quit);
	signal(SIGPIPE, SIG_IGN);

	loopflag = 1;

	ufds = pen_malloc((connections_max*2+2)*sizeof *ufds);

	if (debuglevel) debug("POLLIN = %d, POLLOUT = %d", (int)POLLIN, (int)POLLOUT);
	if (debuglevel) debug("mainloop_poll()");
	while (loopflag) {
		int n;

		if (do_stats) {
			if (webfile) webstats();
			else textstats();
			do_stats=0;
		}
		if (do_restart_log) {
			if (logfp) {
				fclose(logfp);
				logfp = fopen(logfile, "a");
				if (!logfp)
					error("Can't open logfile %s", logfile);
			}
			read_cfg(cfgfile);
			do_restart_log=0;
		}
		nfds = 0;
		ufds[nfds].fd = listenfd;
		ufds[nfds++].events = POLLIN;	/* new connections */
		if (ctrlfd != -1) {
			ufds[nfds].fd = ctrlfd;
			ufds[nfds++].events = POLLIN;
		}

		/* add sockets from open connections */
		if (debuglevel) debug("filling pollfd structure");
		for (i = 0; i < connections_max; i++) {
			if (conns[i].downfd == -1) continue;
			upevents = downevents = 0;

			if (conns[i].upn == 0) downevents |= POLLIN;
			else upevents |= POLLOUT;

			if (conns[i].downn == 0) upevents |= POLLIN;
			else downevents |= POLLOUT;

			if (downevents) {
				ufds[nfds].fd = conns[i].downfd;
				ufds[nfds++].events = downevents;
			}
			if (upevents) {
				ufds[nfds].fd = conns[i].upfd;
				ufds[nfds++].events = upevents;
			}
		}

		if (debuglevel) dump_pollfd(ufds, nfds);

		/* Wait for a connection from a client process. */
		n = poll(ufds, nfds, -1);
		if (debuglevel) debug("n = %d", n);
		if (n < 0 && errno != EINTR) {
			perror("poll");
			error("Error on poll");
		}
		if (n <= 0) continue;

		if (debuglevel) dump_pollfd(ufds, nfds);
		j = 0;
		if (debuglevel) debug("checking pollfd structure");
		if (debuglevel) debug("revents[%d] = %d", j, (int)ufds[j].revents);
		if (ufds[j].revents & POLLIN) {
			clilen = sizeof cli_addr;
			downfd = accept(listenfd,
				(struct sockaddr *) &cli_addr, &clilen);
			if (downfd < 0) {
				if (debuglevel) perror("accept");
				continue;
			}
			if (clilen == 0) {
				if (debuglevel) perror("clilen");
				continue;
			}
			add_client(downfd, &cli_addr);
		}
		j++;

		/* check control port */
		if (ctrlfd != -1 && (ufds[j++].revents & POLLIN)) {
			if (debuglevel) debug("revents[%d] = %d", j-1, (int)POLLIN);
			clilen = sizeof cli_addr;
			downfd = accept(ctrlfd,
				(struct sockaddr *) &cli_addr, &clilen);
			if (downfd < 0) {
				if (debuglevel) perror("accept");
				continue;
			}
			if (clilen == 0) {
				if (debuglevel) perror("clilen");
				continue;
			}
			do_ctrl(downfd, &cli_addr);
			j++;
		}

		/* check sockets from open connections */
		for (i = 0; i < connections_max; i++) {
			if (conns[i].downfd == -1) continue;

			if (conns[i].downfd != ufds[j].fd) downevents = 0;
			else downevents = ufds[j++].revents;

			if (conns[i].upfd != ufds[j].fd) upevents = 0;
			else upevents = ufds[j++].revents;

			if (debuglevel) {
				debug("conn = %d, upevents = %d, downevents = %d",
					i, upevents, downevents);
				if (downevents || upevents) {
					debug("down[%d] = %d, up[%d] = %d",
						i, downevents, i, upevents);
			}
		}
			if (downevents & POLLIN) {
				if (copy_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (upevents & POLLIN) {
				if (copy_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (downevents & POLLOUT) {
				if (flush_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (upevents & POLLOUT) {
				if (flush_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
		}
	}
}
#endif	/* HAVE_POLL */

#ifdef HAVE_KQUEUE

static void dump_kevent(struct kevent *kev, int nfds)
{
	int i;
	struct kevent *kptr;
	for (i = 0; i < nfds; i++) {
		kptr = &kev[i];
		debug("kev[%d]: <i=%d, f=%d, f=%d, ff=%d, d=%d u=%p>", i,
		    kptr->ident, kptr->filter, kptr->flags,
		    kptr->fflags, kptr->data, kptr->udata);
	}

}

static void mainloop_kqueue(void)
{
	int downfd, clilen;
	int kq;
	struct kevent *kev, *kptr;
	connection *conn;
	struct sockaddr_storage cli_addr;
	int i, j, nfds;
	short downevents, upevents;

	loopflag = 1;

	kq = kqueue();
	if (kq == -1)
	{
		perror("kqueue");
		error("Error creating kernel queue");
	}

	kev = pen_malloc((connections_max*2+2)*sizeof *kev);

	if (debuglevel) debug("mainloop_kqueue()");
	while (loopflag) {
		int n;

		if (do_stats) {
			if (webfile) webstats();
			else textstats();
			do_stats=0;
		}
		if (do_restart_log) {
			if (logfp) {
				fclose(logfp);
				logfp = fopen(logfile, "a");
				if (!logfp)
					error("Can't open logfile %s", logfile);
			}
			read_cfg(cfgfile);
			do_restart_log=0;
		}
		kptr = kev;
		nfds = 0;

		/* FIXME: these two don't need to be done every loop;
		 * they'll persist until the sockets are closed. But moving
		 * them outside the loop adds complications (kptr initial
		 * setting etc) */
		EV_SET(kptr++, listenfd, EVFILT_READ, EV_ADD, 0, 0, 0);
		nfds++;
		if (ctrlfd != -1) {
			EV_SET(kptr++, ctrlfd, EVFILT_READ, EV_ADD, 0, 0, 0);
			nfds++;
		}

		/* add sockets from open connections */
		if (debuglevel) debug("filling kqueue structure");
		for (i = 0; i < connections_max; i++) {
			if (conns[i].downfd == -1) continue;
			upevents = downevents = 0;

			if (conns[i].upn == 0)
			{
				EV_SET(kptr++, conns[i].downfd, EVFILT_READ,
				    EV_ADD | EV_ONESHOT, 0, 0, &conns[i]);
				nfds++;
			}
			else
			{
				EV_SET(kptr++, conns[i].upfd, EVFILT_WRITE,
				    EV_ADD | EV_ONESHOT, 0, 0, &conns[i]);
				nfds++;
			}

			if (conns[i].downn == 0)
			{
				EV_SET(kptr++, conns[i].upfd, EVFILT_READ,
				    EV_ADD | EV_ONESHOT, 0, 0, &conns[i]);
				nfds++;
			}
			else
			{
				EV_SET(kptr++, conns[i].downfd, EVFILT_WRITE,
				    EV_ADD | EV_ONESHOT, 0, 0, &conns[i]);
				nfds++;
			}
		}

		if (debuglevel) dump_kevent(kev, nfds);

		/* Wait for a connection from a client process. */
		n = kevent(kq, kev, nfds, kev, nfds, NULL);
		if (debuglevel) debug("n = %d", n);
		if (n < 0 && errno != EINTR) {
			perror("kevent");
			error("Error on kevent");
		}
		if (n <= 0) continue;

		if (debuglevel) debug("checking kqueue structure");
		if (debuglevel) dump_kevent(kev, n);

		for(j = 0 ; j < n ; j++)
		{
			kptr = &kev[j];

			/* check listener */
			if (kptr->ident == listenfd)
			{
				clilen = sizeof cli_addr;
				downfd = accept(listenfd,
					(struct sockaddr *) &cli_addr, &clilen);
				if (downfd < 0) {
					if (debuglevel) perror("accept");
					continue;
				}
				if (clilen == 0) {
					if (debuglevel) perror("clilen");
					continue;
				}
				add_client(downfd, &cli_addr);
				continue;
			}

			/* check control port */
			if (ctrlfd != -1 && kptr->ident == ctrlfd)
			{
				clilen = sizeof cli_addr;
				downfd = accept(ctrlfd,
					(struct sockaddr *) &cli_addr, &clilen);
				if (downfd < 0) {
					if (debuglevel) perror("accept");
					continue;
				}
				if (clilen == 0) {
					if (debuglevel) perror("clilen");
					continue;
				}
				do_ctrl(downfd, &cli_addr);
				continue;
			}

			/* check sockets from open connections */
			conn = (connection *)kptr->udata;
			if (conn->downfd == -1) continue;

			if (conn->downfd != kptr->ident)
				downevents = 0;
			else
				downevents = kptr->filter;

			if (conn->upfd != kptr->ident)
				upevents = 0;
			else
				upevents = kptr->filter;

			i = conn->i;
			if (debuglevel) {
				debug("conn = %d, upevents = %d, downevents = %d",
					i, upevents, downevents);
			}

			if (downevents == EVFILT_READ) {
				if (copy_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (upevents == EVFILT_READ) {
				if (copy_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (downevents == EVFILT_WRITE) {
				if (flush_down(i) < 0) {
					close_conn(i);
					continue;
				}
			}
			if (upevents == EVFILT_WRITE) {
				if (flush_up(i) < 0) {
					close_conn(i);
					continue;
				}
			}
		}
	}
}
#endif	/* HAVE_KQUEUE */

static int options(int argc, char **argv)
{
	int c;
	char b[1024];

#ifdef HAVE_SSL
	char *opt = "B:C:F:S:T:b:c:e:j:l:o:p:t:u:w:x:DHPQWXUadfhnrsE:K:G:A:ZRL:";
#else
	char *opt = "B:C:F:S:T:b:c:e:j:l:o:p:t:u:w:x:DHPQWXUadfhnrs";
#endif

	while ((c = getopt(argc, argv, opt)) != -1) {
		switch (c) {
		case 'B':
			a_server = optarg;
			break;
		case 'C':
			ctrlport = optarg;
			break;
		case 'D':
			delayed_forward = 1;
			break;
		case 'F':
			cfgfile = optarg;
			break;
		case 'H':
			http = 1;
			break;
		case 'Q':
			use_kqueue = 1;
			break;
		case 'P':
			use_poll = 1;
			break;
		case 'S':
			servers_max = atoi(optarg);
			break;
		case 'T':
			tracking_time = atoi(optarg);
			break;
		case 'U':
			udp = 1;
			break;
		case 'W':
			weight = 1;
			break;
		case 'X':
	    		exit_enabled = 1;
	    		break;
		case 'a':
			asciidump = 1;
			break;
		case 'b':
			blacklist_time = atoi(optarg);
			break;
		case 'c':
			clients_max = atoi(optarg);
			break;
		case 'd':
			debuglevel++;
			break;
		case 'e':
			e_server = optarg;
			break;
		case 'f':
			foreground = 1;
			break;
		case 'h':
			hash = 1;
			break;
		case 'j':
			jail = optarg;
			break;
		case 'l':
			logfile = pen_strdup(optarg);
			break;
		case 'n':
			nblock = 0;
			break;
		case 'o':
			snprintf(b, sizeof b, "%s", optarg);
			do_cmd(optarg, output_file, stdout);
			break;
		case 'p':
			pidfile = optarg;
			break;
		case 'r':
			roundrobin = 1;
			break;
		case 's':
			stubborn = 1;
			break;
		case 't':
			timeout = atoi(optarg);
			if (timeout < 1) {
				usage();
			}
			break;
		case 'u':
			user = optarg;
			break;
		case 'x':
			connections_max = atoi(optarg);
			break;
		case 'w':
			webfile = pen_strdup(optarg);
			break;
#ifdef HAVE_SSL
		case 'E':
			certfile = optarg;
			break;
		case 'K':
			keyfile = optarg;
			break;
		case 'G':
			cacert_file = optarg;
			break;
		case 'A':
			cacert_dir = optarg;
			break;
		case 'Z':
			ssl_compat = 1;
			break;
		case 'R':
			require_peer_cert = 1;
			break;
		case 'L':
			if (strcmp(optarg, "ssl23") == 0)
				ssl_protocol = SRV_SSL_V23;
			else if (strcmp(optarg, "ssl2") == 0)
				ssl_protocol = SRV_SSL_V2;
			else if (strcmp(optarg, "ssl3") == 0)
				ssl_protocol = SRV_SSL_V3;
			else if (strcmp(optarg, "tls1") == 0)
				ssl_protocol = SRV_SSL_TLS1;
			else {
				fprintf(stderr, "protocol version %s not known\n", optarg);
				exit(1);
			}
			break;
#endif  /* HAVE_SSL */
		case '?':
		default:
			usage();
		}
	}

	return optind;
}

int main(int argc, char **argv)
{
	int i;
	struct passwd *pwd = NULL;
	struct rlimit r;
	int n = options(argc, argv);
	argc -= n;
	argv += n;

	if (argc < 1) {
		usage();
	}

	if ((connections_max*2+10) > FD_SETSIZE && !use_poll)
		error("Number of simultaneous connections to large.\n"
		      "Maximum is %d, or re-build pen with larger FD_SETSIZE",
		      (FD_SETSIZE-10)/2);

	getrlimit(RLIMIT_CORE, &r);
	r.rlim_cur = r.rlim_max;
	setrlimit(RLIMIT_CORE, &r);

	signal(SIGCHLD, SIG_IGN);

	if (!foreground) {
		background();
	}

#ifdef HAVE_SSL
	if (certfile) {
		ssl_init();
	}
#endif

	/* we must open listeners before dropping privileges */
	/* Control port */
	if (ctrlport) {
		if (getuid() == 0 && user == NULL) {
			debug("Won't open control port running as root; use -u to run as different user");
		} else {
			ctrlfd = open_listener(ctrlport);
		}
	}

	/* Balancing port */
	if (udp) {
		protoid = SOCK_DGRAM;
		proto = "udp";
	}

	listenport = argv[0];
	listenfd = open_listener(listenport);
	if (listenfd < 0)
	{
		return EXIT_FAILURE;
	}
	init_mask();
	init(argc, argv);

	/* we must look up user id before chrooting */
	if (user) {
		if (debuglevel) debug("Run as user %s", user);
		pwd = getpwnam(user);
		if (pwd == NULL) error("Can't getpwnam(%s)", user);
	}

	/* we must chroot before dropping privileges */
	if (jail) {
		if (debuglevel) debug("Run in %s", jail);
		if (chroot(jail) == -1) error("Can't chroot(%s)", jail);
	}

	/* ready to defang ourselves */
	if (pwd) {
		if (setgid(pwd->pw_gid) == -1)
			error("Can't setgid(%d)", (int)pwd->pw_gid);
		if (setuid(pwd->pw_uid) == -1)
			error("Can't setuid(%d)", (int)pwd->pw_uid);
	}

	read_cfg(cfgfile);
	open_log(logfile);
	if (pidfile) {
		pidfp = fopen(pidfile, "w");
		if (!pidfp) {
			error("Can't create pidfile %s", pidfile);
			exit(1);
		}
		fprintf(pidfp, "%d", (int)getpid());
		fclose(pidfp);
	}

#ifdef HAVE_GEOIP
	geoip4 = GeoIP_open_type(GEOIP_COUNTRY_EDITION, GEOIP_MEMORY_CACHE);
	if (geoip4 == NULL) debug("Could not initialize GeoIP for IPv4");
	geoip6 = GeoIP_open_type(GEOIP_COUNTRY_EDITION_V6, GEOIP_MEMORY_CACHE);
	if (geoip6 == NULL) debug("Could not initialize GeoIP for IPv6");
#endif

#ifdef HAVE_KQUEUE
	if (use_kqueue) mainloop_kqueue();
#else
	if (use_kqueue) error("You don't have kqueue()");
#endif /* HAVE_KQUEUE */

#ifdef HAVE_POLL
	if (use_poll) mainloop_poll();
#else
	if (use_poll) error("You don't have poll()");
#endif	/* HAVE_POLL */

	if (!use_kqueue && !use_poll) mainloop_select();

	if (debuglevel) debug("Exiting, cleaning up...");
	if (logfp) fclose(logfp);
	for (i = 0; i < connections_max; i++) {
		close_conn(i);
	}
	close(listenfd);
	if (pidfile) {
		unlink(pidfile);
	}
	return EXIT_SUCCESS;
}
