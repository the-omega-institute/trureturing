/* Independent fixed-storage n=14-only public PSW falsifier.
   Public mathematical specification: Pan thesis Chapter7/author MATLAB,
   EPTCS445 Conjecture7.8, and DGS Theorem1. See source_audit.json.
   No substantial MATLAB code copied; author MIT notice retained separately.
   Darwin implementation, C11, libproc and kqueue; no worker threads. */
#define _DARWIN_C_SOURCE
#ifndef __APPLE__
#error This resource supervisor supports Darwin only.
#endif
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <libproc.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/event.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "source_tests.h"

enum { NMAX=14, NSTAGES=16, CPU_SECONDS=1200, WALL_SECONDS=1500,
       SAMPLE_MS=100, SHARED_BYTES=4096 };
enum { RUNNING=0, ALL_PASS=1, CANDIDATE=2, INVALID=3,
       CONTROL_FAILURE=4, RESOURCE_FAILURE=5 };
static const uint64_t expected_inputs=UINT64_C(25401600);
static const uint64_t rss_ceiling=UINT64_C(1073741824);
typedef unsigned char Perm[NMAX];
typedef struct { Perm w,y; } Pair;
typedef struct { unsigned n,tilde; } Stage;
static const Stage stages[NSTAGES] = {
    {4,0},{5,0},{5,1},{6,0},{7,0},{7,1},{8,0},{9,0},
    {9,1},{10,0},{11,0},{11,1},{12,0},{13,0},{13,1},{14,0}
};
typedef struct {
    Pair path[NSTAGES];
    unsigned choice[NSTAGES];
    Perm point_w[NMAX+1],point_y[NMAX+1];
    unsigned removed[NMAX+1];
    Perm scratch,independent;
    Pair control;
    int histogram[NMAX+1];
    unsigned bad_r,bad_c;
} Workspace;
static Workspace work;
typedef struct {
    _Atomic uint64_t begun,executed,passed,cells;
    _Atomic unsigned ready,controls,outcome,scan_started;
    Perm input,output;
    unsigned bad_r,bad_c,input_rank,output_rank;
} Shared;
_Static_assert(sizeof(Workspace)<=16384,"workspace exceeds preregistered16KiB");
_Static_assert(sizeof(Shared)<=SHARED_BYTES,"shared fixed mapping overflow");
_Static_assert(sizeof(source_cases)+sizeof(stages)+1024<=4096,
               "literal source controls exceed4KiB bound");
static Shared *shared;
static int log_fd=-1;
static volatile sig_atomic_t caught_signal;
static pid_t owned_child;

static void output_failure(int code) {
    if(owned_child>0) {
        kill(owned_child,SIGKILL);
        while(wait4(owned_child,NULL,0,NULL)<0 && errno==EINTR) {}
    }
    _exit(code);
}

static bool write_all(int fd,const char *p,size_t n) {
    while(n) {
        ssize_t k=write(fd,p,n);
        if(k<0 && errno==EINTR) continue;
        if(k<=0) return false;
        p+=k; n-=(size_t)k;
    }
    return true;
}
static void emit(const char *fmt,...) {
    char line[1024];
    va_list ap;
    va_start(ap,fmt);
    int n=vsnprintf(line,sizeof line,fmt,ap);
    va_end(ap);
    if(n<0 || (size_t)n>=sizeof line) output_failure(91);
    if(!write_all(log_fd,line,(size_t)n)) output_failure(92);
    if(!write_all(STDOUT_FILENO,line,(size_t)n)) output_failure(93);
}
static bool permutation(const Perm w,unsigned n) {
    if(n<4 || n>NMAX) return false;
    unsigned bits=0;
    for(unsigned i=0;i<n;i++) {
        unsigned v=w[i];
        if(v<1 || v>n || (bits & (1u<<v))) return false;
        bits|=1u<<v;
    }
    return bits==((1u<<(n+1))-2u);
}
static bool block_member(const Perm w,unsigned n,bool tilde) {
    if(!permutation(w,n)) return false;
    unsigned split=(n+(tilde?1u:0u))/2;
    for(unsigned i=0;i<n;i++)
        if((i<split)!=(w[i]<=split)) return false;
    return true;
}
static bool parity_member(const Perm y,unsigned n) {
    if(!permutation(y,n)) return false;
    for(unsigned i=0;i<n;i++) if(((i+1u)^y[i]) & 1u) return false;
    return true;
}
static bool pair_member(const Pair *p,unsigned n,bool tilde) {
    return block_member(p->w,n,tilde) && parity_member(p->y,n);
}
static bool insert(const Perm a,unsigned old,unsigned p,Perm out) {
    if(old>=NMAX || p<1 || p>old+1) return false;
    for(unsigned i=0;i<p-1;i++) out[i]=a[i];
    out[p-1]=(unsigned char)(old+1);
    for(unsigned i=p;i<=old;i++) out[i]=a[i-1];
    return true;
}
static bool insert_swap(const Perm a,unsigned old,unsigned q,Perm out) {
    if(q<1 || q>old+1 || ((old+1-q)&1u)) return false;
    if(!insert(a,old,q,out)) return false;
    for(unsigned i=q;i<old;i+=2) {
        unsigned char v=out[i]; out[i]=out[i+1]; out[i+1]=v;
    }
    return true;
}
static void ru(const Perm a,unsigned n,Perm out) {
    for(unsigned i=0;i<n;i++) out[i]=(unsigned char)(n+1-a[n-1-i]);
}
static bool extend_pair(const Pair *a,unsigned old,bool odd,unsigned branch,Pair *b) {
    unsigned first=odd?old/2+1:(old+1)/2+1;
    return insert(a->w,old,first+branch,b->w) &&
           insert_swap(a->y,old,2*branch+(odd?1u:2u),b->y);
}
static unsigned direct_rank(const Perm w,unsigned r,unsigned c) {
    unsigned count=0;
    for(unsigned i=0;i<r;i++) if(w[i]<=c) count++;
    return count;
}
static bool direct_le(const Perm w,const Perm y,unsigned n) {
    bool ok=true;
    for(unsigned r=0;r<=n;r++) for(unsigned c=0;c<=n;c++)
        if(direct_rank(w,r,c)<direct_rank(y,r,c)) ok=false;
    return ok;
}
/* Histogram updates evaluate every NW cell, not sorted-prefix shortcuts. */
static bool all_nw(const Perm w,const Perm y,unsigned n,unsigned *r_bad,unsigned *c_bad) {
    memset(work.histogram,0,sizeof work.histogram);
    for(unsigned r=1;r<=n;r++) {
        work.histogram[w[r-1]]++;
        work.histogram[y[r-1]]--;
        int difference=0;
        for(unsigned c=1;c<=n;c++) {
            difference+=work.histogram[c];
            if(difference<0) { *r_bad=r; *c_bad=c; return false; }
        }
    }
    return true;
}
/* Independent point evaluation: maximum removal, then reconstruction using
   direct index formulas (not staged insert/insert_swap/ru). No C recursion. */
static bool point_image(const Perm input,unsigned n,Perm out) {
    if(!block_member(input,n,false)) return false;
    memcpy(work.point_w[n],input,n);
    for(unsigned m=n;m>4;m--) {
        unsigned p=0;
        while(p<m && work.point_w[m][p]!=m) p++;
        if(p==m || p<m/2) return false;
        work.removed[m]=p+1;
        for(unsigned i=0;i<m-1;i++)
            work.scratch[i]=work.point_w[m][i+(i>=p?1u:0u)];
        for(unsigned i=0;i<m-1;i++)
            work.point_w[m-1][i]=(m&1u)?work.scratch[i]:
                (unsigned char)(m-work.scratch[m-2-i]);
        if(!block_member(work.point_w[m-1],m-1,false)) return false;
    }
    work.point_y[4][0]=(work.point_w[4][0]==2)?3:1;
    work.point_y[4][2]=(unsigned char)(4-work.point_y[4][0]);
    work.point_y[4][1]=(work.point_w[4][2]==4)?4:2;
    work.point_y[4][3]=(unsigned char)(6-work.point_y[4][1]);
    for(unsigned m=5;m<=n;m++) {
        for(unsigned i=0;i<m-1;i++)
            work.scratch[i]=(m&1u)?work.point_y[m-1][i]:
                (unsigned char)(m-work.point_y[m-1][m-2-i]);
        unsigned p=work.removed[m];
        unsigned k=(m-1)/2;
        unsigned q=(m&1u)?2*(p-k)-1:2*(p-k-1);
        if(q<1 || q>m || ((m-q)&1u)) return false;
        unsigned slot=q-1;
        for(unsigned i=0;i<m;i++) {
            if(i<slot) work.point_y[m][i]=work.scratch[i];
            else if(i==slot) work.point_y[m][i]=(unsigned char)m;
            else work.point_y[m][i]=work.scratch[slot+((i-slot-1)^1u)];
        }
        if(!parity_member(work.point_y[m],m)) return false;
    }
    memcpy(out,work.point_y[n],n);
    return true;
}
static bool control(const char *name,bool ok) {
    emit("[%s] %s\n",ok?"PASS":"FAIL",name);
    if(!ok) { atomic_store(&shared->outcome,CONTROL_FAILURE); return false; }
    atomic_fetch_add(&shared->controls,1);
    return true;
}
static bool source_controls(void) {
    for(unsigned i=0;i<sizeof source_cases/sizeof source_cases[0];i++) {
        const SourceCase *c=&source_cases[i];
        if(!control(c->name,point_image(c->input,c->n,work.independent) &&
                    memcmp(work.independent,c->output,c->n)==0 &&
                    direct_le(c->input,c->output,c->n) &&
                    all_nw(c->input,c->output,c->n,&work.bad_r,&work.bad_c))) return false;
    }
    if(!control("ins3-public",insert(operation_input,6,3,work.scratch) &&
                memcmp(work.scratch,insertion_expected,7)==0)) return false;
    if(!control("inss3-public",insert_swap(operation_input,6,3,work.scratch) &&
                memcmp(work.scratch,swapping_expected,7)==0)) return false;
    if(!control("inss4-rejected",!insert_swap(operation_input,6,4,work.scratch))) return false;
    if(!control("ins-append",insert(operation_input,6,7,work.scratch) &&
                memcmp(work.scratch,append_expected,7)==0)) return false;
    if(!control("inss-append",insert_swap(operation_input,6,7,work.scratch) &&
                memcmp(work.scratch,append_expected,7)==0)) return false;
    ru(operation_input,6,work.scratch);
    if(!control("RU-public-operations",memcmp(work.scratch,ru_expected,6)==0)) return false;
    memcpy(work.path[0].w,source_cases[2].input,4);
    memcpy(work.path[0].y,source_cases[2].output,4);
    if(!control("staged-f5-worked",extend_pair(&work.path[0],4,true,0,&work.path[1]) &&
                memcmp(work.path[1].w,source_cases[4].input,5)==0 &&
                memcmp(work.path[1].y,source_cases[4].output,5)==0)) return false;
    ru(work.path[1].w,5,work.path[2].w); ru(work.path[1].y,5,work.path[2].y);
    if(!control("staged-f6-worked",pair_member(&work.path[2],5,true) &&
                extend_pair(&work.path[2],5,false,1,&work.path[3]) &&
                memcmp(work.path[3].w,source_cases[9].input,6)==0 &&
                memcmp(work.path[3].y,source_cases[9].output,6)==0)) return false;
    memcpy(work.path[0].w,source_cases[1].input,4);
    memcpy(work.path[0].y,source_cases[1].output,4);
    if(!control("staged-f5-append",extend_pair(&work.path[0],4,true,2,&work.path[1]) &&
                memcmp(work.path[1].w,source_cases[5].input,5)==0 &&
                memcmp(work.path[1].y,source_cases[5].output,5)==0)) return false;
    if(!control("rank-direction-positive",direct_le(order_lower,order_upper,4) &&
                all_nw(order_lower,order_upper,4,&work.bad_r,&work.bad_c))) return false;
    if(!control("rank-direction-negative",!direct_le(order_upper,order_lower,4) &&
                !all_nw(order_upper,order_lower,4,&work.bad_r,&work.bad_c))) return false;
    if(!control("obstruction-inputs",block_member(obstruction_u,6,false) &&
                parity_member(obstruction_v,6) && direct_le(obstruction_u,obstruction_v,6))) return false;
    if(!control("obstruction-displayed-slots",insert(obstruction_u,6,6,work.control.w) &&
                insert_swap(obstruction_v,6,5,work.control.y) &&
                memcmp(work.control.w,obstruction_ins,7)==0 &&
                memcmp(work.control.y,obstruction_inss,7)==0)) return false;
    if(!control("obstruction-not-comparable",!direct_le(work.control.w,work.control.y,7) &&
                !all_nw(work.control.w,work.control.y,7,&work.bad_r,&work.bad_c))) return false;
    emit("OBSTRUCTION first_bad_r=%u first_bad_c=%u input_rank=%u output_rank=%u actual_slots=6,5 printed_slots=5,4\n",
         work.bad_r,work.bad_c,direct_rank(work.control.w,work.bad_r,work.bad_c),
         direct_rank(work.control.y,work.bad_r,work.bad_c));
    if(!control("obstruction-not-special-f6",point_image(obstruction_u,6,work.independent) &&
                memcmp(work.independent,obstruction_true_f6,6)==0 &&
                memcmp(work.independent,obstruction_v,6)!=0)) return false;
    return true;
}
static void print_perm(const char *name,const Perm p,unsigned n) {
    char s[128]; size_t used=0;
    for(unsigned i=0;i<n;i++) {
        int k=snprintf(s+used,sizeof s-used,"%s%u",i?",":"",p[i]);
        if(k<0 || (size_t)k>=sizeof s-used) _exit(94);
        used+=(size_t)k;
    }
    emit("%s=[%s]\n",name,s);
}
static int scan(void) {
    uint64_t count=0,passed=0,cells=0;
    atomic_store(&shared->scan_started,1);
    emit("SCAN n=14 expected=%" PRIu64 " complete_cells_per_pass=196\n",expected_inputs);
    memset(work.choice,0,sizeof work.choice);
    for(unsigned seed=0;seed<4;seed++) {
        memcpy(work.path[0].w,source_cases[seed].input,4);
        memcpy(work.path[0].y,source_cases[seed].output,4);
        int d=0;
        while(d>=0) {
            unsigned n=stages[d].n;
            if(d==NSTAGES-1) {
                if(count>=expected_inputs) {
                    emit("INVALID exceeded maximum enumeration count\n");
                    atomic_store(&shared->outcome,INVALID); return INVALID;
                }
                atomic_store(&shared->begun,count+1);
                if(!pair_member(&work.path[d],14,false)) {
                    emit("INVALID final membership input_index=%" PRIu64 "\n",count+1);
                    atomic_store(&shared->outcome,INVALID); return INVALID;
                }
                bool ok=all_nw(work.path[d].w,work.path[d].y,14,&work.bad_r,&work.bad_c);
                count++;
                cells+=ok?196:(work.bad_r-1)*14+work.bad_c;
                atomic_store(&shared->cells,cells);
                atomic_store(&shared->executed,count);
                if(!ok) {
                    bool genuine=point_image(work.path[d].w,14,work.independent) &&
                        memcmp(work.independent,work.path[d].y,14)==0 &&
                        block_member(work.path[d].w,14,false) &&
                        parity_member(work.independent,14) &&
                        direct_rank(work.path[d].w,work.bad_r,work.bad_c)<
                        direct_rank(work.independent,work.bad_r,work.bad_c) &&
                        !direct_le(work.path[d].w,work.independent,14);
                    memcpy(shared->input,work.path[d].w,14);
                    memcpy(shared->output,work.path[d].y,14);
                    shared->bad_r=work.bad_r; shared->bad_c=work.bad_c;
                    shared->input_rank=direct_rank(work.path[d].w,work.bad_r,work.bad_c);
                    shared->output_rank=direct_rank(work.path[d].y,work.bad_r,work.bad_c);
                    print_perm("candidate_input",shared->input,14);
                    print_perm("candidate_output",shared->output,14);
                    emit("CANDIDATE independently_confirmed=%u index=%" PRIu64 " r=%u c=%u input_rank=%u output_rank=%u\n",
                         genuine?1u:0u,count,shared->bad_r,shared->bad_c,shared->input_rank,shared->output_rank);
                    atomic_store(&shared->outcome,genuine?CANDIDATE:INVALID);
                    return genuine?CANDIDATE:INVALID;
                }
                passed++;
                atomic_store(&shared->passed,passed);
                d--; continue;
            }
            Stage next=stages[d+1];
            bool ru_stage=(next.n==n);
            unsigned choices=ru_stage?1:(next.n&1u)?n/2+1:(n+1)/2;
            if(work.choice[d]==choices) { work.choice[d]=0; d--; continue; }
            unsigned branch=work.choice[d]++;
            if(ru_stage) {
                ru(work.path[d].w,n,work.path[d+1].w);
                ru(work.path[d].y,n,work.path[d+1].y);
            } else if(!extend_pair(&work.path[d],n,(next.n&1u)!=0,branch,&work.path[d+1])) {
                emit("INVALID stage insertion d=%d branch=%u\n",d,branch);
                atomic_store(&shared->outcome,INVALID); return INVALID;
            }
            if(!pair_member(&work.path[d+1],next.n,next.tilde!=0)) {
                emit("INVALID stage membership d=%d n=%u branch=%u\n",d+1,next.n,branch);
                atomic_store(&shared->outcome,INVALID); return INVALID;
            }
            d++;
        }
    }
    if(count!=expected_inputs || passed!=count || cells!=count*196) {
        emit("INVALID final count=%" PRIu64 " passed=%" PRIu64 " cells=%" PRIu64 "\n",count,passed,cells);
        atomic_store(&shared->outcome,INVALID); return INVALID;
    }
    atomic_store(&shared->outcome,ALL_PASS);
    emit("ALL_PASS executed=%" PRIu64 " passed=%" PRIu64 " NW_cells=%" PRIu64 "\n",count,passed,cells);
    return 0;
}
static void on_signal(int sig) { caught_signal=sig; }
static bool now_ns(clockid_t clock,uint64_t *out) {
    struct timespec ts;
    if(clock_gettime(clock,&ts)<0) return false;
    *out=(uint64_t)ts.tv_sec*UINT64_C(1000000000)+(uint64_t)ts.tv_nsec;
    return true;
}
static bool rss_info(pid_t pid,uint64_t *rss,unsigned *threads) {
    struct proc_taskinfo info;
    memset(&info,0,sizeof info);
    int got=proc_pidinfo(pid,PROC_PIDTASKINFO,0,&info,sizeof info);
    if(got!=(int)sizeof info) return false;
    *rss=info.pti_resident_size; *threads=(unsigned)info.pti_threadnum;
    return true;
}
static pid_t reap(pid_t child,int *status,struct rusage *usage,int flags) {
    pid_t got;
    do { got=wait4(child,status,flags,usage); } while(got<0 && errno==EINTR);
    return got;
}
static void child_run(int ready_fd,int permission_fd) {
    signal(SIGINT,SIG_DFL); signal(SIGTERM,SIG_DFL); signal(SIGHUP,SIG_DFL);
    signal(SIGPIPE,SIG_DFL);
    struct rlimit limit={CPU_SECONDS,CPU_SECONDS},readback;
    if(setrlimit(RLIMIT_CPU,&limit)<0 || getrlimit(RLIMIT_CPU,&readback)<0 ||
       readback.rlim_cur!=CPU_SECONDS || readback.rlim_max!=CPU_SECONDS) {
        emit("RESOURCE_FAILURE RLIMIT_CPU errno=%d diagnostic=%s\n",errno,strerror(errno));
        atomic_store(&shared->outcome,RESOURCE_FAILURE); _exit(RESOURCE_FAILURE);
    }
    emit("RESOURCE RLIMIT_CPU soft=%llu hard=%llu seconds; RLIMIT_AS/DATA not requested\n",
         (unsigned long long)readback.rlim_cur,(unsigned long long)readback.rlim_max);
    atomic_store(&shared->ready,1);
    if(!write_all(ready_fd,"R",1)) _exit(RESOURCE_FAILURE);
    close(ready_fd);
    char permission=0; ssize_t got;
    do { got=read(permission_fd,&permission,1); } while(got<0 && errno==EINTR);
    close(permission_fd);
    if(got!=1 || permission!='G') {
        emit("RESOURCE_FAILURE no supervisor permission\n");
        atomic_store(&shared->outcome,RESOURCE_FAILURE); _exit(RESOURCE_FAILURE);
    }
    if(!source_controls()) _exit(CONTROL_FAILURE);
    emit("CONTROLS all_passed=%u; scan permission granted\n",atomic_load(&shared->controls));
    _exit(scan());
}
int main(int argc,char **argv) {
    if(argc!=3) { fprintf(stderr,"usage: checker RUNNER_DIRECTORY STOP_UTC (YYYY-MM-DDTHH:MM:SSZ)\n"); return 64; }
    struct tm stop_tm; memset(&stop_tm,0,sizeof stop_tm);
    char *tail=strptime(argv[2],"%Y-%m-%dT%H:%M:%SZ",&stop_tm);
    if(!tail || *tail) { fprintf(stderr,"invalid STOP_UTC\n"); return 64; }
    time_t stop_epoch=timegm(&stop_tm);
    if(stop_epoch<=0) { fprintf(stderr,"invalid STOP_UTC epoch\n"); return 64; }
    int dir_fd=open(argv[1],O_RDONLY|O_DIRECTORY);
    if(dir_fd<0) { perror("runner-directory"); return 65; }
    log_fd=openat(dir_fd,"checker.stdout.log",O_WRONLY|O_CREAT|O_EXCL,0600);
    if(log_fd<0) { perror("fresh checker.stdout.log"); close(dir_fd); return 65; }
    int once=openat(dir_fd,"scan.once",O_WRONLY|O_CREAT|O_EXCL,0600);
    if(once<0) { emit("BOUNDARY scan.once errno=%d %s; zero retries\n",errno,strerror(errno)); return 65; }
    if(!write_all(once,"one bounded attempt\n",20)) { emit("BOUNDARY scan.once write failure\n"); return 65; }
    close(once);
    int evidence_fd=openat(dir_fd,"terminal.json",O_WRONLY|O_CREAT|O_EXCL,0600);
    if(evidence_fd<0) { emit("BOUNDARY terminal.json errno=%d %s\n",errno,strerror(errno)); return 65; }
    emit("STORAGE workspace=%zu shared_mapping=%u literal_bound=4096 log_frame=1024 terminal_frame=4096 mathematical_stack_bound=65536 combined_bound=131072 bytes\n",
         sizeof work,SHARED_BYTES);
    emit("BUILD Apple clang21 C11 O3 fixed arrays libproc kqueue; no threads/no per-input heap calls\n");
    shared=mmap(NULL,SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_ANON|MAP_SHARED,-1,0);
    if(shared==MAP_FAILED) { emit("BOUNDARY mmap errno=%d %s\n",errno,strerror(errno)); return 69; }
    memset(shared,0,SHARED_BYTES);
    if(!atomic_is_lock_free(&shared->executed)) { emit("BOUNDARY counters not lock free\n"); return 69; }
    uint64_t self_rss=0; unsigned self_threads=0;
    if(!rss_info(getpid(),&self_rss,&self_threads)) { emit("BOUNDARY proc_pidinfo self errno=%d %s\n",errno,strerror(errno)); return 69; }
    uint64_t start=0,realtime=0;
    if(!now_ns(CLOCK_MONOTONIC,&start) || !now_ns(CLOCK_REALTIME,&realtime)) { emit("BOUNDARY clock_gettime errno=%d\n",errno); return 69; }
    uint64_t stop_ns=(uint64_t)stop_epoch*UINT64_C(1000000000);
    if(realtime>=stop_ns) { emit("BOUNDARY substantive deadline already expired\n"); return 69; }
    uint64_t duration=(uint64_t)WALL_SECONDS*UINT64_C(1000000000);
    if(stop_ns-realtime<duration) duration=stop_ns-realtime;
    uint64_t deadline=start+duration;
    emit("RESOURCE supervisor_self_rss=%" PRIu64 " bytes threads=%u effective_wall_limit=%.9f seconds UTC_cap=%s watchdog_interval_ms=%u ceiling=%" PRIu64 " bytes sampled_only=1\n",
         self_rss,self_threads,(double)duration/1e9,argv[2],SAMPLE_MS,rss_ceiling);
    int ready_pipe[2],permission_pipe[2];
    if(pipe(ready_pipe)<0 || pipe(permission_pipe)<0) { emit("BOUNDARY pipe errno=%d\n",errno); return 69; }
    int queue=kqueue();
    if(queue<0) { emit("BOUNDARY kqueue errno=%d\n",errno); return 69; }
    struct sigaction action; memset(&action,0,sizeof action);
    action.sa_handler=on_signal; sigemptyset(&action.sa_mask);
    if(sigaction(SIGINT,&action,NULL)<0 || sigaction(SIGTERM,&action,NULL)<0 ||
       sigaction(SIGHUP,&action,NULL)<0) { emit("BOUNDARY sigaction errno=%d\n",errno); return 69; }
    if(signal(SIGPIPE,SIG_IGN)==SIG_ERR) { emit("BOUNDARY SIGPIPE errno=%d\n",errno); return 69; }
    pid_t child=fork();
    if(child<0) { emit("BOUNDARY fork errno=%d\n",errno); return 69; }
    if(child==0) {
        close(ready_pipe[0]); close(permission_pipe[1]); close(queue);
        close(evidence_fd); close(dir_fd);
        child_run(ready_pipe[1],permission_pipe[0]);
        _exit(95);
    }
    owned_child=child;
    close(ready_pipe[1]); close(permission_pipe[0]);
    struct kevent changes[4],event;
    EV_SET(&changes[0],(uintptr_t)ready_pipe[0],EVFILT_READ,EV_ADD|EV_ENABLE,0,0,NULL);
    EV_SET(&changes[1],(uintptr_t)child,EVFILT_PROC,EV_ADD|EV_ENABLE|EV_ONESHOT,NOTE_EXIT,0,NULL);
    EV_SET(&changes[2],10,EVFILT_TIMER,EV_ADD|EV_ENABLE,NOTE_USECONDS,(intptr_t)SAMPLE_MS * 1000,NULL);
    EV_SET(&changes[3],11,EVFILT_TIMER,EV_ADD|EV_ENABLE|EV_ONESHOT,NOTE_NSECONDS,(intptr_t)duration,NULL);
    const char *stop_reason="child_completed";
    bool killed=false,ready=false,timer_seen=false,permission=false;
    unsigned samples=0; uint64_t sampled_peak=0;
    int status=0; struct rusage usage; memset(&usage,0,sizeof usage);
    if(kevent(queue,changes,4,NULL,0,NULL)<0) {
        emit("BOUNDARY kevent registration errno=%d %s\n",errno,strerror(errno));
        stop_reason="timer_registration_failure"; killed=true;
    }
    while(!killed) {
        pid_t got=reap(child,&status,&usage,WNOHANG);
        if(got==child) break;
        if(got<0) { emit("BOUNDARY wait4 errno=%d\n",errno); stop_reason="wait4_failure"; killed=true; break; }
        if(caught_signal) { stop_reason="supervisor_signal"; killed=true; break; }
        int k=kevent(queue,NULL,0,&event,1,NULL);
        if(k<0 && errno==EINTR) continue;
        if(k<0 || (event.flags & EV_ERROR)) {
            emit("BOUNDARY kevent wait errno=%d event_data=%lld\n",errno,k<0?0LL:(long long)event.data);
            stop_reason="timer_event_failure"; killed=true; break;
        }
        uint64_t current=0;
        if(!now_ns(CLOCK_MONOTONIC,&current)) { stop_reason="clock_failure"; killed=true; break; }
        if(current>=deadline || (event.filter==EVFILT_TIMER && event.ident==11)) {
            stop_reason="wall_deadline"; killed=true; break;
        }
        if(event.filter==EVFILT_PROC) continue;
        if(event.filter==EVFILT_READ) {
            char message=0; ssize_t bytes=read(ready_pipe[0],&message,1);
            if(bytes!=1 || message!='R') {
                got=reap(child,&status,&usage,WNOHANG);
                if(got==child) break;
                emit("BOUNDARY ready handshake bytes=%lld errno=%d\n",(long long)bytes,errno);
                stop_reason="ready_handshake_failure"; killed=true; break;
            }
            ready=true;
            struct kevent remove_event;
            EV_SET(&remove_event,(uintptr_t)ready_pipe[0],EVFILT_READ,EV_DELETE,0,0,NULL);
            if(kevent(queue,&remove_event,1,NULL,0,NULL)<0) { stop_reason="ready_event_removal_failure"; killed=true; break; }
        }
        if(event.filter==EVFILT_TIMER && event.ident==10) timer_seen=true;
        if(ready && (event.filter==EVFILT_TIMER || !permission)) {
            uint64_t rss=0; unsigned threads=0;
            if(!rss_info(child,&rss,&threads)) {
                got=reap(child,&status,&usage,WNOHANG);
                if(got==child) break;
                emit("BOUNDARY proc_pidinfo child errno=%d %s\n",errno,strerror(errno));
                stop_reason="rss_observation_failure"; killed=true; break;
            }
            samples++; if(rss>sampled_peak) sampled_peak=rss;
            if(rss>=rss_ceiling) { stop_reason="sampled_rss_watchdog"; killed=true; break; }
            if(threads!=1) { stop_reason="single_thread_contract_failure"; killed=true; break; }
            if(timer_seen && !permission) {
                emit("RESOURCE ready CPU_readback=1 watchdog_observed=1 timer_observed=1 child_threads=1 child_rss=%" PRIu64 " bytes; mathematical permission granted\n",rss);
                if(!write_all(permission_pipe[1],"G",1)) { stop_reason="permission_write_failure"; killed=true; break; }
                close(permission_pipe[1]); permission=true;
            }
            if(samples%50==0) emit("OBSERVATION wall_seconds=%.6f begun=%" PRIu64 " executed=%" PRIu64 " passed=%" PRIu64 " sampled_rss=%" PRIu64 " bytes\n",
                (double)(current-start)/1e9,atomic_load(&shared->begun),atomic_load(&shared->executed),
                atomic_load(&shared->passed),rss);
        }
    }
    if(killed) {
        emit("STOP reason=%s signal=%d begun=%" PRIu64 " executed=%" PRIu64 "\n",stop_reason,(int)caught_signal,
             atomic_load(&shared->begun),atomic_load(&shared->executed));
        if(kill(child,SIGKILL)<0 && errno!=ESRCH) emit("BOUNDARY kill errno=%d %s\n",errno,strerror(errno));
        if(reap(child,&status,&usage,0)!=child) { emit("BOUNDARY child could not be reaped errno=%d\n",errno); return 70; }
    }
    owned_child=0;
    uint64_t end=0;
    if(!now_ns(CLOCK_MONOTONIC,&end)) { emit("BOUNDARY final clock errno=%d\n",errno); return 70; }
    if(WIFSIGNALED(status) && !killed) stop_reason="child_signal";
    if(WIFEXITED(status) && WEXITSTATUS(status)!=0 && !killed)
        stop_reason=atomic_load(&shared->outcome)==CANDIDATE?"first_genuine_candidate":"child_error";
    double user_cpu=(double)usage.ru_utime.tv_sec+(double)usage.ru_utime.tv_usec/1e6;
    double system_cpu=(double)usage.ru_stime.tv_sec+(double)usage.ru_stime.tv_usec/1e6;
    emit("TERMINAL reason=%s outcome_code=%u raw_wait_status=%d exit=%d signal=%d reaped=1 executed=%" PRIu64 " passed=%" PRIu64 " cells=%" PRIu64 " wall=%.9f user_cpu=%.6f system_cpu=%.6f wait4_peak_rss=%ld bytes sampled_peak_rss=%" PRIu64 " bytes samples=%u\n",
         stop_reason,atomic_load(&shared->outcome),status,WIFEXITED(status)?WEXITSTATUS(status):-1,
         WIFSIGNALED(status)?WTERMSIG(status):0,atomic_load(&shared->executed),atomic_load(&shared->passed),
         atomic_load(&shared->cells),(double)(end-start)/1e9,user_cpu,system_cpu,usage.ru_maxrss,sampled_peak,samples);
    char json[4096];
    int length=snprintf(json,sizeof json,
        "{\n \"stop_reason\":\"%s\",\n \"child_outcome_code\":%u,\n \"raw_wait_status\":%d,\n \"exit_code\":%d,\n \"signal\":%d,\n \"child_reaped\":true,\n"
        " \"mathematical_permission\":%s,\n \"controls_passed\":%u,\n \"scan_started\":%s,\n \"n\":14,\n \"expected_inputs\":%" PRIu64 ",\n"
        " \"begun\":%" PRIu64 ",\n \"executed\":%" PRIu64 ",\n \"all_cells_passed_inputs\":%" PRIu64 ",\n \"evaluated_nonempty_NW_cells\":%" PRIu64 ",\n"
        " \"wall_seconds\":%.9f,\n \"user_cpu_seconds\":%.6f,\n \"system_cpu_seconds\":%.6f,\n \"cpu_seconds\":%.6f,\n"
        " \"wait4_peak_rss_bytes\":%ld,\n \"sampled_peak_rss_bytes\":%" PRIu64 ",\n \"rss_samples\":%u,\n \"rss_sampling_interval_ms\":100,\n"
        " \"rss_watchdog_ceiling_bytes\":1073741824,\n \"rss_watchdog_is_hard_address_space_cap\":false,\n \"cpu_soft_limit_seconds\":1200,\n \"cpu_hard_limit_seconds\":1200,\n"
        " \"effective_wall_limit_seconds\":%.9f,\n \"workspace_bytes\":%zu,\n \"fixed_shared_mapping_bytes\":4096,\n \"combined_application_storage_bound_bytes\":131072,\n"
        " \"candidate_r\":%u,\n \"candidate_c\":%u,\n \"candidate_input_rank\":%u,\n \"candidate_output_rank\":%u\n}\n",
        stop_reason,atomic_load(&shared->outcome),status,WIFEXITED(status)?WEXITSTATUS(status):-1,
        WIFSIGNALED(status)?WTERMSIG(status):0,permission?"true":"false",atomic_load(&shared->controls),
        atomic_load(&shared->scan_started)?"true":"false",expected_inputs,atomic_load(&shared->begun),
        atomic_load(&shared->executed),atomic_load(&shared->passed),atomic_load(&shared->cells),
        (double)(end-start)/1e9,user_cpu,system_cpu,user_cpu+system_cpu,usage.ru_maxrss,sampled_peak,samples,
        (double)duration/1e9,sizeof work,shared->bad_r,shared->bad_c,shared->input_rank,shared->output_rank);
    if(length<0 || (size_t)length>=sizeof json || !write_all(evidence_fd,json,(size_t)length) || fsync(evidence_fd)<0) {
        emit("BOUNDARY terminal evidence write errno=%d\n",errno); return 70;
    }
    close(evidence_fd); close(ready_pipe[0]); close(queue); close(dir_fd);
    munmap(shared,SHARED_BYTES); close(log_fd);
    return killed?124:WIFEXITED(status)?WEXITSTATUS(status):128+WTERMSIG(status);
}
