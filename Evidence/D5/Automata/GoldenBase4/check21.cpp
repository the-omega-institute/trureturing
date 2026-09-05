// Exact checker for the fixed 21-state interval certificate.
// Build: g++ -O2 -std=c++17 -Wall -Wextra -Werror check21.cpp -o check21
// Run: ./check21 machine21.tsv
// Coordinates (a,b) denote (a+b*phi)/4. No floating-point operations.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

struct P { long long a,b; };
int sign(P p) {
    const long long u=2*p.a+p.b,v=p.b;
    if(!v) return (u>0)-(u<0);
    if(!u) return (v>0)-(v<0);
    if(u>0 && v>0) return 1;
    if(u<0 && v<0) return -1;
    const __int128 d=static_cast<__int128>(u)*u-5*static_cast<__int128>(v)*v;
    return ((d>0)-(d<0))*(u>0?1:-1);
}
int cmp(P p,P q) { return sign({p.a-q.a,p.b-q.b}); }
P image(P p,int d) { return {p.a-p.b-8*d,-p.a+4*d}; }
struct S {char type;int out,z,o;P lo,hi;bool point;};
void require(bool p,const std::string& m){if(!p)throw std::runtime_error(m);}
bool inside(P p,const S& s){return s.point?cmp(p,s.lo)==0:cmp(s.lo,p)<0&&cmp(p,s.hi)<0;}
int next(const std::vector<S>& m,int q,int d){return q<0?-1:(d?m[q].o:m[q].z);}
int run(const std::vector<S>& m,const std::string& w){int q=0;for(char c:w)q=next(m,q,c-'0');return q<0?-1:m[q].out;}
unsigned long long value(const std::string& w){
    unsigned long long q=0,v=0;
    for(char c:w){unsigned long long d=c-'0',nq=v+d;v=q+v+2*d;q=nq;}
    return q;
}
unsigned long long isqrt128(unsigned __int128 n){
    unsigned __int128 x=0,bit=static_cast<unsigned __int128>(1)<<126;
    while(bit>n)bit>>=2;
    while(bit){if(n>=x+bit){n-=x+bit;x=(x>>1)+bit;}else x>>=1;bit>>=2;}
    return static_cast<unsigned long long>(x);
}
unsigned long long floorphi(unsigned long long q){return(q+isqrt128(5*static_cast<unsigned __int128>(q)*q))/2;}
int digit(unsigned long long q){return static_cast<int>(floorphi(4*q)-4*floorphi(q));}
std::string distinguishing(const std::vector<S>& m,int p,int q){
    std::queue<std::tuple<int,int,std::string>> todo;
    bool seen[22][22]{};todo.emplace(p,q,"");seen[p+1][q+1]=true;
    while(!todo.empty()){
        auto [a,b,w]=todo.front();todo.pop();
        if((a<0?-1:m[a].out)!=(b<0?-1:m[b].out))return w;
        for(int d=0;d<2;++d){
            int aa=next(m,a,d),bb=next(m,b,d);
            if(!seen[aa+1][bb+1]){seen[aa+1][bb+1]=true;todo.emplace(aa,bb,w+char('0'+d));}
        }
    }
    return "!";
}
int main(int argc,char**argv){try{
    require(argc==2,"Usage: check21 machine21.tsv");
    std::ifstream f(argv[1]);require(static_cast<bool>(f),"Cannot open certificate");
    std::vector<S> m;int id,pt;S s{};
    while(f>>id>>s.type>>s.out>>s.z>>s.o>>s.lo.a>>s.lo.b>>s.hi.a>>s.hi.b>>pt){
        require(id==static_cast<int>(m.size()),"State order mismatch");s.point=pt;m.push_back(s);
    }
    require(m.size()==21,"Wrong state count");
    require(m[0].point&&cmp(m[0].lo,{0,0})==0&&cmp(m[0].hi,{0,0})==0,"Start point mismatch");
    require(m[0].type=='R'&&m[0].z==0&&m[0].out==0,"Start anchors fail");
    require(cmp(m[1].lo,{12,-8})==0&&cmp(m[13].hi,{8,-4})==0,"R domain mismatch");
    require(cmp(m[14].lo,{4,-4})==0&&cmp(m[20].hi,{12,-8})==0,"T domain mismatch");
    int transitions=0,excluded=0;
    for(int i=0;i<21;++i){
        const S& c=m[i];require(c.point==(i==0),"Unexpected singleton cell");require(c.type==(i<14?'R':'T'),"Wrong type");
        require(0<=c.out&&c.out<4,"Output range");
        if(!c.point){
            require(cmp(c.lo,c.hi)<0,"Empty cell");
            if(i!=1&&i!=14){
                require(cmp(m[i-1].hi,c.lo)==0,"Gap between cells");
                if(cmp(c.lo,{0,0})!=0){require(c.lo.a%4||c.lo.b%4,"Attainable artificial cut");++excluded;}
            }
            int k=c.out-(cmp(c.hi,{0,0})<=0?4:0);
            require(cmp({k,0},c.lo)<=0&&cmp(c.hi,{k+1,0})<=0,"Nonconstant output cell");
        }
        for(int d=0;d<2;++d){
            const int j=next(m,i,d);
            if(c.type=='T'&&d==1){require(j==-1,"Invalid 11 transition allowed");continue;}
            require(0<=j&&j<21,"Missing legal transition");const S& dest=m[j];
            require(dest.type==(d?'T':'R'),"Destination type mismatch");
            if(c.point)require(inside(image(c.lo,d),dest),"Point transition fails");
            else{
                require(!dest.point,"Interval sent to point");
                P lo=image(c.hi,d),hi=image(c.lo,d);
                require(cmp(dest.lo,lo)<=0&&cmp(lo,hi)<0&&cmp(hi,dest.hi)<=0,"Interval transition fails");
            }
            ++transitions;
        }
    }
    std::array<std::string,21> access;access.fill("!");access[0]="";
    std::queue<int> todo;todo.push(0);
    while(!todo.empty()){
        int q=todo.front();todo.pop();
        for(int d=0;d<2;++d){int k=next(m,q,d);if(k>=0&&access[k]=="!"){access[k]=access[q]+char('0'+d);todo.push(k);}}
    }
    int pairs=0,same=0;std::size_t longest=0;
    for(int i=0;i<21;++i){
        require(access[i]!="!","Unreachable state");require(run(m,access[i])==digit(value(access[i])),"Access output mismatch");
        for(int j=i+1;j<21;++j){
            auto w=distinguishing(m,i,j);require(w!="!","Equivalent state pair");++pairs;
            if(m[i].type==m[j].type){
                auto u=access[i]+w,v=access[j]+w;
                require(u.find("11")==std::string::npos&&v.find("11")==std::string::npos,"Illegal same-type witness");
                require(run(m,u)==digit(value(u))&&run(m,v)==digit(value(v)),"Witness oracle mismatch");
                require(digit(value(u))!=digit(value(v)),"Witness not distinguishing");
                ++same;longest=std::max(longest,std::max(u.size(),v.size()));
            }
        }
    }
    std::cout<<"{\"status\":\"PASS\",\"states\":21,\"exact_transitions\":"<<transitions
             <<",\"unattainable_nonzero_cuts\":"<<excluded<<",\"all_pair_witnesses\":"<<pairs
             <<",\"same_type_oracle_witnesses\":"<<same<<",\"max_witness_input_length\":"<<longest
             <<",\"lean_kernel_checked\":false}\n";
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
