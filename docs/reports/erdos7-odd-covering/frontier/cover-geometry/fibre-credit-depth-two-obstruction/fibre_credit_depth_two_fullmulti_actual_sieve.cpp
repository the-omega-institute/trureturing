// Literal numerical certificate checker for Report756.
// Sieve every actual original on Z/LZ, then fold by numerical divisors.
// The declared carrier bounds every integer count below 2^32.
// The consumer validates the complete divisor/query inventory and compiles
// with UBSan. No phase generation, row-tensor model or solver is used here.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <vector>
using U=std::uint64_t;
void need(bool p,const char*s){if(!p)throw std::runtime_error(s);}
std::map<U,U> expected;
const int primes[8]={3,5,7,11,13,17,19,23};
U total=0,checked=0,divisors=0;
template<class T>void fold(const std::vector<T>&a,int start){
 U n=a.size(),sum=0,cap=0;for(T v:a){sum+=v;cap=std::max(cap,U(v));}
 need(sum==total,"mass conserved by numerical residue folding");++divisors;
 auto at=expected.find(n);if(at!=expected.end()){need(cap==at->second,"independent exact maximum agrees");++checked;}
 for(int i=start;i<8;++i)if(n%primes[i]==0){U m=n/primes[i];std::vector<std::uint32_t>b(m,0);for(int k=0;k<primes[i];++k)for(U x=0;x<m;++x)b[x]+=a[x+k*m];fold(b,i);}
}
int main(int argc,char**argv){try{need(argc==3,"usage input output");std::ifstream in(argv[1]);U L,M,R;in>>L>>M>>R;need(L==334639305&&R==383,"actual carrier and 383 originals");std::vector<std::uint8_t>a(L,1);std::map<U,U>rules;for(U i=0;i<R;++i){U m,r;in>>m>>r;need(m>1&&m%2==1&&L%m==0&&r<m,"legal numerical class");need(rules.emplace(m,r).second,"distinct numerical moduli");for(U x=r;x<L;x+=m)a[x]=0;}U count;in>>count;need(count==320,"320 nonzero query slots");for(U i=0;i<count;++i){U m,cap;in>>m>>cap;need(expected.emplace(m,cap).second,"distinct numerical query");}need(bool(in),"complete input");for(auto v:a)total+=v;need(total==M,"literal numerical CRT sieve mass");std::cerr<<"numerical sieve count "<<total<<"; folding all 384 numerical divisors\n";fold(a,0);need(divisors==384&&checked==320,"complete independent query inventory");std::ofstream out(argv[2]);out<<"{\"passed\":true,\"carrier\":"<<L<<",\"originals\":383,\"survivor_count\":"<<total<<",\"numerical_divisors\":384,\"exact_query_maxima\":320,\"method\":\"literal numerical progression sieve, then exact residue folding\",\"lean_verification\":false}\n";need(bool(out),"output");}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
