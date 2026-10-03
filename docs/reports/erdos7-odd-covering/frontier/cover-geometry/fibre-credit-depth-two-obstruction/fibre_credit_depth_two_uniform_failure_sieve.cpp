// Numerical negative certificate for the uniform full actual source.
// Reads only literal numerical classes and60 fixed queries; no optimizer.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using U=std::uint64_t;
void need(bool b,const char*s){if(!b)throw std::runtime_error(s);}
int main(int argc,char**argv){try{
 need(argc==3,"usage literal-rules result");constexpr U L=334639305;std::ifstream in(argv[1]);int nr;in>>nr;need(nr==383,"383 originals");std::vector<std::uint8_t>live(L,1);std::set<U>moduli;
 for(int j=0;j<nr;++j){U m,a;in>>m>>a;need(m>1&&m%2==1&&L%m==0&&a<m&&moduli.insert(m).second,"actual legal distinct divisor");for(U x=a;x<L;x+=m)live[x]=0;}need(bool(in),"literal phase table");
 const int d[10]={5,7,9,15,21,35,45,63,105,315};const int phase[10]={2,5,7,2,5,2,7,25,2,2};const int w[10]={12,8,24,12,8,22,42,36,22,57};const int p[5]={11,13,17,19,23};U score[315]={};for(int x=0;x<315;++x)for(int j=0;j<10;++j)if(x%d[j]==phase[j])score[x]+=w[j];
 U mass=0,old=0,single=0;for(U x=0;x<L;++x)if(live[x]){++mass;U s=score[x%315];old+=s;for(int prime:p)if(x%prime==1)single+=s;}
 need(mass==27336206&&old==1003836400&&single==381077191,"literal selected-cylinder exact certificate");std::int64_t upper=std::int64_t(48*mass)-std::int64_t(old)-std::int64_t(single);need(upper==-72775703&&upper<0,"strict negative uniform-source upper bound");
 std::ofstream out(argv[2]);out<<"{\"passed\":true,\"carrier\":"<<L<<",\"actual_original_count\":383,\"actual_full_survivor_count\":"<<mass<<",\"selected_query_count\":60,\"selected_old_debit48\":"<<old<<",\"selected_singleton_debit48\":"<<single<<",\"uniform_J_upper48\":"<<upper<<",\"method\":\"literal numerical sieve and 60 fixed-cylinder lower bounds; no query maximization\",\"lean_verification\":false}\n";need(bool(out),"result");
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
