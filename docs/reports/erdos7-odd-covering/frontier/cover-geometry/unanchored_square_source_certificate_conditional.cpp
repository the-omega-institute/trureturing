#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
using i64=std::int64_t;using i128=__int128_t;
static constexpr int NC=80,NT=95;
static int cell_l[NC],cell_m[NC],rootcell[NC],choice_l[NT],choice_m[NT],paircode[NT*NT][NC];
static i64 weights3[6],weights5[20],clo[512],chi[512],glo,ghi,hs,cs;
static std::string dec(i128 n){if(!n)return"0";bool neg=n<0;if(neg)n=-n;std::string s;while(n){s.push_back(char('0'+n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
template<class T>static void read(std::ifstream&f,T&x){f.read(reinterpret_cast<char*>(&x),sizeof(x));if(!f)throw std::runtime_error("truncated input");}
static void initialize(const std::array<std::uint8_t,4>&source){
 if(source[0]!=3||source[1]!=4||source[2]!=5||(source[3]!=6&&source[3]!=10))throw std::runtime_error("supported case12/14 source");
 for(int l=0;l<6;l++)weights3[l]=l==3?0:l==source[1]?1:2;for(int m=0;m<20;m++)weights5[m]=m==5?0:m==source[3]?3:4;
 int c=0;for(int l=0;l<6;l++)for(int m=0;m<20;m++)if(l!=3&&m!=5&&!(l/3==0&&m/5==0)){cell_l[c]=l;cell_m[c]=m;rootcell[c]=4*(l/3)+m/5;c++;}if(c!=NC)throw std::runtime_error("cells");
 int t=0;for(int l=0;l<6;l++)for(int m=0;m<20;m++)if(l!=3&&m!=5){choice_l[t]=l;choice_m[t]=m;t++;}if(t!=NT)throw std::runtime_error("templates");
 for(int i=0;i<NT;i++)for(int j=0;j<NT;j++)for(int c=0;c<NC;c++)paircode[NT*i+j][c]=3*((cell_l[c]==choice_l[i])+(cell_m[c]==choice_m[i]))+(cell_l[c]==choice_l[j])+(cell_m[c]==choice_m[j]);
}
static std::array<i64,4> quinary(const i64*h){
 std::array<i64,4>out{};for(int j=0;j<4;j++){i64 root=0;for(int k=0;k<5;k++){int m=5*j+k;if(!weights5[m])continue;i64 x=weights5[m]*h[m];root+=x;out[2]=std::max(out[2],x);out[3]=std::max(out[3],60*h[m]);}out[0]+=root;out[1]=std::max(out[1],root);}return out;
}
static std::array<i64,16> screens(const i64 h[6][20]){
 std::array<i64,16>out{};i64 roots[2][20]{},total[20]{};
 for(int l=0;l<6;l++)if(weights3[l]){auto v=quinary(h[l]);for(int e=0;e<4;e++){out[8+e]=std::max(out[8+e],weights3[l]*v[e]);out[12+e]=std::max(out[12+e],9*v[e]);}for(int m=0;m<20;m++)roots[l/3][m]+=weights3[l]*h[l][m];}
 for(int m=0;m<20;m++)total[m]=roots[0][m]+roots[1][m];auto v=quinary(total),a=quinary(roots[0]),b=quinary(roots[1]);for(int e=0;e<4;e++){out[e]=v[e];out[4+e]=std::max(i64(0),std::max(a[e],b[e]));}return out;
}
struct Interval {i64 mass[720],query[23040];};
int main(int argc,char**argv){try{
 if(argc!=2||std::endian::native!=std::endian::little)throw std::runtime_error("usage / little endian");std::ifstream f(argv[1],std::ios::binary);std::array<char,16>magic;read(f,magic);if(std::string(magic.data())!="E7CONDTAILBOX1")throw std::runtime_error("schema");
 std::uint32_t count;read(f,count);if(count==0||count>1000)throw std::runtime_error("count");std::array<std::uint8_t,4>source;read(f,source);read(f,hs);read(f,cs);read(f,glo);read(f,ghi);if(hs!=(1LL<<23)||cs!=(1LL<<27))throw std::runtime_error("fixed certificate scales");read(f,clo);read(f,chi);initialize(source);
 if(!(0<=glo&&glo<=ghi&&ghi<=cs))throw std::runtime_error("gain interval");i128 sumchi=0;for(int j=0;j<512;j++){if(clo[j]<0||chi[j]<clo[j])throw std::runtime_error("coefficient interval");sumchi+=chi[j];}i128 screen=i128(675)*2*hs,budget=screen*(ghi+sumchi);if(screen>=(i128(1)<<63)||1000*10*budget>=(i128(1)<<120))throw std::runtime_error("integer overflow bound");
 std::cout<<"{\"denominator\":\""<<dec(i128(675)*hs*cs)<<"\",\"layouts\":[";
 i128 global=i128(1)<<120;
 for(unsigned k=0;k<count;k++){
  std::array<std::uint8_t,5>states;std::array<std::array<std::uint8_t,4>,5>roots;read(f,states);read(f,roots);
  for(int q=0;q<5;q++){auto x=roots[q];if(x[0]>1||x[1]>3||x[2]>1||x[3]>3||(x[2]==0&&x[3]==0))throw std::runtime_error("root role domain");int raw=2*(4*(2*x[0]+x[2])+x[1])+(x[3]==x[1]);if(raw==1||raw==17||states[q]!=raw-(raw>1)-(raw>17))throw std::runtime_error("root-to-boundary state mismatch");}
  Interval in;read(f,in);for(auto x:in.mass)if(x < -2*hs||x>2*hs)throw std::runtime_error("mass bound");for(auto x:in.query)if(x < -2*hs||x>2*hs)throw std::runtime_error("query bound");
  std::array<i128,10>lows;std::array<int,10>args;i128 total=0;
  for(int e=0;e<10;e++){
   i128 low=i128(1)<<120;int arg=-1;
   for(int ij=0;ij<NT*NT;ij++){
    i64 m=0;for(int c=0;c<NC;c++)m+=weights3[cell_l[c]]*weights5[cell_m[c]]*in.mass[72*e+9*rootcell[c]+paircode[ij][c]];i128 value=i128(m)*(m>=0?glo:ghi);
    for(int T=0;T<32;T++){i64 h[6][20]{};for(int c=0;c<NC;c++)h[cell_l[c]][cell_m[c]]=in.query[72*(32*e+T)+9*rootcell[c]+paircode[ij][c]];auto sc=screens(h);for(int mode=0;mode<16;mode++){int j=32*mode+T;value-=i128(sc[mode])*(sc[mode]>=0?chi[j]:clo[j]);}}
    if(value<low){low=value;arg=ij;}
   }
   lows[e]=low;args[e]=arg;total+=low;
  }
  global=std::min(global,total);if(k)std::cout<<',';std::cout<<"{\"shared_states\":[";for(int q=0;q<5;q++){if(q)std::cout<<',';std::cout<<int(states[q]);}std::cout<<"],\"roots\":[";for(int q=0;q<5;q++){if(q)std::cout<<',';std::cout<<'[';for(int j=0;j<4;j++){if(j)std::cout<<',';std::cout<<int(roots[q][j]);}std::cout<<']';}std::cout<<"],\"gate_numerator\":\""<<dec(total)<<"\",\"edges\":[";for(int e=0;e<10;e++){if(e)std::cout<<',';std::cout<<"{\"minimum\":\""<<dec(lows[e])<<"\",\"argmin\":["<<args[e]/NT<<','<<args[e]%NT<<"]}";}std::cout<<"]}";
 }
 char extra;if(f.read(&extra,1))throw std::runtime_error("trailing data");std::cout<<"],\"minimum_numerator\":\""<<dec(global)<<"\",\"positive\":"<<(global>0?"true":"false")<<",\"pair_evaluations\":"<<count*10*NT*NT<<"}\n";return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
