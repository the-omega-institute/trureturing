#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <thread>
#include <vector>
#include <chrono>
#include <stdexcept>
using i64=std::int64_t; using i128=__int128_t;
static constexpr int NT=5320, NE=10;
static constexpr int EQ[10]={0,0,0,0,1,1,1,2,2,3};
static constexpr int ER[10]={1,2,3,4,2,3,4,3,4,4};
struct Edge {std::array<i64,256> mass;std::array<i64,8192> query;};
struct Input {
 int nc,np;
 std::array<std::uint8_t,6> w;std::array<std::uint8_t,20> v;
 std::vector<std::array<std::uint8_t,2>> cells;
 std::array<std::array<std::uint8_t,6>,NT> templates;
 std::vector<std::uint8_t> codes;
 std::vector<std::array<std::uint16_t,3>> pairs;
 std::array<i64,512> clo,chi; i64 glo,ghi,hs,cs;
 std::array<Edge,10> edges;
};
static Input in;
struct Output {std::array<i128,16> table;std::array<std::array<int,2>,16> arg; i128 minimum;std::int64_t cases;};
static std::array<Output,NE> out;static std::atomic<int> nextedge{0};
static std::string dec(i128 n){if(n==0)return"0";bool neg=n<0;if(neg)n=-n;std::string s;while(n){s.push_back(char('0'+n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
template<class T>static void readraw(std::ifstream&f,T&x){f.read(reinterpret_cast<char*>(&x),sizeof(x));if(!f)throw std::runtime_error("truncated input");}
template<class T>static void readvec(std::ifstream&f,std::vector<T>&v){f.read(reinterpret_cast<char*>(v.data()),v.size()*sizeof(T));if(!f)throw std::runtime_error("truncated vector");}
static void readinput(const char*path){
 if(std::endian::native!=std::endian::little)throw std::runtime_error("little endian reader");
 std::ifstream f(path,std::ios::binary);std::array<char,16> magic;readraw(f,magic);
 if(std::string(magic.data())!="E7PURE20INTV1")throw std::runtime_error("wrong schema");
 std::array<std::uint32_t,7> count;readraw(f,count);
 if(count[0]<80||count[0]>87||count[1]!=NT||count[3]!=NE||count[4]!=16||count[5]!=32||count[6]!=675)throw std::runtime_error("wrong dimensions");
 in.nc=count[0];in.np=count[2];if(in.np<=0||in.np>NT*NT)throw std::runtime_error("pair count");
 readraw(f,in.hs);readraw(f,in.cs);readraw(f,in.glo);readraw(f,in.ghi);readraw(f,in.w);readraw(f,in.v);
 if(in.hs<=0||in.hs>(1LL<<30)||in.cs<=0||in.cs>(1LL<<30))throw std::runtime_error("scale");
 in.cells.resize(in.nc);readvec(f,in.cells);readraw(f,in.templates);in.codes.resize(NT*in.nc);readvec(f,in.codes);
 in.pairs.resize(in.np);readvec(f,in.pairs);readraw(f,in.clo);readraw(f,in.chi);readraw(f,in.edges);
 char extra;if(f.read(&extra,1))throw std::runtime_error("trailing data");
 int sw=0,sv=0;for(auto w:in.w){if(w>2)throw std::runtime_error("ternary weight");sw+=w;}for(auto v:in.v){if(v>4)throw std::runtime_error("quinary weight");sv+=v;}if(sw!=9||sv!=75)throw std::runtime_error("source mass");
 for(auto c:in.cells)if(c[0]>=6||c[1]>=20||!in.w[c[0]]||!in.v[c[1]]||(c[0]/3==0&&c[1]/5==0))throw std::runtime_error("cell");
 for(auto p:in.pairs)if(p[0]>=NT||p[1]>=NT||p[2]==0)throw std::runtime_error("pair");
 for(auto c:in.codes)if(c>=16)throw std::runtime_error("state");
 if(in.glo<0||in.glo>in.ghi||in.ghi>in.cs)throw std::runtime_error("gain bounds");
 i128 coeffsum=in.ghi;
 for(int j=0;j<512;j++){
  if(in.clo[j]<0||in.clo[j]>in.chi[j])throw std::runtime_error("coefficient bounds");
  coeffsum+=in.chi[j];
 }
 // Every actual central selector has total mass at most one. The integer
 // screen has denominator675, including the constant deep factors9,60.
 // Enforce bounds before any signed64 screen or signed128 budget is used.
 i128 screen_bound=i128(2)*in.hs*675;
 i128 budget_unit=i128(10000)*10*screen_bound;
 if(screen_bound>=i128(std::numeric_limits<i64>::max())||
    coeffsum>((i128(1)<<120)-1)/budget_unit)
   throw std::runtime_error("integer overflow bound");
 for(const auto&e:in.edges){for(auto z:e.mass)if(z < -2*in.hs||z>2*in.hs)throw std::runtime_error("mass interval");for(auto z:e.query)if(z < -2*in.hs||z>2*in.hs)throw std::runtime_error("query interval");}
}
// All source selectors use a common denominator75; deep mass4/5 has numerator60.
static inline std::array<i64,4> quinary(const i64*y){
 std::array<i64,4>z{};
 for(int j=0;j<4;j++){i64 block=0;for(int s=0;s<5;s++){int m=5*j+s;if(!in.v[m])continue;i64 a=i64(in.v[m])*y[m];block+=a;z[2]=std::max(z[2],a);z[3]=std::max(z[3],60*y[m]);}z[0]+=block;z[1]=std::max(z[1],block);}return z;
}
static inline std::array<i64,16> screens(const i64 h[6][20]){
 std::array<i64,16>s{};i64 roots[2][20]{},total[20]{};
 for(int l=0;l<6;l++){if(!in.w[l])continue;auto v=quinary(h[l]);for(int e=0;e<4;e++){s[8+e]=std::max(s[8+e],i64(in.w[l])*v[e]);s[12+e]=std::max(s[12+e],9*v[e]);}for(int m=0;m<20;m++)roots[l/3][m]+=i64(in.w[l])*h[l][m];}
 for(int m=0;m<20;m++)total[m]=roots[0][m]+roots[1][m];
 auto v0=quinary(total),v1=quinary(roots[0]),v2=quinary(roots[1]);
 for(int e=0;e<4;e++){s[e]=v0[e];s[4+e]=std::max(i64(0),std::max(v1[e],v2[e]));}return s;
}
static i128 evaluate(const Edge&e,int ti,int tj){
 std::array<std::uint8_t,120>state{};i64 mass=0;
 for(int c=0;c<in.nc;c++){state[c]=std::uint8_t(16*in.codes[ti*in.nc+c]+in.codes[tj*in.nc+c]);int l=in.cells[c][0],m=in.cells[c][1];mass+=i64(in.w[l]*in.v[m])*e.mass[state[c]];}
 i128 value=i128(mass)*(mass>=0?in.glo:in.ghi);
 for(int T=0;T<32;T++){i64 h[6][20]{};for(int c=0;c<in.nc;c++)h[in.cells[c][0]][in.cells[c][1]]=e.query[256*T+state[c]];auto sc=screens(h);for(int mode=0;mode<16;mode++){int j=32*mode+T;value-=i128(sc[mode])*(sc[mode]>=0?in.chi[j]:in.clo[j]);}}return value;
}
static void runedge(int e){
 auto start=std::chrono::steady_clock::now();auto&o=out[e];o.table.fill(i128(1)<<120);o.cases=0;
 for(auto pp:in.pairs){i128 value=evaluate(in.edges[e],pp[0],pp[1]);for(int pos=0;pos<16;pos++)if((pp[2]>>pos)&1)if(value<o.table[pos]){o.table[pos]=value;o.arg[pos]={pp[0],pp[1]};}o.cases++;}
 o.minimum=*std::min_element(o.table.begin(),o.table.end());for(auto x:o.table)if(x==(i128(1)<<120))throw std::runtime_error("uncovered columns");
 std::cerr<<"edge "<<e<<" complete "<<std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count()<<" ms\n";
}
int main(int argc,char**argv){try{
 if(argc<2)throw std::runtime_error("usage: verifier input.bin [threads]");readinput(argv[1]);int threads=argc>2?std::stoi(argv[2]):2;if(threads<1||threads>10)throw std::runtime_error("threads");
 std::vector<std::thread>workers;for(int k=0;k<threads;k++)workers.emplace_back([]{while(true){int e=nextedge.fetch_add(1);if(e>=NE)break;runedge(e);}});for(auto&th:workers)th.join();
 i128 best=i128(1)<<120,independent=0;std::array<int,5>arg{};for(auto&o:out)independent+=o.minimum;
 for(int code=0;code<1024;code++){int z=code;std::array<int,5>cs;for(int q=0;q<5;q++){cs[q]=z%4;z/=4;}i128 v=0;for(int e=0;e<NE;e++)v+=out[e].table[4*cs[EQ[e]]+cs[ER[e]]];if(v<best){best=v;arg=cs;}}
 i128 den=i128(675)*in.hs*in.cs;
 std::cout<<"{\"schema\":\"pure-source-signed-pair-exact-v1\",\"denominator\":\""<<dec(den)<<"\",\"gate_lower_numerator\":\""<<dec(best)<<"\",\"independent_edge_lower_numerator\":\""<<dec(independent)<<"\",\"columns\":[";
 for(int q=0;q<5;q++){if(q)std::cout<<',';std::cout<<arg[q];}std::cout<<"],\"joint_column_assignments\":1024,\"pair_orbit_evaluations\":"<<10LL*in.np<<",\"tables\":[";
 for(int e=0;e<NE;e++){if(e)std::cout<<',';std::cout<<"{\"edge\":["<<EQ[e]<<','<<ER[e]<<"],\"costs\":[";for(int k=0;k<16;k++){if(k)std::cout<<',';std::cout<<'"'<<dec(out[e].table[k])<<'"';}std::cout<<"],\"argmin_template_ids\":[";for(int k=0;k<16;k++){if(k)std::cout<<',';std::cout<<'['<<out[e].arg[k][0]<<','<<out[e].arg[k][1]<<']';}std::cout<<"]}";}std::cout<<"],\"positive\":"<<(best>0?"true":"false")<<"}\n";return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
