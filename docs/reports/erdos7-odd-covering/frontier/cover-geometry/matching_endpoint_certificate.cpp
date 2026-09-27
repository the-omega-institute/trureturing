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
using i64=std::int64_t; using i128=__int128_t;
static constexpr int NC=80, NT=5320, NP=317920, NE=10;
static constexpr int W[6]={81,81,81,81,41,0};
static constexpr int REF[4]={12,12,15,12};
static constexpr int EQ[10]={0,0,0,0,1,1,1,2,2,3};
static constexpr int ER[10]={1,2,3,4,2,3,4,3,4,4};
struct Edge {std::array<i64,256> mass;std::array<i64,8192> query;};
struct Input {
 std::array<std::array<std::uint8_t,2>,80> cells;
 std::array<std::array<std::uint8_t,6>,5320> templates;
 std::array<std::array<std::uint8_t,80>,5320> codes;
 std::vector<std::array<std::uint16_t,2>> pairs;
 std::array<i64,512> clo,chi; i64 glo,ghi,hs,cs;
 std::array<Edge,10> edges;
};
static Input in;
struct Output {std::array<i128,16> table;std::array<std::array<int,2>,16> arg; i128 minimum; std::int64_t cases;};
static std::array<Output,10> out;
static std::atomic<int> nextedge{0};
static std::string dec(i128 n){if(n==0)return "0";bool neg=n<0;if(neg)n=-n;std::string s;while(n){s.push_back(char('0'+n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
template<class T>static void readraw(std::ifstream& f,T& x){f.read(reinterpret_cast<char*>(&x),sizeof(x));if(!f)throw std::runtime_error("truncated input");}
static void readinput(const char* path){
 if(std::endian::native!=std::endian::little)throw std::runtime_error("requires little endian input reader");
 std::ifstream f(path,std::ios::binary);std::array<char,16> magic;readraw(f,magic);
 if(std::string(magic.data(),14)!="E7MATCHPAIRIV1")throw std::runtime_error("wrong schema");
 std::array<std::uint32_t,7> count;readraw(f,count);
 if(count!=std::array<std::uint32_t,7>{80,5320,317920,10,16,32,58400})throw std::runtime_error("wrong dimensions");
 readraw(f,in.hs);readraw(f,in.cs);readraw(f,in.glo);readraw(f,in.ghi);
 readraw(f,in.cells);readraw(f,in.templates);readraw(f,in.codes);
 in.pairs.resize(NP);f.read(reinterpret_cast<char*>(in.pairs.data()),NP*sizeof(in.pairs[0]));if(!f)throw std::runtime_error("truncated pairs");
 readraw(f,in.clo);readraw(f,in.chi);readraw(f,in.edges);
 char extra;if(f.read(&extra,1))throw std::runtime_error("trailing data");
 for(auto c:in.cells)if(c[0]>=6||c[1]>=20)throw std::runtime_error("cell out of range");
 for(auto p:in.pairs)if(p[0]>=NT||p[1]>=NT)throw std::runtime_error("pair index out of range");
 for(auto a:in.codes)for(auto c:a)if(c>=16)throw std::runtime_error("state out of range");
 // Every precomputed grid interval is in [-2,2]; this bounds all i64 screen arithmetic.
 for(const auto& e:in.edges){for(auto z:e.mass)if(z < -2*in.hs || z>2*in.hs)throw std::runtime_error("mass range");for(auto z:e.query)if(z < -2*in.hs || z>2*in.hs)throw std::runtime_error("query range");}
}
// All four quantities have quinary denominator 80 (first three) or16 (last).
static inline std::array<i64,4> quinary(const i64* y){
 std::array<i64,4> z{0,std::numeric_limits<i64>::min(),std::numeric_limits<i64>::min(),std::numeric_limits<i64>::min()};
 for(int j=0;j<4;j++){i64 block=0;for(int s=0;s<5;s++){int m=5*j+s;int v=m==10?0:(j==2?5:4);i64 a=v*y[m];block+=a;z[2]=std::max(z[2],a);z[3]=std::max(z[3],i64(REF[j])*y[m]);}z[0]+=block;z[1]=std::max(z[1],block);}return z;
}
static inline std::array<i64,16> screens(const i64 h[6][20]){
 std::array<i64,16> s{};i64 roots[2][20]{};i64 total[20]{};
 // The sixth zero leaf is retained, so maxima for leaf selectors start at zero.
 for(int l=0;l<5;l++){
  auto v=quinary(h[l]);for(int e=0;e<4;e++){s[8+e]=std::max(s[8+e],i64(W[l])*v[e]);s[12+e]=std::max(s[12+e],i64(729)*v[e]);}
  for(int m=0;m<20;m++)roots[l/3][m]+=i64(W[l])*h[l][m];
 }
 for(int m=0;m<20;m++)total[m]=roots[0][m]+roots[1][m];
 auto v0=quinary(total);auto v1=quinary(roots[0]);auto v2=quinary(roots[1]);
 for(int e=0;e<4;e++){s[e]=v0[e];s[4+e]=std::max(v1[e],v2[e]);}
 // Lift every central screen to the common denominator58400.
 for(int mode=0;mode<16;mode++){int e3=mode/4,e5=mode%4;s[mode]*=e5==3?(e3==3?5:10):(e3==3?1:2);}return s;
}
static i128 evaluate(const Edge& e,int ti,int tj){
 std::array<std::uint8_t,80> state; i64 mass=0;
 for(int c=0;c<80;c++){state[c]=std::uint8_t(16*in.codes[ti][c]+in.codes[tj][c]);int l=in.cells[c][0],m=in.cells[c][1];int v=m==10?0:(m/5==2?5:4);mass+=i64(2*W[l]*v)*e.mass[state[c]];}
 i128 value=i128(mass)*(mass>=0?in.glo:in.ghi);
 for(int T=0;T<32;T++){
  i64 h[6][20]{};for(int c=0;c<80;c++)h[in.cells[c][0]][in.cells[c][1]]=e.query[256*T+state[c]];
  auto sc=screens(h);for(int mode=0;mode<16;mode++){int j=32*mode+T;i64 cf=sc[mode]>=0?in.chi[j]:in.clo[j];value-=i128(sc[mode])*cf;}
 }return value;
}
static int sw(int c){return c==1?3:(c==3?1:c);}
static void runedge(int e){
 auto start=std::chrono::steady_clock::now();auto& o=out[e];o.table.fill(i128(1)<<120);o.cases=0;
 for(auto pp:in.pairs){int i=pp[0],j=pp[1];i128 value=evaluate(in.edges[e],i,j);int c=in.templates[i][1],d=in.templates[j][1];for(int pos:{4*c+d,4*sw(c)+sw(d)})if(value<o.table[pos]){o.table[pos]=value;o.arg[pos]={i,j};}o.cases++;}
 o.minimum=*std::min_element(o.table.begin(),o.table.end());for(auto x:o.table)if(x==(i128(1)<<120))throw std::runtime_error("uncovered column pair");
 auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count();
 std::cerr<<"edge "<<e<<" complete "<<ms<<" ms\n";
}
int main(int argc,char**argv){try{
 if(argc<2)throw std::runtime_error("usage: verifier input.bin [threads]");readinput(argv[1]);int threads=argc>2?std::stoi(argv[2]):2;if(threads<1||threads>10)throw std::runtime_error("threads");
 std::vector<std::thread> workers;for(int k=0;k<threads;k++)workers.emplace_back([]{while(true){int e=nextedge.fetch_add(1);if(e>=10)break;runedge(e);}});for(auto& th:workers)th.join();
 i128 best=i128(1)<<120,independent=0;std::array<int,5> arg{};for(auto& o:out)independent+=o.minimum;
 for(int code=0;code<1024;code++){int z=code;std::array<int,5> cs;for(int q=0;q<5;q++){cs[q]=z%4;z/=4;}i128 v=0;for(int e=0;e<10;e++)v+=out[e].table[4*cs[EQ[e]]+cs[ER[e]]];if(v<best){best=v;arg=cs;}}
 i128 den=i128(58400)*in.hs*in.cs;if(1000*best<=7*den)throw std::runtime_error("strict gate 7/1000 failed");
 std::cout<<"{\"schema\":\"matching-endpoint-all-star-fixedpoint-v1\",\"denominator\":\""<<dec(den)<<"\",\"gate_lower_numerator\":\""<<dec(best)<<"\",\"independent_edge_lower_numerator\":\""<<dec(independent)<<"\",\"columns\":[";
 for(int q=0;q<5;q++){if(q)std::cout<<',';std::cout<<arg[q];}std::cout<<"],\"joint_column_assignments\":1024,\"pair_orbit_evaluations\":3179200,\"tables\":[";
 for(int e=0;e<10;e++){if(e)std::cout<<',';std::cout<<"{\"edge\":["<<EQ[e]<<','<<ER[e]<<"],\"costs\":[";for(int k=0;k<16;k++){if(k)std::cout<<',';std::cout<<'"'<<dec(out[e].table[k])<<'"';}std::cout<<"],\"argmin_template_ids\":[";for(int k=0;k<16;k++){if(k)std::cout<<',';std::cout<<'['<<out[e].arg[k][0]<<','<<out[e].arg[k][1]<<']';}std::cout<<"]}";}
 std::cout<<"],\"strict_target\":\"7/1000\",\"passed\":true}\n";return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
