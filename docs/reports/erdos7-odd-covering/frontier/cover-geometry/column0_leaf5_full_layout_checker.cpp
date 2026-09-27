#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
using U=std::uint64_t; using S=std::int64_t; using W=__int128_t;
struct Vec { std::array<U,10> a; };
struct Case { std::array<std::vector<Vec>,16> menu; };
struct Family { U denominator; std::array<Case,20> cases; };
struct Result { int family=-1; S lower=std::numeric_limits<S>::min(); U screens=0,cases=0; };
U read_u64(std::istream& s){ U v=0;for(unsigned i=0;i<8;i++){int b=s.get();if(b<0)throw std::runtime_error("truncated integer input");v|=U(unsigned(b))<<(8*i);}return v; }
void write_u64(std::ostream& s,U v){for(unsigned i=0;i<8;i++)s.put(char((v>>(8*i))&255));}
S floor_q40(W numerator,U denominator){ W d=W(675)*denominator*(U(1)<<24);W q=numerator/d;if(numerator<0&&numerator%d!=0)--q;if(q<std::numeric_limits<S>::min()||q>std::numeric_limits<S>::max())throw std::runtime_error("q40 overflow");return S(q);}
int main(int argc,char**argv){try{
 if(argc<5)throw std::runtime_error("usage checker input.bin result.bin threads row [limit]");
 std::ifstream in(argv[1],std::ios::binary);if(!in)throw std::runtime_error("missing input");
 if(read_u64(in)!=0x314c4146454c5546ULL||read_u64(in)!=1)throw std::runtime_error("input schema");
 const U scale=read_u64(in),gL=read_u64(in),target=read_u64(in),expected=read_u64(in);
 if(scale!=(U(1)<<32)||gL>scale||expected!=1657470||target!=2122057442ULL)throw std::runtime_error("input constants");
 std::array<U,512>C;U sumC=0;for(auto&c:C){c=read_u64(in);if(c>7*scale)throw std::runtime_error("individual fee bound");sumC+=c;}if(sumC>7*scale)throw std::runtime_error("fee bound");
 constexpr std::size_t table_size=4*1024*32;std::vector<U>lo(table_size),hi(table_size);
 for(auto&v:lo){v=read_u64(in);if(v>scale)throw std::runtime_error("response lower bound");}
 for(std::size_t i=0;i<table_size;i++){hi[i]=read_u64(in);if(hi[i]>scale||lo[i]>hi[i])throw std::runtime_error("response interval");}
 std::array<Family,2>families;
 for(auto&f:families){f.denominator=read_u64(in);if(!f.denominator||f.denominator>(U(1)<<20))throw std::runtime_error("field denominator");
  for(auto&cs:f.cases)for(auto&menu:cs.menu){U n=read_u64(in);if(n<1||n>100)throw std::runtime_error("selector menu size");menu.resize(n);for(auto&v:menu){U sum=0;for(auto&a:v.a){a=read_u64(in);if(a>675*f.denominator)throw std::runtime_error("selector coefficient");sum+=a;}if(sum>675*f.denominator)throw std::runtime_error("selector mass bound");}}
 }
 if(in.get()!=-1)throw std::runtime_error("trailing input bytes");
 std::vector<std::array<std::uint8_t,10>>layouts;layouts.reserve(expected);std::array<std::uint8_t,10>current;
 std::function<void(int,int)> gen=[&](int at,int used){if(at==10){layouts.push_back(current);return;}for(int c:{4,5}){current[at]=c;gen(at+1,used);}for(int c=0;c<std::min(used+1,3);c++){current[at]=c;gen(at+1,std::max(used,c+1));}};gen(0,0);
 if(layouts.size()!=expected)throw std::runtime_error("canonical layout count");
 std::size_t limit=layouts.size();if(argc>5)limit=std::min(limit,std::size_t(std::stoull(argv[5])));
 if(limit==0)throw std::runtime_error("zero layout limit");
 std::vector<Result>results(limit);std::atomic<std::size_t>next{0};std::atomic<bool>bad{false};std::mutex errors;
 const int row_role=std::stoi(argv[4]);if(row_role!=0&&row_role!=1)throw std::runtime_error("row role");
 const int requested=std::stoi(argv[3]);if(requested<1||requested>64)throw std::runtime_error("thread count");
 std::vector<int>case_order={14,18,13,17,1,5,9};for(int k=0;k<20;k++)if(std::find(case_order.begin(),case_order.end(),k)==case_order.end())case_order.push_back(k);
 auto worker=[&](){try{while(true){auto start=next.fetch_add(32);if(start>=limit)break;for(auto a=start;a<std::min(start+32,limit);a++){
   const auto&layout=layouts[a];std::array<unsigned,5>masks{};for(unsigned e=0;e<10;e++){unsigned l=layout[e];unsigned u=l<3?l:l-1;masks[u]|=1u<<e;}
   std::array<std::array<U,10>,32>L,H;for(unsigned u=0;u<5;u++){unsigned l=u<3?u:u+1;unsigned n=unsigned(l/3==unsigned(row_role))+unsigned(l==5);for(unsigned col=0;col<2;col++)for(unsigned T=0;T<32;T++){auto idx=((n+col)*1024+masks[u])*32+T;L[T][2*u+col]=lo[idx];H[T][2*u+col]=hi[idx];}}
   Result r;for(int fi:{0,1}){const auto&f=families[fi];S minq=std::numeric_limits<S>::max();bool passed=true;
    for(int k:case_order){r.cases++;const auto&cs=f.cases[k];if(cs.menu[0].size()!=1)throw std::runtime_error("mass menu must be singleton");
     U mass=0;for(int p=0;p<10;p++)mass+=cs.menu[0][0].a[p]*L[0][p];
     W N=W(gL)*mass; // Promotion precedes multiplication.
     for(int mode=0;mode<16&&passed;mode++)for(int T=0;T<32;T++){
      const U fee=C[32*mode+T];if(!fee)continue;U screen=0;
      for(const auto&v:cs.menu[mode]){U value=0;for(int p=0;p<10;p++)value+=v.a[p]*H[T][p];screen=std::max(screen,value);}
      r.screens++;N-=W(fee)*screen; // Promotion precedes multiplication.
      if(floor_q40(N,f.denominator)<S(target)){passed=false;break;}
     }
     if(!passed)break;S q=floor_q40(N,f.denominator);minq=std::min(minq,q);
    }
    if(passed){r.family=fi;r.lower=minq;break;}
   }
   results[a]=r;if(r.family<0)bad.store(true);
  }}}catch(const std::exception&e){bad.store(true);std::lock_guard<std::mutex>lock(errors);std::cerr<<"worker failure: "<<e.what()<<"\n";}catch(...){bad.store(true);std::lock_guard<std::mutex>lock(errors);std::cerr<<"unknown worker failure\n";}};
 std::vector<std::thread>threads;for(int t=0;t<requested;t++)threads.emplace_back(worker);for(auto&t:threads)t.join();
 U minq=std::numeric_limits<U>::max(),minidx=0,total_cases=0,total_screens=0,failed=0;std::array<U,2>counts{};
 for(std::size_t a=0;a<limit;a++){const auto&r=results[a];total_cases+=r.cases;total_screens+=r.screens;if(r.family<0){failed++;continue;}counts[r.family]++;if(U(r.lower)<minq){minq=U(r.lower);minidx=a;}}
 std::ofstream out(argv[2],std::ios::binary);if(!out)throw std::runtime_error("result output");write_u64(out,0x31544c5553455255ULL);write_u64(out,limit);write_u64(out,failed);write_u64(out,minq);write_u64(out,minidx);write_u64(out,total_cases);write_u64(out,total_screens);for(auto c:counts)write_u64(out,c);for(auto c:layouts[minidx])write_u64(out,c);for(const auto&r:results)out.put(char(r.family<0?255:r.family));out.close();if(!out)throw std::runtime_error("result write failure");
 std::cout<<"{\"count\":"<<limit<<",\"failed\":"<<failed<<",\"minimum_q40\":"<<minq<<",\"minimum_index\":"<<minidx<<",\"cases\":"<<total_cases<<",\"screens\":"<<total_screens<<",\"complete\":"<<(limit==expected?"true":"false")<<"}\n";
 if(bad.load())return 2;return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}}
