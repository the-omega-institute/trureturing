// Shared exhaustive64-template engine: one or three directed profiles.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
using I=std::int64_t;
constexpr int BITS=20,D=1<<BITS,SD=12*D;
struct Profile {I scale,gain,coefficient[192],minimum=std::numeric_limits<I>::max();std::array<int,5> best{};int best_t=0;};
template<int Count>
struct Engine {
 Profile profiles[Count];
 std::uint32_t factor_lo[5][64][8],factor_hi[5][64][8];
 std::uint32_t lo[6][32][8]{},hi[6][32][8]{};
 std::array<int,5> path{};
 std::uint64_t cases=0;
 void include(){
  I gate[Count][2];
  auto* low=lo[5][0];I sum0=low[0]+low[1]+low[2]+low[3],sum1=low[4]+low[5]+low[6]+low[7];
  for(int p=0;p<Count;++p){gate[p][0]=profiles[p].gain*(sum0+2*sum1);gate[p][1]=profiles[p].gain*(2*sum0+sum1);}
  for(int mask=0;mask<32;++mask){
   auto*g=hi[5][mask];int a=g[0]+g[1]+g[2]+g[3],b=g[4]+g[5]+g[6]+g[7];
   int ma=std::max({g[0],g[1],g[2],g[3]}),mb=std::max({g[4],g[5],g[6],g[7]}),cm1=0,cm2=0;
   for(int j=0;j<4;++j){cm1=std::max(cm1,int(g[j]+2*g[j+4]));cm2=std::max(cm2,int(2*g[j]+g[j+4]));}
   int s1[6]={a+2*b,4*cm1,std::max(a,2*b),std::max(a,b),4*std::max(ma,2*mb),4*std::max(ma,mb)};
   int s2[6]={2*a+b,4*cm2,std::max(2*a,b),std::max(a,b),4*std::max(2*ma,mb),4*std::max(ma,mb)};
   for(int p=0;p<Count;++p)for(int mode=0;mode<6;++mode){I c=profiles[p].coefficient[mode*32+mask];gate[p][0]-=c*s1[mode];gate[p][1]-=c*s2[mode];}
  }
  cases+=2;for(int p=0;p<Count;++p)for(int t=0;t<2;++t)if(gate[p][t]<profiles[p].minimum){profiles[p].minimum=gate[p][t];profiles[p].best=path;profiles[p].best_t=t+1;}
 }
 void visit(int q,int max_name){
  if(q==5){include();return;}
  const int count=1<<q;
  for(int row=0;row<2;++row)for(int col=0;col<=std::min(3,max_name+1);++col){
   const int after_col=std::max(max_name,col);
   for(int point_row=0;point_row<2;++point_row)for(int point_col=0;point_col<=std::min(3,after_col+1);++point_col){
    int code=((row*4+col)*2+point_row)*4+point_col;path[q]=code;
    for(int mask=0;mask<count;++mask)for(int k=0;k<8;++k){
     lo[q+1][mask+count][k]=lo[q][mask][k];hi[q+1][mask+count][k]=hi[q][mask][k];
     lo[q+1][mask][k]=(std::uint64_t(lo[q][mask][k])*factor_lo[q][code][k])>>BITS;
     hi[q+1][mask][k]=(std::uint64_t(hi[q][mask][k])*factor_hi[q][code][k]+D-1)>>BITS;
    }
    visit(q+1,std::max(after_col,point_col));
   }
  }
 }
};
I read(std::istream& in){std::string s;if(!(in>>s)||s.empty())throw std::runtime_error("missing integer");I v=0;for(char c:s){if(c<'0'||c>'9'||v>(std::numeric_limits<I>::max()-(c-'0'))/10)throw std::runtime_error("invalid integer");v=10*v+c-'0';}return v;}
template<int Count> void run(std::istream& in){
 Engine<Count> e;
 for(int pi=0;pi<Count;++pi){
  auto&p=e.profiles[pi];p.scale=read(in);p.gain=read(in);
  if(p.scale<=0 || p.scale>std::numeric_limits<I>::max()/SD)throw std::runtime_error("invalid scale");
  __int128 bound=p.gain;
  for(auto&c:p.coefficient){c=read(in);bound+=c;}
  if(bound*SD>=std::numeric_limits<I>::max())throw std::runtime_error("unsafe int64 bound");
 }
 for(int q=0;q<5;++q)for(int code=0;code<64;++code)for(int k=0;k<8;++k){
  I l=read(in),h=read(in);
  if(l>h||h>D)throw std::runtime_error("factor interval");
  e.factor_lo[q][code][k]=l;e.factor_hi[q][code][k]=h;
 }
 std::string extra;if(in>>extra)throw std::runtime_error("extra input");
 for(int k=0;k<8;++k)e.lo[0][0][k]=e.hi[0][0][k]=k?D:0;
 e.visit(0,0);
 for(int pi=0;pi<Count;++pi){
  auto&p=e.profiles[pi];
  std::cout<<pi<<' '<<e.cases<<' '<<p.minimum<<' '<<p.scale*SD<<' '<<p.best_t;
  for(auto v:p.best)std::cout<<' '<<v;
  std::cout<<'\n';
 }
}
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("usage: engine input-file");
 std::ifstream in(argv[1]);if(!in)throw std::runtime_error("cannot open input");
 I profiles=read(in);
 if(profiles==1)run<1>(in);
 else if(profiles==3)run<3>(in);
 else throw std::runtime_error("expected one or three profiles");
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
return 0;
}
