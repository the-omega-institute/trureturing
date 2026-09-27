// Full five-star scan with phase-free pair query ratio bounds.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
using I=std::int64_t;
constexpr int BITS=20,D=1<<BITS,SD=12*D,CB=30;
constexpr I CD=I(1)<<CB;
struct Engine{
 I scale,gain,oldc[192],newc[192],crossgain[5],klow[10],crosshigh[5];
 I minimum=std::numeric_limits<I>::max();std::array<int,5> best{},path{};int best_t=0;
 int edges[10];
 std::uint32_t flo[5][64][8],fhi[5][64][8],lo[6][32][8]{},hi[6][32][8]{};
 std::uint64_t cases=0;
 static void screens(const I*g,I*s1,I*s2){
  I a=g[0]+g[1]+g[2]+g[3],b=g[4]+g[5]+g[6]+g[7];
  I ma=std::max({g[0],g[1],g[2],g[3]}),mb=std::max({g[4],g[5],g[6],g[7]}),cm1=0,cm2=0;
  for(int j=0;j<4;++j){cm1=std::max(cm1,g[j]+2*g[j+4]);cm2=std::max(cm2,2*g[j]+g[j+4]);}
  s1[0]=a+2*b;s2[0]=2*a+b;s1[1]=4*cm1;s2[1]=4*cm2;
  s1[2]=std::max(a,2*b);s2[2]=std::max(2*a,b);s1[3]=s2[3]=std::max(a,b);
  s1[4]=4*std::max(ma,2*mb);s2[4]=4*std::max(2*ma,mb);s1[5]=s2[5]=4*std::max(ma,mb);
 }
 void include(){
  I g1=0,g2=0;
  auto addmean=[&](int m,I coefficient){auto*g=lo[5][m];I a=g[0]+g[1]+g[2]+g[3],b=g[4]+g[5]+g[6]+g[7];g1+=coefficient*(a+2*b);g2+=coefficient*(2*a+b);};
  addmean(0,gain);for(int q=0;q<5;++q)addmean(31^(1<<q),crossgain[q]);
  for(int m=0;m<32;++m){
   I oldg[8],newg[8];for(int k=0;k<8;++k)oldg[k]=newg[k]=hi[5][m][k];
   for(int j=0;j<10;++j)if(!(m&edges[j])){
    auto*l=lo[5][m|edges[j]];for(int k=1;k<8;++k)newg[k]-=(klow[j]*l[k])>>CB;
   }
   for(int q=0;q<5;++q)if(!(m&(31^(1<<q)))){
    auto*h=hi[5][m|(31^(1<<q))];for(int k=1;k<8;++k)newg[k]+=(crosshigh[q]*h[k]+CD-1)>>CB;
   }
   for(int k=0;k<8;++k){if(newg[k]<0)throw std::runtime_error("negative query upper");newg[k]=std::min(newg[k],oldg[k]);}
   I os1[6],os2[6],ns1[6],ns2[6];screens(oldg,os1,os2);screens(newg,ns1,ns2);
   for(int mode=0;mode<6;++mode){I a=oldc[32*mode+m],b=newc[32*mode+m];g1-=a*os1[mode]+b*ns1[mode];g2-=a*os2[mode]+b*ns2[mode];}
  }
  cases+=2;if(g1<minimum){minimum=g1;best=path;best_t=1;}if(g2<minimum){minimum=g2;best=path;best_t=2;}
 }
 void visit(int q,int max_name){
  if(q==5){include();return;}
  int count=1<<q;
  for(int row=0;row<2;++row)for(int col=0;col<=std::min(3,max_name+1);++col){int ac=std::max(max_name,col);
   for(int pr=0;pr<2;++pr)for(int pc=0;pc<=std::min(3,ac+1);++pc){
    int code=((row*4+col)*2+pr)*4+pc;path[q]=code;
    for(int mask=0;mask<count;++mask)for(int k=0;k<8;++k){
     lo[q+1][mask+count][k]=lo[q][mask][k];hi[q+1][mask+count][k]=hi[q][mask][k];
     lo[q+1][mask][k]=(std::uint64_t(lo[q][mask][k])*flo[q][code][k])>>BITS;
     hi[q+1][mask][k]=(std::uint64_t(hi[q][mask][k])*fhi[q][code][k]+D-1)>>BITS;
    }
    visit(q+1,std::max(ac,pc));
   }
  }
 }
};
I read(std::istream&in){std::string s;if(!(in>>s)||s.empty())throw std::runtime_error("missing integer");I v=0;for(char c:s){if(c<'0'||c>'9'||v>(std::numeric_limits<I>::max()-(c-'0'))/10)throw std::runtime_error("invalid integer");v=10*v+c-'0';}return v;}
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("usage: engine input-file");std::ifstream in(argv[1]);if(!in)throw std::runtime_error("cannot open input");Engine e;
 e.scale=read(in);e.gain=read(in);__int128 bound=e.gain;
 if(e.scale<=0||e.scale>std::numeric_limits<I>::max()/SD)throw std::runtime_error("unsafe scale");
 for(auto&v:e.oldc){v=read(in);bound+=v;}for(auto&v:e.newc){v=read(in);bound+=v;}for(auto&v:e.crossgain){v=read(in);bound+=v;}
 if(bound*SD>=std::numeric_limits<I>::max())throw std::runtime_error("unsafe signed accumulation");
 for(auto&v:e.klow){v=read(in);if(v>CD)throw std::runtime_error("kappa cap");}for(auto&v:e.crosshigh){v=read(in);if(v>CD)throw std::runtime_error("cross cap");}
 for(int q=0;q<5;++q)for(int j=0;j<64;++j)for(int k=0;k<8;++k){I l=read(in),h=read(in);if(l>h||h>D)throw std::runtime_error("factor interval");e.flo[q][j][k]=l;e.fhi[q][j][k]=h;}
 std::string extra;if(in>>extra)throw std::runtime_error("extra input");int idx=0;for(int q=0;q<5;++q)for(int r=q+1;r<5;++r)e.edges[idx++]=(1<<q)|(1<<r);
 for(int k=0;k<8;++k)e.lo[0][0][k]=e.hi[0][0][k]=k?D:0;e.visit(0,0);
 std::cout<<e.cases<<' '<<e.minimum<<' '<<e.scale*SD<<' '<<e.best_t;for(auto c:e.best)std::cout<<' '<<c;std::cout<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}return 0;
}
