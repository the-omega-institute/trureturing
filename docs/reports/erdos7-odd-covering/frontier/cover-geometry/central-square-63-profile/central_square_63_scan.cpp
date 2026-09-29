#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <chrono>
using I=std::int64_t;using U=std::uint32_t;using W=std::uint64_t;
constexpr int D=1<<20;constexpr I SD=36LL*D;
struct State{int mark,t,u,um;};
struct Engine{
 I scale,gain,coef[6][8][32]{},threshold;U beta[6],faclo[5][64][2][8],fachi[5][64][2][8];
 U lo[6][32][2][8]{},hi[6][32][2][8]{};State states[16];int path[5]{},limit=64;
 W ways[6][4]{},nodes[6]{},certified=0,leaf_fail=0,examined[6]{},pruned[6]{};
 I least=std::numeric_limits<I>::max();int bestpath[5]{},beststate=-1,bestdepth=-1;
 W count(int d,int maxn){if(d==5)return 1;if(ways[d][maxn])return ways[d][maxn];W n=0;
 for(int r=0;r<2;++r)for(int c=0;c<=std::min(3,maxn+1);++c){int m=std::max(c,maxn);for(int kr=0;kr<2;++kr)for(int kc=0;kc<=std::min(3,m+1);++kc)n+=count(d+1,std::max(m,kc));}return ways[d][maxn]=n;}
 I bound(int d,int sid){const State&s=states[sid];I mass=0;
 for(int r=0;r<2;++r)for(int j=0;j<4;++j){int k=4*r+j;I b=lo[d][0][0][k],a=lo[d][0][1][k];int t=r?9-s.t:s.t;mass+=t*b+(r==s.mark?s.u*(a-b):0);}
 I lower_mass=mass*beta[d]/D;I val=gain*lower_mass;
 const int count=1<<d;
 for(int mask=0;mask<count;++mask){auto*b=hi[d][mask][0];auto*a=hi[d][mask][1];I rs[2]{},bs[2]{},as[2]{},maxa=0,maxb=0,maxleaf=0,maxrowleaf=0,maxcol=0;I wa[8];
  for(int r=0;r<2;++r){int t=r?9-s.t:s.t;for(int j=0;j<4;++j){int k=4*r+j;bs[r]+=b[k];as[r]+=a[k];wa[k]=t*I(b[k])+(r==s.mark?s.u*(I(a[k])-b[k]):0);rs[r]+=wa[k];maxa=std::max(maxa,wa[k]);maxb=std::max(maxb,I(b[k]));maxleaf=std::max(maxleaf,I(r==s.mark?s.um:2)*b[k]);if(r==s.mark)maxleaf=std::max(maxleaf,I(s.u)*a[k]);}}
  for(int r=0;r<2;++r){maxrowleaf=std::max(maxrowleaf,I(r==s.mark?s.um:2)*bs[r]);if(r==s.mark)maxrowleaf=std::max(maxrowleaf,I(s.u)*as[r]);}
  for(int j=0;j<4;++j)maxcol=std::max(maxcol,wa[j]+wa[j+4]);
  I screens[8]={rs[0]+rs[1],4*maxcol,std::max(rs[0],rs[1]),4*maxa,maxrowleaf,4*maxleaf,std::max(bs[0],bs[1]),4*maxb};
  for(int mode=0;mode<8;++mode)val-=coef[d][mode][mask]*screens[mode];
  if(d<5 && val<threshold)return val;
 }
 return val;
 }
 void visit(int d,int maxn,U active){++nodes[d];if(d){U keep=0;for(int sid=0;sid<16;++sid)if(active>>sid&1){++examined[d];I v=bound(d,sid);if(v>=threshold){++pruned[d];certified+=count(d,maxn);if(v<least){least=v;beststate=sid;bestdepth=d;std::copy(path,path+5,bestpath);}}else if(d==5){++leaf_fail;if(v<least){least=v;beststate=sid;bestdepth=d;std::copy(path,path+5,bestpath);}if(leaf_fail<5){std::cout<<"FAIL "<<v<<" state "<<sid<<" codes";for(int k:path)std::cout<<' '<<k;std::cout<<'\n';}}else keep|=1u<<sid;}active=keep;if(!active)return;}
 const int masks=1<<d;
 for(int r=0;r<2;++r)for(int c=0;c<=std::min(3,maxn+1);++c){int next=std::max(maxn,c);for(int kr=0;kr<2;++kr)for(int kc=0;kc<=std::min(3,next+1);++kc){int code=((r*4+c)*2+kr)*4+kc;if(d==0&&code>=limit)continue;path[d]=code;
  for(int mask=0;mask<masks;++mask)for(int alt=0;alt<2;++alt)for(int k=0;k<8;++k){lo[d+1][mask+masks][alt][k]=lo[d][mask][alt][k];hi[d+1][mask+masks][alt][k]=hi[d][mask][alt][k];lo[d+1][mask][alt][k]=(W(lo[d][mask][alt][k])*faclo[d][code][alt][k])>>20;hi[d+1][mask][alt][k]=(W(hi[d][mask][alt][k])*fachi[d][code][alt][k]+D-1)>>20;}
  visit(d+1,std::max(next,kc),active);
  if(d==0)std::cerr<<"q7 "<<code<<" certified "<<certified<<" failed "<<leaf_fail<<" nodes5 "<<nodes[5]<<'\n';
 }}
 }
};
I read_uint(std::istream&in){std::string s;if(!(in>>s)||s.empty())throw std::runtime_error("missing unsigned integer");I v=0;for(char c:s){if(c<'0'||c>'9'||v>(std::numeric_limits<I>::max()-(c-'0'))/10)throw std::runtime_error("invalid or overflowing unsigned integer");v=10*v+c-'0';}return v;}
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("usage: central_square_63_scan input-file");std::ifstream in(argv[1]);if(!in)throw std::runtime_error("input unavailable");Engine e;
 e.scale=read_uint(in);e.gain=read_uint(in);I dd=read_uint(in),denominator=read_uint(in);
 if(e.scale!=100000000||e.gain!=1155102040||dd!=D||denominator!=1000)throw std::runtime_error("scale/gain/threshold mismatch");
 __int128 total=e.gain;for(int mode=0;mode<8;++mode)for(int mask=0;mask<32;++mask){e.coef[5][mode][mask]=read_uint(in);total+=e.coef[5][mode][mask];}
 if(total*SD>=std::numeric_limits<I>::max())throw std::runtime_error("unsafe signed-64 accumulation");
 for(int d=4;d>=0;--d)for(int mode=0;mode<8;++mode)for(int mask=0;mask<(1<<d);++mask)e.coef[d][mode][mask]=e.coef[d+1][mode][mask]+e.coef[d+1][mode][mask+(1<<d)];
 if(read_uint(in)!=16)throw std::runtime_error("state count");
 const int triples[8][3]={{3,0,2},{3,1,2},{3,2,1},{4,0,2},{4,2,2},{5,1,2},{5,2,2},{6,2,2}};
 for(int i=0;i<16;++i){I r=read_uint(in),t=read_uint(in),u=read_uint(in),um=read_uint(in);const auto*z=triples[i%8];if(r!=i/8||t!=(r?9-z[0]:z[0])||u!=z[1]||um!=z[2])throw std::runtime_error("state mismatch");e.states[i]={int(r),int(t),int(u),int(um)};}
 for(int d=0;d<=5;++d){I b=read_uint(in);if(b<=0||b>D||(d==5&&b!=D))throw std::runtime_error("remaining-factor bound");e.beta[d]=U(b);}
 for(int q=0;q<5;++q)for(int code=0;code<64;++code)for(int alt=0;alt<2;++alt)for(int k=0;k<8;++k){I l=read_uint(in),h=read_uint(in);if(l<=0||l>h||h>D||h-l>1)throw std::runtime_error("factor interval");e.faclo[q][code][alt][k]=U(l);e.fachi[q][code][alt][k]=U(h);}
 std::string extra;if(in>>extra)throw std::runtime_error("trailing input");
 e.threshold=e.scale*SD/denominator;if(e.threshold*denominator!=e.scale*SD)throw std::runtime_error("nonintegral threshold");
 for(int alt=0;alt<2;++alt)for(int k=0;k<8;++k)e.lo[0][0][alt][k]=e.hi[0][0][alt][k]=k?D:0;
 constexpr W expected_orbits=179481600,expected_cases=16*expected_orbits;
 if(e.count(0,0)!=expected_orbits)throw std::runtime_error("suffix orbit count mismatch");
 auto started=std::chrono::steady_clock::now();e.visit(0,0,65535);
 if(e.leaf_fail||e.certified!=expected_cases||e.least<e.threshold||e.least==std::numeric_limits<I>::max()||e.beststate<0||e.beststate>=16||e.bestdepth<1||e.bestdepth>5)throw std::runtime_error("incomplete or nonpositive certificate");
 std::cout<<"threshold 1/"<<denominator<<" certified "<<e.certified<<" expected "<<expected_cases<<" failed "<<e.leaf_fail<<" lower "<<e.least<<" denominator "<<e.scale*SD<<" state "<<e.beststate<<" depth "<<e.bestdepth<<" codes";for(int v:e.bestpath)std::cout<<' '<<v;std::cout<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<'\n';
 for(int d=0;d<=5;++d)std::cout<<d<<" nodes "<<e.nodes[d]<<" eval "<<e.examined[d]<<" pruned "<<e.pruned[d]<<'\n';return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
