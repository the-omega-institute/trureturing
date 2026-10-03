#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using I=std::int64_t;using V=std::array<int,17>;using W=std::array<I,17>;using H=std::array<I,12>;
void need(bool b,const char*m){if(!b)throw std::runtime_error(m);}
struct Source{int id;I den;V b;W w;};
int main(int argc,char**argv){
 need(argc==3,"input and output paths required");std::ifstream in(argv[1]);int ns=0;in>>ns;need(ns>0&&ns<=64,"source count");std::vector<Source>sources(ns);
 for(auto&s:sources){in>>s.id>>s.den;for(auto&v:s.b)in>>v;for(auto&v:s.w)in>>v;need(bool(in),"full input");need(0<s.den&&s.den<=1000000000000LL,"bounded exact denominators");I mass=0;for(int x=0;x<17;++x){need(0<=s.b[x]&&s.b[x]<=5&&0<=s.w[x]&&s.w[x]<=s.den,"actual weighted fibers");mass+=(6-s.b[x])*s.w[x];}need(mass==s.den,"source normalization");}
 std::vector<int>pts;for(int x=0;x<45;++x)if(x%3!=0&&x%9!=4&&x%5!=0&&x%15!=1&&x%45!=37)pts.push_back(x);need(pts.size()==17,"first shape points");
 std::array<std::vector<std::uint32_t>,5>groups;int mods[5]={3,5,9,15,45};for(int j=0;j<5;++j){std::set<std::uint32_t>g;for(int a=0;a<mods[j];++a){std::uint32_t m=0;for(int x=0;x<17;++x)if(pts[x]%mods[j]==a)m|=1u<<x;if(m)g.insert(m);}groups[j]={g.begin(),g.end()};}
 std::set<V>unique;for(auto a:groups[0])for(auto b:groups[1])for(auto c:groups[2])for(auto d:groups[3])for(auto e:groups[4]){V q;q.fill(1);for(auto mask:{a,b,c,d,e})for(int x=0;x<17;++x)q[x]+=(mask>>x)&1u;unique.insert(q);}std::vector<V>A(unique.begin(),unique.end());need(A.size()==4760,"complete actual query inventory");
 std::vector<H>answer(ns);std::vector<std::vector<H>>base(ns,std::vector<H>(A.size()));for(int s=0;s<ns;++s)for(std::size_t i=0;i<A.size();++i)for(int t=0;t<12;++t)for(int x=0;x<17;++x)base[s][i][t]+=(5-sources[s].b[x])*sources[s].w[x]*std::max(A[i][x]-t,0);
 std::uint64_t pairs=0;for(std::size_t i=0;i<A.size();++i)for(std::size_t j=0;j<A.size();++j){V sum;for(int x=0;x<17;++x)sum[x]=A[i][x]+A[j][x];for(int s=0;s<ns;++s){I hist[13]={0};for(int x=0;x<17;++x)hist[sum[x]]+=sources[s].w[x];I tail=0,value=0;for(int t=11;t>=0;--t){tail+=hist[t+1];value+=tail;answer[s][t]=std::max(answer[s][t],base[s][i][t]+value);}}++pairs;}
 need(pairs==22657600,"all weighted actual query pairs");std::ofstream out(argv[2]);out<<"{\"scope\":\"Exact full query hinge envelopes on actual reweighted315 sources, not Lean\",\"ordered_pairs\":"<<pairs<<",\"rows\":[";
 for(int s=0;s<ns;++s){need(answer[s][0]-answer[s][1]==sources[s].den,"unit query term");if(s)out<<',';out<<"{\"id\":"<<sources[s].id<<",\"denominator\":"<<sources[s].den<<",\"cell_weight_numerators\":[";for(int x=0;x<17;++x){if(x)out<<',';out<<sources[s].w[x];}out<<"],\"b\":[";for(int x=0;x<17;++x){if(x)out<<',';out<<sources[s].b[x];}out<<"],\"hinge_numerators\":[";for(int t=0;t<12;++t){if(t)out<<',';out<<answer[s][t];}out<<"]}";std::cout<<"source "<<sources[s].id<<" mean numerator "<<answer[s][1]<<" denominator "<<sources[s].den<<"\n";}
 out<<"]}\n";need(bool(out),"result saved");std::cout<<"PASS "<<ns<<" exact weighted source envelopes\n";
}
