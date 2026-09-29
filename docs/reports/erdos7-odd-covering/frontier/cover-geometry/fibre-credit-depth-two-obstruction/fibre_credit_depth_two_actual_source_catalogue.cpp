#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>
using V=std::array<int,17>;using A12=std::array<int,12>;using Colors=std::array<int,5>;
void require(bool b,const char*m){if(!b)throw std::runtime_error(m);}
int main(int argc,char**argv){
 require(argc==2,"exact output path required");
 std::vector<int>pts;for(int x=0;x<45;++x)if(x%3!=0&&x%9!=4&&x%5!=0&&x%15!=1&&x%45!=37)pts.push_back(x);require(pts.size()==17,"actual firstshape");
 std::array<std::vector<std::uint32_t>,5>groups;int mods[5]={3,5,9,15,45};
 for(int j=0;j<5;++j){std::set<std::uint32_t>s;for(int a=0;a<mods[j];++a){std::uint32_t m=0;for(int i=0;i<17;++i)if(pts[i]%mods[j]==a)m|=1u<<i;if(m)s.insert(m);}groups[j]={s.begin(),s.end()};}
 std::vector<Colors>colors;Colors cur{};std::function<void(int,int)>gen=[&](int n,int mx){if(n==5){colors.push_back(cur);return;}for(int c=0;c<=mx+1;++c){cur[n]=c;gen(n+1,std::max(c,mx));}};cur[0]=0;gen(1,0);require(colors.size()==52,"all color partitions");
 std::set<V>queries;std::map<int,std::set<V>>sources;std::uint64_t layouts=0,total=0;
 for(auto a:groups[0])for(auto b:groups[1])for(auto c:groups[2])for(auto d:groups[3])for(auto e:groups[4]){
  std::array<std::uint32_t,5>ms={a,b,c,d,e};V q;q.fill(1);for(auto m:ms)for(int i=0;i<17;++i)q[i]+=(m>>i)&1u;queries.insert(q);++layouts;
  for(auto col:colors){std::uint32_t gone[6]={0};for(int j=0;j<5;++j)gone[col[j]]|=ms[j];V v{};int removed=0;for(int i=0;i<17;++i){for(auto m:gone)v[i]+=(m>>i)&1u;removed+=v[i];}sources[102-removed].insert(v);++total;}
 }
 require(layouts==4760&&queries.size()==4760&&total==247520,"actual inventories complete");
 using Key=std::pair<int,int>;
 std::map<Key,std::set<V>>grouped;
 for(auto&nv:sources)for(auto&b:nv.second){int numerator=42;for(auto&gs:groups){int best=0;for(auto mask:gs){int value=0;for(int x=0;x<17;++x)if((mask>>x)&1u)value+=6-b[x];best=std::max(best,value);}numerator+=best;}grouped[{nv.first,numerator}].insert(b);}
 std::cout<<"actual (N,mean-numerator) groups "<<grouped.size()<<"\n";
 std::vector<V>A(queries.begin(),queries.end());std::vector<A12>J(A.size());
 for(std::size_t i=0;i<A.size();++i)for(std::size_t j=i;j<A.size();++j){int hist[13]={0};for(int x=0;x<17;++x)++hist[A[i][x]+A[j][x]];int tail=0,val=0;for(int t=11;t>=0;--t){tail+=hist[t+1];val+=tail;J[i][t]=std::max(J[i][t],val);J[j][t]=std::max(J[j][t],val);}}
 std::map<Key,A12>nums;std::size_t sourcecount=0;for(auto&nv:grouped)sourcecount+=nv.second.size();std::cout<<"joint source vectors "<<sourcecount<<"\n";
 for(int t=0;t<12;++t){
  std::map<V,int>lines;for(std::size_t i=0;i<A.size();++i){V v{};int sum=0;for(int x=0;x<17;++x){v[x]=std::max(A[i][x]-t,0);sum+=v[x];}lines[v]=std::max(lines[v],5*sum+J[i][t]);}
  std::vector<std::pair<int,V>>ordered;for(auto&vf:lines)ordered.push_back({vf.second,vf.first});std::sort(ordered.rbegin(),ordered.rend());
  for(auto&nv:grouped){int best=-1;for(auto&fv:ordered){if(fv.first<=best)break;int lowest=10000;for(auto&b:nv.second){int dot=0;for(int x=0;x<17;++x){dot+=b[x]*fv.second[x];if(dot>=lowest)break;}lowest=std::min(lowest,dot);if(lowest==0)break;}best=std::max(best,fv.first-lowest);}require(best>=0,"exact maximum found");nums[nv.first][t]=best;}
  std::cout<<"hinge "<<t<<" unique query energies "<<lines.size()<<"\n";
 }
 std::ofstream f(argv[1]);f<<"{\"scope\":\"Exact convex-query maxima over actual padded315 actual source groups by N, not Lean\",\"layouts\":4760,\"color_partitions\":52,\"total_cases\":247520,\"source_vectors\":"<<sourcecount<<",\"rows\":[\n";bool first=true;
 for(auto&nh:nums){if(!first)f<<",\n";first=false;f<<"{\"N\":"<<nh.first.first<<",\"M\":"<<nh.first.second<<",\"source_vector_count\":"<<grouped[nh.first].size()<<",\"hinge_numerators\":[";for(int t=0;t<12;++t){if(t)f<<',';f<<nh.second[t];}f<<"]}";}f<<"\n],\"exceptional_sources\":[";first=true;
 for(auto&entry:grouped)if(entry.first.first==86&&(entry.first.second==184||entry.first.second==185))for(auto&b:entry.second){
  if(!first)f<<',';first=false;f<<"{\"N\":86,\"M\":"<<entry.first.second<<",\"b\":[";
  for(int x=0;x<17;++x){if(x)f<<',';f<<b[x];}f<<"]}";
 }
 f<<"]}\n";require(bool(f),"output saved");std::cout<<"PASS all actual grouped and all complete queries\n";
}
