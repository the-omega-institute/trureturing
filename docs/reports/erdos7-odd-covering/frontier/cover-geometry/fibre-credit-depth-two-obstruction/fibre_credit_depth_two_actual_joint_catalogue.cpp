// Exact source and query enumeration for Report753.
// Each source is generated from globally fixed old-cylinder phases and a
// restricted-growth partition of five live-root labels. This enumerates
// effective padded sources, not arbitrary independent per-row deletions.
// Query maxima are evaluated on one source at a time. All accumulations
// below fit the declared integer types; the consumer enables UBSan.
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
using V=std::array<int,17>;using C=std::array<int,5>;
void need(bool v,const char*m){if(!v)throw std::runtime_error(m);}
void vec(std::ostream&o,const V&v,int n){o<<'[';for(int i=0;i<n;++i){if(i)o<<',';o<<v[i];}o<<']';}
struct Group{int count=0;V representative{};};
int main(int argc,char**argv){try{
 need(argc==2,"output path argument required");std::ofstream out(argv[1]);need(bool(out),"open result");
 std::vector<C>colors;C c{};std::function<void(int,int)>rec=[&](int j,int mx){if(j==5){colors.push_back(c);return;}for(int t=0;t<=mx+1;++t){c[j]=t;rec(j+1,std::max(mx,t));}};c[0]=0;rec(1,0);need(colors.size()==52,"all52 color partitions");
 out<<"{\"scope\":\"All six canonical actual315 sources with paired exact c, kappa, H4 and H6; no Lean claim\",\"rows\":[\n";
 const int mods[5]={3,5,9,15,45},w0[5]={0,12,24,12,42},w7[5]={8,22,36,22,57};
 for(int shape=0;shape<6;++shape){
  int root=shape/3+1,cat=shape%3,rr=cat==0?root:3-root,col=cat==1?1:2,a15=-1,a45=-1;
  for(int a=0;a<45;++a){if(a<15&&a%3==root&&a%5==1)a15=a;if(a%9==rr&&a%5==col)a45=a;}
  std::vector<int>xs;for(int x=0;x<45;++x)if(x%3!=0&&x%9!=4&&x%5!=0&&x%15!=a15&&x!=a45)xs.push_back(x);
  int n=xs.size();need(n==(shape<3?17:16),"canonical size");std::array<std::vector<unsigned>,5>groups;int sizes[5]={0};
  for(int j=0;j<5;++j){std::set<unsigned>s;for(int a=0;a<mods[j];++a){unsigned mask=0;int pop=0;for(int i=0;i<n;++i)if(xs[i]%mods[j]==a){mask|=1u<<i;++pop;}if(mask)s.insert(mask);sizes[j]=std::max(sizes[j],pop);}groups[j]={s.begin(),s.end()};}
  std::set<V>sources,queries;std::uint64_t raw=0;
  for(auto a:groups[0])for(auto b:groups[1])for(auto d:groups[2])for(auto e:groups[3])for(auto f:groups[4]){
   std::array<unsigned,5>mask={a,b,d,e,f};V query{};for(int i=0;i<n;++i){query[i]=1;for(auto m:mask)query[i]+=(m>>i)&1u;}queries.insert(query);
   for(auto color:colors){unsigned gone[6]={0};for(int j=0;j<5;++j)gone[color[j]]|=mask[j];V v{};for(int i=0;i<n;++i)for(auto m:gone)v[i]+=(m>>i)&1u;sources.insert(v);++raw;}
  }
  std::vector<V>qs(queries.begin(),queries.end());std::vector<int>J4(qs.size());int J6=0;
  for(std::size_t a=0;a<qs.size();++a)for(std::size_t b=a;b<qs.size();++b){int h4=0,h6=0;for(int i=0;i<n;++i){int v=qs[a][i]+qs[b][i];h4+=std::max(v-4,0);h6+=std::max(v-6,0);}J4[a]=std::max(J4[a],h4);J4[b]=std::max(J4[b],h4);J6=std::max(J6,h6);}
  need(J6==10,"complete uniform H6 numerator");std::map<V,int>energies;
  for(std::size_t a=0;a<qs.size();++a){V energy{};int constant=J4[a];for(int i=0;i<n;++i){energy[i]=std::max(qs[a][i]-4,0);constant+=5*energy[i];}energies[energy]=std::max(energies[energy],constant);}
  int const7=8*n,query7=n;for(int j=0;j<5;++j){const7+=w7[j]*sizes[j];query7+=sizes[j];}
  std::map<std::array<int,4>,Group>catalogue;std::map<std::array<int,3>,int>triplets;std::vector<std::pair<std::array<int,4>,V>>exceptional;
  for(const auto&b:sources){int N=0,M=query7,K=const7,J=0;for(int i=0;i<n;++i)N+=6-b[i];for(int j=0;j<5;++j){int cap=0;for(auto mask:groups[j]){int value=0;for(int i=0;i<n;++i)if(mask>>i&1u)value+=6-b[i];cap=std::max(cap,value);}M+=cap;K+=w0[j]*cap;}
   for(const auto&line:energies){int value=line.second;for(int i=0;i<n;++i)value-=b[i]*line.first[i];J=std::max(J,value);}
   auto&group=catalogue[{N,M,K,J}];if(group.count++==0)group.representative=b;++triplets[{N,M,K}];if(shape>=4&&N==75&&K==1873&&M>=146)exceptional.push_back({{N,M,K,J},b});
  }
  if(shape)out<<",\n";out<<"{\"shape_index\":"<<shape<<",\"a15\":"<<a15<<",\"a45\":"<<a45<<",\"old45_points\":[";for(int x:xs){if(x!=xs[0])out<<',';out<<x;}out<<"],\"effective_cylinders\":[";for(int j=0;j<5;++j){if(j)out<<',';out<<groups[j].size();}out<<"],\"raw_phase_color_cases\":"<<raw<<",\"distinct_b_vectors\":"<<sources.size()<<",\"query_count\":"<<qs.size()<<",\"unordered_query_pairs\":"<<qs.size()*(qs.size()+1)/2<<",\"H4_energy_lines\":"<<energies.size()<<",\"H6_numerator\":"<<J6<<",\"joint_triplets\":[";
  bool first=true;for(auto&p:triplets){if(!first)out<<',';first=false;out<<'['<<p.first[0]<<','<<p.first[1]<<','<<p.first[2]<<','<<p.second<<']';}
  out<<"],\"joint_groups\":[";first=true;for(auto&p:catalogue){if(!first)out<<',';first=false;out<<'['<<p.first[0]<<','<<p.first[1]<<','<<p.first[2]<<','<<p.first[3]<<','<<p.second.count<<',';vec(out,p.second.representative,n);out<<']';}
  out<<"],\"exceptional_hinge4\":[";first=true;for(auto&p:exceptional){if(!first)out<<',';first=false;out<<"{\"triplet\":["<<p.first[0]<<','<<p.first[1]<<','<<p.first[2]<<"],\"H4_numerator\":"<<p.first[3]<<",\"b\":";vec(out,p.second,n);out<<'}';}out<<"]}";
  std::cout<<"shape "<<shape<<" sources "<<sources.size()<<" paired_groups "<<catalogue.size()<<" exceptions "<<exceptional.size()<<'\n';
 }
 out<<"\n]}\n";need(bool(out),"write result");
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
