#include <algorithm>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using I=std::int64_t;
using V=std::vector<int>;
void need(bool b,const char* m){if(!b)throw std::runtime_error(m);}
int main(){try{
 int n=0;need(bool(std::cin>>n),"point count input");need(n>=1&&n<=17,"supported old45 point count");
 V points(n),live(n);std::vector<I>weight(n);
 for(auto&v:points)std::cin>>v;
 for(auto&v:live)std::cin>>v;
 for(auto&v:weight)std::cin>>v;
 need(bool(std::cin),"complete input");
 need(std::set<int>(points.begin(),points.end()).size()==points.size(),"distinct old45 points");I denominator=0;
 for(int j=0;j<n;++j){need(points[j]>=0&&points[j]<45&&live[j]>0&&live[j]<=6&&weight[j]>=0&&weight[j]<=1000000,"safe integer input");denominator+=live[j]*weight[j];}
 need(denominator>0,"positive source mass");
 std::set<V>states;states.insert(V(n,1));
 for(int d:{3,5,9,15,45}){
  std::set<V>next;
  for(int a=0;a<d;++a){
   V hit(n);int total=0;
   for(int i=0;i<n;++i){hit[i]=points[i]%d==a;total+=hit[i];}
   if(!total)continue;
   for(const auto&prior:states){V q=prior;for(int i=0;i<n;++i)q[i]+=hit[i];next.insert(q);}
  }
  states=std::move(next);
 }
 std::vector<V>queries(states.begin(),states.end());need(!queries.empty(),"nonempty complete old45 inventory");
 I best4=-1,best6=-1,pairs=0;V a4,b4,a6,b6;
 for(const auto&A:queries){
  I prefix4=0;
  for(int i=0;i<n;++i)prefix4+=weight[i]*(live[i]-1)*std::max(A[i]-4,0);
  for(const auto&B:queries){
   I histogram[13]={};
   for(int i=0;i<n;++i)histogram[A[i]+B[i]]+=weight[i];
   I h4=prefix4,h6=0;
   for(int s=5;s<=12;++s)h4+=(s-4)*histogram[s];
   for(int s=7;s<=12;++s)h6+=(s-6)*histogram[s];
   if(h4>best4){best4=h4;a4=A;b4=B;}
   if(h6>best6){best6=h6;a6=A;b6=B;}
   ++pairs;
  }
 }
 std::cout<<"{\"query_count\":"<<queries.size()<<",\"ordered_pairs\":"<<pairs<<",\"denominator\":"<<denominator<<",\"J4\":"<<best4<<",\"J6\":"<<best6;
 auto emit=[&](const char* name,const V&v){std::cout<<",\""<<name<<"\":[";for(int i=0;i<n;++i){if(i)std::cout<<',';std::cout<<v[i];}std::cout<<']';};
 emit("A4",a4);emit("B4",b4);emit("A6",a6);emit("B6",b6);std::cout<<"}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
