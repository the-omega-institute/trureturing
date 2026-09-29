#include <algorithm>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <vector>
using V=std::vector<int>;
void need(bool b,const char*s){if(!b)throw std::runtime_error(s);}
void check(int Q,int p,int q,V ds={}){
 if(ds.empty())for(int d=2;d<=Q;++d)if(Q%d==0)ds.push_back(d);
 auto ppart=[](int d,int a){int z=1;while(d%a==0){d/=a;z*=a;}return z;};
 int Bp=Q/ppart(Q,p),Bq=Q/ppart(Q,q);V choice(ds.size(),-1);
 std::map<V,V> mp,mq,pairs;long long count=0;
 auto run=[&](auto&& self,int j)->void{
  if(j<(int)ds.size()){for(int a=-1;a<ds[j];++a){choice[j]=a;self(self,j+1);}return;}
  ++count;V c(Q,0),lp(Bp,0),lq(Bq,0),sp,sq;
  for(int i=0;i<(int)ds.size();++i){
   if(choice[i]>=0)for(int x=choice[i];x<Q;x+=ds[i])++c[x];
   sp.push_back(choice[i]<0?-1:choice[i]%(ds[i]/ppart(ds[i],p)));
   sq.push_back(choice[i]<0?-1:choice[i]%(ds[i]/ppart(ds[i],q)));
  }
  for(int x=0;x<Q;++x){lp[x%Bp]+=c[x];lq[x%Bq]+=c[x];}
  auto ip=mp.emplace(lp,sp);need(ip.second||ip.first->second==sp,"p marginal collision");
  auto iq=mq.emplace(lq,sq);need(iq.second||iq.first->second==sq,"q marginal collision");
  V both=lp;both.insert(both.end(),lq.begin(),lq.end());
  auto ij=pairs.emplace(both,choice);need(ij.second||ij.first->second==choice,"two marginal collision");
 };
 run(run,0);long long expected=1;for(int d:ds)expected*=d+1;
 need(expected==count && count==(long long)pairs.size(),"incomplete enumeration");
 long long candidate_pairs=0,compatible_pairs=0,phase_conflicts=0;
 for(const auto& ep:mp)for(const auto& eq:mq){
  ++candidate_pairs;bool compatible=true;
  for(int i=0;i<(int)ds.size();++i){
   int a=ep.second[i],b=eq.second[i];
   if((a<0)!=(b<0)){compatible=false;break;}
   int common=std::gcd(ds[i]/ppart(ds[i],p),ds[i]/ppart(ds[i],q));
   if(a>=0 && (a-b)%common!=0){compatible=false;++phase_conflicts;break;}
  }
  V both=ep.first;both.insert(both.end(),eq.first.begin(),eq.first.end());
  need(compatible==(pairs.count(both)!=0),"joint realization criterion mismatch");
  compatible_pairs+=compatible;
 }
 need(compatible_pairs==count,"joint realization count");
 if(Q==105)need(ds==V{105} && candidate_pairs==792 && compatible_pairs==106 && phase_conflicts==630,"shared-cofactor phase control");
 std::cout<<"period="<<Q<<" modulus_slots="<<ds.size()<<" literal_families="<<count<<" marginals="<<mp.size()<<","<<mq.size()<<" paired="<<pairs.size()<<" candidate_pairs="<<candidate_pairs<<" compatible_pairs="<<compatible_pairs<<" phase_conflicts="<<phase_conflicts<<" PASS\n";
}
int main(){check(12,2,3);check(45,3,5);check(15,3,5);check(105,3,5,{105});}
