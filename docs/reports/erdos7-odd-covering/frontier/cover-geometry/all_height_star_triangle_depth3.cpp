// Exact signed seven-role, three-depth boundary optimizer.
// All quantities below are integers. No original period is enumerated.
// At every depth each role may be off, or be allocated to exactly one node.
// Off choices are handled by subset minima on the second root's remainder.
// Role order: 5,7,11,13,17,19,T; T is the shared 5/7 triangle.
// The signed leaf value may be negative, so saturation is never assumed.
// Each leaf magnitude is at most378675; all tree costs have magnitude
// at most27*378675<2^31. INF is strictly beyond every feasible tree cost.
#include <algorithm>
#include <array>
#include <stdexcept>
#include <limits>
#include <cstdint>
#include <iostream>
#include <vector>
using V=std::vector<int>;
const int M=128,S=M*M,FULL=M-1,INF=1000000000;
std::array<V,M> sub;
std::uint64_t nodework=0,convwork=0;
int leaf(int a,int b,int c){
 int n[7];for(int i=0;i<7;i++)n[i]=((a>>i)&1)+((b>>i)&1)+((c>>i)&1);
 return ((3-n[0])*(5-n[1])-n[6])*(9-n[2])*(11-n[3])*(15-n[4])*(17-n[5]);
}
V conv(const V& x,const V& y){
 V z(S,INF);
 for(int b=0;b<M;b++)for(int c=0;c<M;c++){
  int best=INF;
  for(int u:sub[b])for(int v:sub[c])best=std::min(best,x[u*M+v]+y[(b^u)*M+(c^v)]);
  z[b*M+c]=best;
 }
 convwork+=4782969;
 return z;
}
V subsetmin(V v){
 for(int bit=0;bit<21;bit++)for(int i=0;i<M*S;i++)if(i&(1<<bit))v[i]=std::min(v[i],v[i^(1<<bit)]);
 return v;
}
int main(){
 static_assert(std::numeric_limits<int>::max()>=1000000000);
 for(int m=0;m<M;m++){int u=m;while(true){sub[m].push_back(u);if(!u)break;u=(u-1)&m;}}
 // root order: P23,P33,T333,T233,P23a2,P23a3,P33a3,T333a3,T233a2,T233a3
 std::array<V,10> root;for(auto& r:root)r.resize(M*S);
 for(int a=0;a<M;a++){
  V n2(S),n3(S),a2(S),a3(S);
  for(int b=0;b<M;b++){
   V row(M),pair(M);
   for(int c=0;c<M;c++)row[c]=leaf(a,b,c);
   for(int c=0;c<M;c++){
    int v=INF,w=INF;
    for(int u:sub[c]){v=std::min(v,row[u]+row[c^u]);w=std::min(w,row[u]+2*row[c^u]);}
    pair[c]=v;n2[b*M+c]=2*v;a2[b*M+c]=w;
    nodework+=2*sub[c].size();
   }
   for(int c=0;c<M;c++){
    int v=INF,w=INF;
    for(int u:sub[c]){v=std::min(v,row[u]+pair[c^u]);w=std::min(w,row[u]+2*pair[c^u]);}
    n3[b*M+c]=2*v;a3[b*M+c]=w;
    nodework+=2*sub[c].size();
   }
  }
  auto p23=conv(n2,n3),p33=conv(n3,n3);
  auto p23a2=conv(a2,n3),p23a3=conv(n2,a3),p33a3=conv(a3,n3);
  auto t333=conv(p33,n3),t233=conv(p23,n3),t333a3=conv(p33a3,n3),t233a2=conv(p23a2,n3),t233a3=conv(p23a3,n3);
  std::array<V*,10> parts={&p23,&p33,&t333,&t233,&p23a2,&p23a3,&p33a3,&t333a3,&t233a2,&t233a3};
  for(int j=0;j<10;j++)std::copy(parts[j]->begin(),parts[j]->end(),root[j].begin()+a*S);

 }
 // Each pair places the anchor in root0; root1 uses any subset of its remaining budgets.
 std::array<std::array<int,2>,6> cases={{{4,2},{5,2},{7,0},{6,3},{8,1},{9,1}}};
 const std::array<int,6> expected={3510150,3577860,3586365,3676920,3725466,3748782};
 std::cout<<"{\"orbits\":[";
 for(int j=0;j<6;j++){
  int i0=cases[j][0],i1=cases[j][1];auto off=subsetmin(root[i1]);
  int best=INF,bestfull=INF,arg=-1;
  for(int x=0;x<M*S;x++){
   int z=(M*S-1)^x;
   int v=root[i0][x]+off[z];
   if(v<best){best=v;arg=x;}
   bestfull=std::min(bestfull,root[i0][x]+root[i1][z]);
  }
  if(best!=expected[j] || bestfull!=best)throw std::runtime_error("orbit mismatch");
  if(j)std::cout<<",";
  std::cout<<"{\"orbit\":"<<j<<",\"minimum_with_off\":"<<best<<",\"minimum_saturated\":"<<bestfull
           <<",\"anchor_root_masks\":["<<(arg/S)<<","<<((arg/M)%M)<<","<<(arg%M)<<"]}";
 }
 if(nodework!=143327232ULL || convwork!=6122200320ULL)throw std::runtime_error("work mismatch");
 std::cout<<"],\"node_candidates\":"<<nodework<<",\"root_convolution_candidates\":"<<convwork<<",\"checks_passed\":14}\n";
}
