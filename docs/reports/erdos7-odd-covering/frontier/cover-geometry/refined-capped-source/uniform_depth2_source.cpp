#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <random>
#include <set>
#include <stdexcept>
#include <vector>

using V=std::array<int64_t,5>;
using Layout=std::array<std::array<int,2>,7>;
const std::array<int,7> primes={5,7,11,13,17,19,23};
std::array<std::vector<V>,4> orbit;
int N[8][4]{};

void init(){
  std::array<V,10> base{};
  for(int r=0;r<2;r++)for(int t=0;t<5;t++)for(int l=0;l<5;l++)
    base[5*r+t][l]=1+int((l>=2)==bool(r))+int(l==t);
  for(int k=1;k<=3;k++){
    std::set<V> uniq;
    auto recurse=[&](auto&&self,int left,int start,V v)->void{
      if(left==0){std::sort(v.begin(),v.begin()+2);std::sort(v.begin()+2,v.end());uniq.insert(v);return;}
      for(int i=start;i<10;i++){V next=v;for(int l=0;l<5;l++)next[l]*=base[i][l];self(self,left-1,i,next);}
    };
    recurse(recurse,k,0,V{1,1,1,1,1});
    orbit[k]=std::vector<V>(uniq.begin(),uniq.end());
  }
  if(orbit[1].size()!=4||orbit[2].size()!=16||orbit[3].size()!=48)throw std::runtime_error("orbit count");
  N[0][0]=1;
  for(int h=1;h<=7;h++)for(int k=1;k<=3;k++)N[h][k]=k*N[h-1][k]+(h>=2?(h-1)*N[h-2][k-1]:0);
}

int64_t response(const Layout&layout,int64_t weight_a=1,int64_t weight_b=1){
  int64_t row[5][128];
  for(int l=0;l<5;l++){
    row[l][0]=1;
    for(int s=1;s<128;s++){
      int bit=s&-s,i=__builtin_ctz(unsigned(bit));
      int inc=int((l>=2)==bool(layout[i][0]))+int(l==layout[i][1]);
      row[l][s]=row[l][s^bit]*(primes[i]-2-inc);
    }
  }
  int64_t result=0;
  for(int l=0;l<5;l++)result+=row[l][127]*(l<2?weight_a:weight_b);
  for(int s=1;s<128;s++){
    int h=__builtin_popcount(unsigned(s));if(h<2)continue;
    V v;for(int l=0;l<5;l++)v[l]=row[l][127^s]*(l<2?weight_a:weight_b);
    std::sort(v.begin(),v.begin()+2);std::sort(v.begin()+2,v.end());
    for(int k=1;k<=3;k++)if(N[h][k]){
      int64_t extreme=k%2?0:std::numeric_limits<int64_t>::max();
      for(const auto&c:orbit[k]){
        int64_t value=0;
        for(int l=0;l<5;l++)value+=v[l]*c[k%2?l:(l<2?1-l:6-l)];
        if(k%2)extreme=std::max(extreme,value);else extreme=std::min(extreme,value);
      }
      result+=(k%2?-1:1)*N[h][k]*extreme;
    }
  }
  return result;
}

#ifndef E7_UNIFORM_DEPTH_TWO_LIBRARY
int main(int argc,char**argv){
  init();
  int count=argc>1?std::stoi(argv[1]):0;
  int64_t wa=argc>2?std::stoll(argv[2]):33,wb=argc>3?std::stoll(argv[3]):28;
  // This finite range keeps the complete integer response strictly within
  // signed64-bit capacity; the certified invocation uses weights33 and28.
  if(count<0||count>10000000||wa<0||wb<0||wa>1000||wb>1000||wa+wb==0)
    throw std::runtime_error("parameters outside exact-integer range");
  std::mt19937 gen(20260929);
  std::uniform_int_distribution<int> rdist(0,1),tdist(0,4);
  int64_t minimum=std::numeric_limits<int64_t>::max();Layout best{};
  int negative=0,visited=0,leaf_patterns=0;
  auto visit=[&](const Layout&x){
    int64_t val=response(x,wa,wb);
    negative+=val<0;
    if(val<minimum){minimum=val;best=x;}
    visited++;
  };
  if(count){
    for(int i=0;i<count;i++){
      Layout x;for(auto&rt:x){rt[0]=rdist(gen);rt[1]=tdist(gen);}
      visit(x);
    }
  }else{
    Layout x{};
    auto enumerate=[&](auto&&self,int i,int seen_a,int seen_b)->void{
      if(i==7){
        leaf_patterns++;
        for(int mask=0;mask<128;mask++){
          for(int j=0;j<7;j++)x[j][0]=(mask>>j)&1;
          visit(x);
        }
        return;
      }
      for(int t=0;t<std::min(2,seen_a+1);t++){
        x[i][1]=t;self(self,i+1,std::max(seen_a,t+1),seen_b);
      }
      for(int t=0;t<std::min(3,seen_b+1);t++){
        x[i][1]=t+2;self(self,i+1,seen_a,std::max(seen_b,t+1));
      }
    };
    enumerate(enumerate,0,0,0);
    if(leaf_patterns!=7261||visited!=929408)throw std::runtime_error("complete orbit coverage");
  }
  int64_t den=2*wa+3*wb;for(int p:primes)den*=p-2;
  if(!count&&wa==33&&wb==28&&(minimum!=2263036||den!=1192826250||negative!=0))
    throw std::runtime_error("certified fixed-weight source minimum changed");
  std::cout<<"{\"scope\":\""<<(count?"sampled comparison response only":"all10^7 saturated star vertices modulo S2xS3; ordinary comparison certificate")<<"\",\"samples\":"<<visited
    <<",\"canonical_leaf_patterns\":"<<leaf_patterns
    <<",\"seed\":20260929,\"weight_a\":"<<wa<<",\"weight_b\":"<<wb
    <<",\"negative_samples\":"<<negative<<",\"minimum_numerator\":"<<minimum
    <<",\"denominator\":"<<den<<",\"minimum_decimal\":"<<double(minimum)/den<<",\"layout\":[";
  for(int i=0;i<7;i++)std::cout<<(i?",":"")<<"["<<best[i][0]<<","<<best[i][1]<<"]";
  std::cout<<"]}\n";
}
#endif
