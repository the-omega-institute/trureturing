// Uniform fixed-weight shared-deficit source comparison.
#define E7_UNIFORM_DEPTH_TWO_LIBRARY
#include "uniform_depth2_source.cpp"
#undef E7_UNIFORM_DEPTH_TWO_LIBRARY

int64_t pair_response(const Layout& layout,int64_t wa,int64_t wb,int64_t baseline){
  constexpr int64_t scale=572;
  std::array<V,10> cs{};
  for(int r=0;r<2;r++)for(int t=0;t<5;t++)for(int l=0;l<5;l++)cs[5*r+t][l]=1+int((l>=2)==bool(r))+int(l==t);
  V row[128]; int64_t first[128][10]{},mx[128]{};int deg[128]{};
  for(int s=0;s<128;s++){
    for(int l=0;l<5;l++){
      row[s][l]=l<2?wa:wb;
      for(int i=0;i<7;i++)if(!(s>>i&1))row[s][l]*=primes[i]-2-int((l>=2)==bool(layout[i][0]))-int(l==layout[i][1]);
    }
    if(__builtin_popcount(unsigned(s))<2)continue;
    for(int j=0;j<10;j++)for(int l=0;l<5;l++)first[s][j]+=row[s][l]*cs[j][l];
    for(int j=0;j<10;j++)mx[s]=std::max(mx[s],first[s][j]);
    for(int t=1;t<128;t++)deg[s]+=__builtin_popcount(unsigned(t))>=2&&!(s&t);
  }
  int64_t total=baseline*scale;
  for(int s=1;s<128;s++)if(deg[s])for(int t=s+1;t<128;t++)if(deg[t]&&!(s&t)){
    int64_t lo=std::numeric_limits<int64_t>::max(),energy=lo;
    for(int i=0;i<10;i++)for(int j=0;j<10;j++){
      int64_t pair=0;
      for(int l=0;l<5;l++)pair+=row[s|t][l]*cs[i][l]*cs[j][l];
      lo=std::min(lo,pair);
      energy=std::min(energy,scale*pair+(scale/deg[s])*(mx[s]-first[s][i])+(scale/deg[t])*(mx[t]-first[t][j]));
    }
    if(energy<scale*lo)throw std::runtime_error("negative pair correction");
    total+=energy-scale*lo;
  }
  return total;
}
int main(){
  init();constexpr int count=0;
  constexpr int64_t wa=33,wb=28;
  constexpr int cutoff_denom=100;
  int64_t den=2*wa+3*wb;for(int p:primes)den*=p-2;
  if(count<0||count>10000000||wa<=0||wb<=0||wa>1000||wb>1000||cutoff_denom<1)throw std::runtime_error("range");
  int visits=0,refined=0,leaves=0,raw_leaves=0,minimizers=0;int64_t oldmin=INT64_MAX,newmin=INT64_MAX;Layout best{};
  auto visit=[&](const Layout&x){
    auto v=response(x,wa,wb);oldmin=std::min(oldmin,v);visits++;
    if(v*cutoff_denom>=den)return;
    refined++;auto n=pair_response(x,wa,wb,v);
    if(n<newmin){newmin=n;best=x;minimizers=1;}else if(n==newmin)minimizers++;
    if(refined%1000==0)std::cerr<<"refined="<<refined<<" visits="<<visits<<" min="<<double(newmin)/(572*den)<<"\n";
  };
  if(count){std::mt19937 gen(20260930);std::uniform_int_distribution<int>rd(0,1),td(0,4);for(int k=0;k<count;k++){Layout x;for(auto&rt:x){rt[0]=rd(gen);rt[1]=td(gen);}visit(x);}}
  else{
    Layout x{};
    auto enumerate=[&](auto&&self,int i,int seen_a,int seen_b)->void{
      if(i==7){leaves++;int orbit_size=1;for(int j=0;j<seen_a;j++)orbit_size*=2-j;for(int j=0;j<seen_b;j++)orbit_size*=3-j;raw_leaves+=orbit_size;for(int mask=0;mask<128;mask++){for(int j=0;j<7;j++)x[j][0]=(mask>>j)&1;visit(x);}return;}
      for(int t=0;t<std::min(2,seen_a+1);t++){x[i][1]=t;self(self,i+1,std::max(seen_a,t+1),seen_b);}
      for(int t=0;t<std::min(3,seen_b+1);t++){x[i][1]=t+2;self(self,i+1,seen_a,std::max(seen_b,t+1));}
    };enumerate(enumerate,0,0,0);
    if(leaves!=7261||raw_leaves!=78125||visits!=929408)throw std::runtime_error("orbit coverage");
  }
  if(refined!=683||oldmin!=2263036||newmin!=4431234914||572*den!=682296615000||newmin*100>=572*den)throw std::runtime_error("certified refined minimum");
  std::cout<<"{\"raw_vertices\":"<<128*raw_leaves<<",\"canonical_minimizers\":"<<minimizers<<",\"complete\":"<<(count?"false":"true")<<",\"visits\":"<<visits<<",\"refined\":"<<refined<<",\"cutoff_denominator\":"<<cutoff_denom<<",\"old_min_numerator\":"<<oldmin<<",\"refined_min_numerator\":"<<newmin<<",\"refined_denominator\":"<<572*den<<",\"refined_min\":"<<double(newmin)/(572*den)<<",\"layout\":[";
  for(int i=0;i<7;i++)std::cout<<(i?",":"")<<"["<<best[i][0]<<","<<best[i][1]<<"]";
  std::cout<<"]}\n";
}
