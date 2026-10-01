#define E7_UNIFORM_DEPTH_TWO_LIBRARY
#include "uniform_depth2_source.cpp"
#undef E7_UNIFORM_DEPTH_TWO_LIBRARY

#include <chrono>

__int128 pair_response(const Layout& layout,__int128 wa,__int128 wb,__int128 baseline){
  constexpr __int128 scale=572;
  std::array<V,10> cs{};
  for(int r=0;r<2;r++)for(int t=0;t<5;t++)for(int l=0;l<5;l++)cs[5*r+t][l]=1+int((l>=2)==bool(r))+int(l==t);
  std::array<__int128,5> row[128]; __int128 first[128][10]{},mx[128]{};int deg[128]{};
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
  __int128 total=baseline*scale;
  for(int s=1;s<128;s++)if(deg[s])for(int t=s+1;t<128;t++)if(deg[t]&&!(s&t)){
    __int128 lo=std::numeric_limits<__int128>::max(),energy=lo;
    for(int i=0;i<10;i++)for(int j=0;j<10;j++){
      __int128 pair=0;
      for(int l=0;l<5;l++)pair+=row[s|t][l]*cs[i][l]*cs[j][l];
      lo=std::min(lo,pair);
      energy=std::min(energy,scale*pair+(scale/deg[s])*(mx[s]-first[s][i])+(scale/deg[t])*(mx[t]-first[t][j]));
    }
    if(energy<scale*lo)throw std::runtime_error("negative pair correction");
    total+=energy-scale*lo;
  }
  return total;
}
std::string wide(__int128 n){if(!n)return "0";bool neg=n<0;if(neg)n=-n;std::string s;while(n){s.push_back(char('0'+n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
int main(){
  init();constexpr int count=0;
  constexpr int64_t wa=1575730278,wb=1300374491;
  constexpr int cutoff_denom=100;
  // The sum of absolute baseline terms is at most
  // (2wa+3wb)*18728919 =132087275019834651 <2^63.
  // Pair terms and their common denominator use signed128-bit arithmetic.
  __int128 den=2*__int128(wa)+3*__int128(wb);for(int p:primes)den*=p-2;
  if(count<0||count>10000000||wa<=0||wb<=0||wa>2000000000LL||wb>2000000000LL||cutoff_denom<1)throw std::runtime_error("range");
  int visits=0,refined=0,leaves=0,raw_leaves=0,minimizers=0;__int128 oldmin=std::numeric_limits<__int128>::max(),newmin=std::numeric_limits<__int128>::max();Layout best{};
  auto visit=[&](const Layout&x){
    __int128 v=response(x,wa,wb);oldmin=std::min(oldmin,v);visits++;
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
  if(refined!=722||oldmin!=222646444984111LL||newmin!=__int128(256643908771876456LL)||572*den!=__int128(3207969473326507890LL)*10||newmin*100>=572*den)throw std::runtime_error("certified optimum changed");
  std::cout<<"{\"raw_vertices\":"<<128*raw_leaves<<",\"canonical_minimizers\":"<<minimizers<<",\"complete\":"<<(count?"false":"true")<<",\"visits\":"<<visits<<",\"refined\":"<<refined<<",\"cutoff_denominator\":"<<cutoff_denom<<",\"old_min_numerator\":"<<wide(oldmin)<<",\"refined_min_numerator\":"<<wide(newmin)<<",\"refined_denominator\":"<<wide(572*den)<<",\"refined_min\":"<<double(newmin)/(572*den)<<",\"layout\":[";
  for(int i=0;i<7;i++)std::cout<<(i?",":"")<<"["<<best[i][0]<<","<<best[i][1]<<"]";
  std::cout<<"]}\n";
}
