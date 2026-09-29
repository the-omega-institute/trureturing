#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using I=__int128;
using A=std::array<int64_t,7>;
constexpr int64_t D=256, STEPS=8192, E=100000*STEPS, TARGET=15050;
constexpr int64_t R[7]={28,30,36,40,42,46,52};
constexpr int64_t KT[18]={1,8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384};
constexpr int64_t TS[10]={1,8,10,12,16,20,24,32,40,48};
constexpr int64_t CO[7][10]={{0,17433,0,60373,42972,0,0,0,0,0},{0,12486,0,48905,43923,0,0,0,0,0},{0,13379,0,23152,1976,22346,36800,0,0,0},{0,7808,0,6200,25538,0,43974,0,0,0},{0,5254,0,2173,20259,0,52573,0,0,0},{0,6900,0,0,6653,10259,23239,38770,0,0},{0,0,0,4597,0,3250,19992,42974,0,0}};
I power(I v,int n){I a=1;while(n--)a*=v;return a;}
std::string str(I n){if(n==0)return "0";bool neg=n<0;if(neg)n=-n;std::string s;while(n){s.push_back('0'+int(n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
struct Data{I P;std::array<I,21>b2;std::array<I,35>b3;};
Data data(A u){Data x;x.P=1;for(auto v:u)x.P*=v;int j=0,k=0;bool nz=*std::min_element(u.begin(),u.end())>0;
 for(int a=0;a<7;a++)for(int b=a+1;b<7;b++){
  I v=1;if(nz)v=x.P/u[a]/u[b];else for(int t=0;t<7;t++)if(t!=a&&t!=b)v*=u[t];x.b2[j++]=v;
  for(int c=b+1;c<7;c++){v=1;if(nz)v=x.P/u[a]/u[b]/u[c];else for(int t=0;t<7;t++)if(t!=a&&t!=b&&t!=c)v*=u[t];x.b3[k++]=v;}
 }return x;}
int vertex(I numerator,I denominator){I floor=numerator/denominator;int low=0,hi=17;while(low<hi){int md=(low+hi)/2;if(KT[md]+KT[md+1]<=floor)low=md+1;else hi=md;}return KT[low];}
struct Eval{I derivative;I weighted_squares;};
Eval parts(int T,const Data&x,int64_t den){I b2v=0,b3v=0,s2=0,s3=0;I d2=I(E)*power(den,5),d3=I(E)*power(den,4);
 for(I b:x.b2){I v=vertex(I(T)*b,d2);b2v+=b*v;s2+=v*v;}
 for(I b:x.b3){I v=vertex(I(24)*T*b,d3);b3v+=b*v;s3+=v*v;}
 return {x.P-power(den,2)*b2v-power(den,3)*b3v,24*s2+s3};}
I value(int T,const Data&x,int64_t den){auto v=parts(T,x,den);return I(24)*T*v.derivative+I(E)*power(den,7)*v.weighted_squares;}
int choose(A center){A u;for(int i=0;i<7;i++)u[i]=2*R[i]*D-center[i];auto x=data(u);int64_t den=2*D;
 if(parts(0,x,den).derivative<=0)return 0;
 if(parts(STEPS,x,den).derivative>=0)return STEPS;
 int low=0,hi=STEPS;while(hi-low>1){int md=(low+hi)/2;if(parts(md,x,den).derivative>0)low=md;else hi=md;}
 return value(low,x,den)>=value(hi,x,den)?low:hi;}
I unary(A a,int64_t den){I s=0;for(int i=0;i<7;i++)for(int j=0;j<10;j++)s+=I(CO[i][j])*std::max<int64_t>(0,a[i]-TS[j]*den);return s;}
struct Box{A lo,hi;int depth;};
int main(){try{
 I unitden=I(2400)*E*power(D,7),factor=I(24)*E*power(D,6),rhs=TARGET*unitden;
 Box root;for(int i=0;i<7;i++){root.lo[i]=D;root.hi[i]=R[i]*D;}root.depth=0;
 std::vector<Box> stack{root};int64_t nodes=0,leaves=0;I volume=0,full=1;for(auto r:R)full*=(r-1)*D;
 std::map<int,int64_t>depths;int64_t zero=0,mono=0,corner_count=0;auto start=std::chrono::steady_clock::now();
 while(!stack.empty()){
  Box z=stack.back();stack.pop_back();nodes++;I unarylow=unary(z.lo,D);bool ok=false;int branch=0,T=0;A failed{};I failed_lhs=0;
  if(I(24)*unarylow+I(53900)*D>=I(TARGET)*2400*D){ok=true;branch=1;}
  else{
   A center,u;for(int i=0;i<7;i++){center[i]=2*z.hi[i];u[i]=R[i]*D-z.hi[i];}T=choose(center);
   if(unarylow*factor+I(100)*value(T,data(u),D)>=rhs){ok=true;branch=2;}
   else{
    std::array<int64_t,7>ls{};int64_t intercept=0;
    for(int i=0;i<7;i++){center[i]=z.lo[i]+z.hi[i];for(int j=0;j<10;j++)if(center[i]>=2*D*TS[j]){ls[i]+=CO[i][j];intercept-=CO[i][j]*TS[j];}}
    T=choose(center);ok=true;branch=3;
    for(int mask=0;mask<128;mask++){
     A a;I line=I(intercept)*D;for(int i=0;i<7;i++){a[i]=(mask&(1<<(6-i)))?z.hi[i]:z.lo[i];u[i]=R[i]*D-a[i];line+=I(ls[i])*a[i];}
     I lhs=line*factor+I(100)*value(T,data(u),D);
     if(lhs<rhs){ok=false;failed=a;failed_lhs=lhs;break;}
    }
   }
  }
  if(ok){leaves++;I vol=1;for(int i=0;i<7;i++)vol*=z.hi[i]-z.lo[i];volume+=vol;depths[z.depth]++;if(branch==1)zero++;if(branch==2)mono++;if(branch==3)corner_count++;}
  else{
   int j=0;for(int i=1;i<7;i++)if(z.hi[i]-z.lo[i]>z.hi[j]-z.lo[j])j=i;
   if(z.hi[j]-z.lo[j]<=1){std::cerr<<"grid exhausted at ";for(auto a:failed)std::cerr<<a<<",";std::cerr<<" lower="<<str(failed_lhs)<<"/"<<str(unitden)<<"\n";return 2;}
   int64_t mid=(z.lo[j]+z.hi[j])/2,bestdist=INT64_MAX;
   for(int k=0;k<10;k++)if(CO[j][k]&&z.lo[j]<TS[k]*D&&TS[k]*D<z.hi[j]){int64_t a=TS[k]*D,dist=std::abs(2*a-z.lo[j]-z.hi[j]);if(dist<bestdist){bestdist=dist;mid=a;}}
   Box left=z,right=z;left.hi[j]=mid;right.lo[j]=mid;left.depth++;right.depth++;stack.push_back(right);stack.push_back(left);
  }
  if(nodes>30000000)throw std::runtime_error("bounded node cap exhausted");
  if(nodes%100000==0){double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cerr<<"nodes="<<nodes<<" leaves="<<leaves<<" volume="<<(double)volume/(double)full<<" seconds="<<sec<<"\n";}
 }
 if(volume!=full||nodes!=2*leaves-1)throw std::runtime_error("incomplete tree/volume");
 std::cout<<"{\"parameters\":{\"grid_denominator\":"<<D<<",\"lambda_steps\":"<<STEPS<<",\"lambda_denominator\":"<<E<<",\"target\":"<<TARGET<<",\"capacities\":[";
 for(int i=0;i<7;i++){if(i)std::cout<<",";std::cout<<R[i];}
 std::cout<<"],\"knots\":[";for(int i=0;i<18;i++){if(i)std::cout<<",";std::cout<<KT[i];}
 std::cout<<"],\"thresholds\":[";for(int i=0;i<10;i++){if(i)std::cout<<",";std::cout<<TS[i];}
 std::cout<<"],\"coefficients\":[";for(int i=0;i<7;i++){if(i)std::cout<<",";std::cout<<"[";for(int j=0;j<10;j++){if(j)std::cout<<",";std::cout<<CO[i][j];}std::cout<<"]";}
 std::cout<<"]},\"complete\":true,\"nodes\":"<<nodes<<",\"leaves\":"<<leaves<<",\"volume\":\""<<str(volume)<<"\",\"full_volume\":\""<<str(full)<<"\",\"branches\":{\"zero\":"<<zero<<",\"monotone\":"<<mono<<",\"corners\":"<<corner_count<<"},\"depths\":{";
 bool first=true;for(auto p:depths){if(!first)std::cout<<",";first=false;std::cout<<"\""<<p.first<<"\":"<<p.second;}std::cout<<"}}\n";
 return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}}
