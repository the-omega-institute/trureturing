// Discovery and computational coverage verifier. Not a Lean-kernel proof.
// Bounds use dyadic integer intervals; doubles propose preconditioners only.
#include <array>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <chrono>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <set>
using namespace std;
using ll=int64_t; using wide=__int128_t;
constexpr ll ONE=1LL<<40;
ll checked(wide x){if(x>INT64_MAX||x<INT64_MIN)throw overflow_error("dyadic bound overflow");return (ll)x;}
ll down(wide n,wide d){if(d==0)throw domain_error("zero denominator");if(d<0){n=-n;d=-d;}wide q=n/d,r=n%d;if(r<0)--q;return checked(q);}
ll up(wide n,wide d){if(d==0)throw domain_error("zero denominator");if(d<0){n=-n;d=-d;}wide q=n/d,r=n%d;if(r>0)++q;return checked(q);}
struct I{ll l,h;I(int n=0):l((ll)n*ONE),h((ll)n*ONE){} I(ll a,ll b):l(a),h(b){if(a>b)throw domain_error("reversed interval");}static I point(ll a){return {a,a};}};
I operator+(I a,I b){return {checked((wide)a.l+b.l),checked((wide)a.h+b.h)};}
I operator-(I a){return {checked(-(wide)a.h),checked(-(wide)a.l)};}
I operator-(I a,I b){return a+(-b);}
I operator*(I a,I b){wide x[4]={(wide)a.l*b.l,(wide)a.l*b.h,(wide)a.h*b.l,(wide)a.h*b.h};return {down(*min_element(x,x+4),ONE),up(*max_element(x,x+4),ONE)};}
I operator/(I a,I b){if(b.l<=0&&0<=b.h)throw domain_error("interval division by zero");I r(down((wide)ONE*ONE,b.h),up((wide)ONE*ONE,b.l));return a*r;}
I sq(I a){wide x=(wide)a.l*a.l,y=(wide)a.h*a.h;if(a.l<=0&&a.h>=0)return {0,up(max(x,y),ONE)};return {down(min(x,y),ONE),up(max(x,y),ONE)};}
ll absmax(I a){return max(checked(-(wide)a.l),a.h);}
ll mid(I a){return down((wide)a.l+a.h,2);}
bool subset(I a,I b){return b.l<=a.l&&a.h<=b.h;}
bool strictsub(I a,I b){return b.l<a.l&&a.h<b.h;}
struct C{I r,i;C(I a=I(0),I b=I(0)):r(a),i(b){}};
C operator+(C a,C b){return {a.r+b.r,a.i+b.i};}C operator-(C a){return {-a.r,-a.i};}C operator-(C a,C b){return a+(-b);}
C operator*(C a,C b){return {a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r};}C conj(C a){return {a.r,-a.i};}I normsq(C a){return sq(a.r)+sq(a.i);}
C operator/(C a,C b){I n=normsq(b);C z=a*conj(b);return {z.r/n,z.i/n};}
using Box=array<I,5>;using Ray=array<C,6>;C H[6][6];
Ray phase(Box const&X,int mask){Ray u;u[0]=C(1);for(int j=0;j<5;j++){I t=X[j],den=I(1)+sq(t);int s=mask>>j&1?-1:1;u[j+1]={I(s)*(I(1)-sq(t))/den,I(2*s)*t/den};}return u;}
void eval(Box const&X,int mask,I f[5],I (*J)[5]){Ray u=phase(X,mask);C du[5];if(J)for(int j=0;j<5;j++){I t=X[j],den=I(1)+sq(t);int s=mask>>j&1?-1:1;du[j]={I(-4*s)*t/sq(den),I(2*s)*(I(1)-sq(t))/sq(den)};}
 for(int a=0;a<5;a++){C y;for(int n=0;n<6;n++)y=y+conj(H[n][a])*u[n];f[a]=normsq(y)-I(6);if(J)for(int j=0;j<5;j++){C z=conj(H[j+1][a])*du[j];J[a][j]=I(2)*(y.r*z.r+y.i*z.i);}}
}
bool propose(I A[5][5],I O[5][5]){double M[5][10];for(int i=0;i<5;i++)for(int j=0;j<10;j++)M[i][j]=j<5?(double)mid(A[i][j])/ONE:(i==j-5);
 for(int k=0;k<5;k++){int p=k;for(int i=k+1;i<5;i++)if(abs(M[i][k])>abs(M[p][k]))p=i;if(abs(M[p][k])<1e-10)return false;for(int j=0;j<10;j++)swap(M[k][j],M[p][j]);double d=M[k][k];for(int j=0;j<10;j++)M[k][j]/=d;for(int i=0;i<5;i++)if(i!=k){d=M[i][k];for(int j=0;j<10;j++)M[i][j]-=d*M[k][j];}}
 for(int i=0;i<5;i++)for(int j=0;j<5;j++){double x=M[i][j+5];if(!isfinite(x)||abs(x)>10000)return false;O[i][j]=I::point((ll)llround(ldexp(x,30))*1024);}
 return true;}
struct Kr{Box k;ll contraction;};
bool krawczyk(Box const&X,int mask,Kr &out){try{Box m;for(int j=0;j<5;j++)m[j]=I::point(mid(X[j]));I f[5],J[5][5],f0[5],J0[5][5],P[5][5];eval(m,mask,f0,J0);if(!propose(J0,P))return false;eval(X,mask,f,J);out.contraction=0;
 for(int i=0;i<5;i++){out.k[i]=m[i];ll row=0;for(int k=0;k<5;k++)out.k[i]=out.k[i]-P[i][k]*f0[k];for(int j=0;j<5;j++){I e=I(i==j);for(int k=0;k<5;k++)e=e-P[i][k]*J[k][j];row=checked((wide)row+absmax(e));out.k[i]=out.k[i]+e*(X[j]-m[j]);}out.contraction=max(row,out.contraction);}return true;
 }catch(overflow_error const&){return false;}}
struct Root{int id,mask;Box x,y;Ray ray;};vector<Root> roots;
void load_roots(string const&path){ifstream in(path);if(!in)throw runtime_error("missing root input");int n=0;if(!(in>>n))throw runtime_error("missing root count");if(n!=60)throw runtime_error("bad root count");set<int> labels;for(int k=0;k<n;k++){Root r{};if(!(in>>r.id>>r.mask))throw runtime_error("truncated root label");if(r.id<0||r.id>=60||r.mask<0||r.mask>=32||!labels.insert(r.id).second)throw runtime_error("bad root label");for(int j=0;j<5;j++){ll t=0;if(!(in>>t))throw runtime_error("truncated root coordinate");r.x[j]={checked((wide)t-(1LL<<24)),checked((wide)t+(1LL<<24))};}Kr q;if(!krawczyk(r.x,r.mask,q)||q.contraction>=ONE)throw runtime_error("root contraction failed");for(int j=0;j<5;j++){if(!strictsub(q.k[j],r.x[j]))throw runtime_error("root inclusion failed");r.y[j]=q.k[j];}for(int iter=0;iter<3;iter++){Kr tight;if(!krawczyk(r.y,r.mask,tight))throw runtime_error("root sharpening failed");for(int j=0;j<5;j++)r.y[j]=I(max(r.y[j].l,tight.k[j].l),min(r.y[j].h,tight.k[j].h));}r.ray=phase(r.y,r.mask);roots.push_back(r);}if(!in)throw runtime_error("truncated root data");string extra;if(in>>extra)throw runtime_error("trailing root data");}
int in_known(Box const&X,int mask){for(auto const&r:roots){Box dest=X;bool ok=true;for(int j=0;j<5;j++){if(((mask^r.mask)>>j)&1){if(dest[j].l<=0&&dest[j].h>=0){ok=false;break;}dest[j]=-I(1)/dest[j];}if(!subset(dest[j],r.x[j])){ok=false;break;}}if(ok)return r.id;}return -1;}
void seed(){ll t=(ll)(sqrt(21)*ONE);while((wide)t*t>(wide)21*ONE*ONE)--t;while((wide)(t+1)*(t+1)<=(wide)21*ONE*ONE)++t; if(!((wide)t*t<(wide)21*ONE*ONE&&(wide)(t+1)*(t+1)>(wide)21*ONE*ONE))throw runtime_error("sqrt bounds failed");C b(I(-3)/I(5),I(4)/I(5)),e(I(-2)/I(5),I(t,t+1)/I(5));for(int i=0;i<3;i++)for(int j=0;j<3;j++){C a=i==j?b:C(1),bb=i==j?e:C(1);H[i][j]=a;H[i][j+3]=bb;H[i+3][j]=conj(bb);H[i+3][j+3]=-conj(a);}}

void interval_seed(string const& path){ifstream f(path);if(!f)throw runtime_error("missing seed interval file");int bits=0;if(!(f>>bits))throw runtime_error("missing interval precision");if(bits!=40)throw runtime_error("wrong interval precision");for(int i=0;i<6;i++)for(int j=0;j<6;j++){ll a,b,c,d;f>>a>>b>>c>>d;if(!f)throw runtime_error("truncated seed matrix");H[i][j]=C(I(a,b),I(c,d));}}
void dump_roots(string const& path){ofstream f(path);if(!f)throw runtime_error("cannot emit root report");f<<roots.size()<<"\n";for(auto const&r:roots){f<<r.id<<" "<<r.mask;for(auto t:r.y)f<<" "<<t.l<<" "<<t.h;f<<"\n";}}

struct Node{Box x;int depth;};
int main(int argc,char**argv){try{if(argc<4)throw runtime_error("usage: cover_exact centers mask max_nodes [report]");seed();if(argc>=6)interval_seed(argv[5]);load_roots(argv[1]);if(argc>=7)dump_roots(argv[6]);int mask=stoi(argv[2]);long cap=stol(argv[3]);if(mask<0||mask>31||cap<1)throw runtime_error("invalid arguments");vector<Node> st;Box b;for(auto&t:b)t=I(-ONE,ONE);st.push_back({b,0});long nodes=0,excluded=0,known=0,contracted=0,unresolved=0;int maxdepth=0;auto start=chrono::steady_clock::now();
 while(!st.empty()&&nodes<cap){auto [X,depth]=st.back();st.pop_back();nodes++;maxdepth=max(maxdepth,depth);if(in_known(X,mask)>=0){known++;continue;}I f[5];eval(X,mask,f,nullptr);bool out=false;for(auto t:f)out|=(t.l>0||t.h<0);if(out){excluded++;continue;}Kr q;
 if(krawczyk(X,mask,q)){bool empty=false;Box Y;for(int j=0;j<5;j++)if(q.k[j].h<X[j].l||q.k[j].l>X[j].h)empty=true;if(empty){excluded++;continue;}bool shrink=false;for(int j=0;j<5;j++){Y[j]={max(q.k[j].l,X[j].l),min(q.k[j].h,X[j].h)};if((wide)5*(Y[j].h-Y[j].l)<(wide)3*(X[j].h-X[j].l))shrink=true;}
 if(in_known(Y,mask)>=0){known++;continue;}if(shrink){st.push_back({Y,depth+1});contracted++;continue;}}
 int j=0;for(int k=1;k<5;k++)if(X[k].h-X[k].l>X[j].h-X[j].l)j=k;ll m=mid(X[j]);if(depth>180||m<=X[j].l||m>=X[j].h){unresolved++;continue;}Box Y=X;Y[j].l=m;X[j].h=m;st.push_back({Y,depth+1});st.push_back({X,depth+1});}
 bool pass=unresolved==0&&st.empty();string status=pass?"COVERED":"INCOMPLETE";double secs=chrono::duration<double>(chrono::steady_clock::now()-start).count();string report="{\"status\":\""+status+"\",\"chart\":"+to_string(mask)+",\"nodes\":"+to_string(nodes)+",\"excluded\":"+to_string(excluded)+",\"known_root_leaves\":"+to_string(known)+",\"contracted\":"+to_string(contracted)+",\"unresolved\":"+to_string(unresolved)+",\"pending\":"+to_string(st.size())+",\"max_depth\":"+to_string(maxdepth)+",\"seconds\":"+to_string(secs)+",\"dyadic_bits\":40,\"lean_kernel_verified\":false}";cout<<report<<endl;if(argc>=5){ofstream f(argv[4]);f<<report<<endl;}return pass?0:2;
 }catch(exception const&e){cerr<<"FAIL CLOSED: "<<e.what()<<endl;return 1;}}
