// Independent full-layout interval evaluator. No producer source is used.
#include <array>
#include <atomic>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
#include <algorithm>
using u64=std::uint64_t;
using i64=std::int64_t;
using wide=__int128;
static void require(bool b,const char* s){if(!b)throw std::runtime_error(s);}
struct Reader{
 std::ifstream f;
 explicit Reader(const char* p):f(p,std::ios::binary){require(bool(f),"input open");}
 u64 word(){unsigned char b[8];f.read(reinterpret_cast<char*>(b),8);require(bool(f),"truncated input");u64 x=0;for(int k=0;k<8;++k)x|=u64(b[k])<<(8*k);return x;}
};
struct Selector{
 std::array<u64,10> coeff{};std::array<unsigned char,10> index{};unsigned count=0;
 u64 eval(const std::array<u64,10>& h)const{u64 x=0;for(unsigned k=0;k<count;++k)x+=coeff[k]*h[index[k]];return x;}
};
struct Corner{std::array<std::vector<Selector>,16> modes;};
struct Family{u64 den=0,publicDen=0;wide threshold=0;std::array<Corner,20> corners;};
struct Input{
 u64 scale=0,g=0,target=0,expected=0,expectedSelectors=0;std::array<u64,512> costs{};
 std::vector<u64> lower,upper;std::vector<Family> families;
 explicit Input(const char* file){
  Reader r(file);require(r.word()==0x314c4146454c5546ULL,"magic");require(r.word()==2,"version");
  scale=r.word();g=r.word();target=r.word();expected=r.word();auto nf=r.word();expectedSelectors=r.word();require(nf>0&&nf<255,"family count");families.resize(nf);
  require(scale==(u64(1)<<32)&&g==4271830001ULL&&target==2122057442ULL&&expected==1657470ULL,"header constants");
  u64 total=0;for(auto& c:costs){c=r.word();require(c<=4850262370ULL,"coefficient bound");total+=c;}
  require(total==28820733047ULL,"complete coefficient sum");
  lower.resize(4*1024*32);upper.resize(lower.size());
  for(auto& h:lower){h=r.word();require(h<=scale,"lower H range");}
  for(std::size_t k=0;k<upper.size();++k){upper[k]=r.word();require(upper[k]<=scale&&upper[k]>=lower[k]&&upper[k]-lower[k]<=1,"H enclosure range");}
  u64 retained=0;
  for(unsigned fi=0;fi<families.size();++fi){
   auto& f=families[fi];f.den=r.word();require(f.den==1048576ULL,"family denominator");
   f.publicDen=675*f.den*(u64(1)<<24);f.threshold=wide(target)*wide(f.publicDen);
   for(auto& corner:f.corners){for(unsigned mode=0;mode<16;++mode){
    auto n=r.word();require(n>=1&&n<=95,"selector count");if(mode==0)require(n==1,"source singleton");
    retained+=n;corner.modes[mode].resize(n);
    for(auto& s:corner.modes[mode]){u64 sum=0;for(unsigned k=0;k<10;++k){
     auto c=r.word();require(c<=675*f.den,"selector coefficient bound");sum+=c;
     if(c){s.coeff[s.count]=c;s.index[s.count]=static_cast<unsigned char>(k);++s.count;}
    }require(sum<=675*f.den,"selector mass bound");}
   }}
  }
  require(retained==expectedSelectors,"retained complete menus");require(r.f.peek()==std::char_traits<char>::eof(),"trailing input");
 }
};
struct Job{std::array<unsigned char,10> labels{};std::array<unsigned,5> masks{};unsigned used=0,depth=0;u64 begin=0,end=0;};
static u64 continuations(unsigned remaining,unsigned used){
 if(!remaining)return 1;
 return (used+2)*continuations(remaining-1,used)+(used<3?continuations(remaining-1,used+1):0);
}
static std::vector<Job> jobs;
static u64 cursor=0;
static void prefixes(Job state,unsigned depth){
 if(depth==3){state.depth=depth;state.begin=cursor;cursor+=continuations(10-depth,state.used);state.end=cursor;jobs.push_back(state);return;}
 for(unsigned label=0;label<5;++label){
  if(label<3&&label>state.used)continue;
  Job next=state;next.labels[depth]=static_cast<unsigned char>(label);next.masks[label]|=1U<<depth;
  if(label<3&&label==state.used)++next.used;
  prefixes(next,depth+1);
 }
}
struct Stats{
 u64 layouts=0,actual=0,attemptedCorners=0,screenMaxima=0;
 std::array<u64,4> regularClasses{};std::vector<u64> familyCounts;
 explicit Stats(unsigned n=0):familyCounts(n,0){}
 i64 minimum=std::numeric_limits<i64>::max();u64 minimumIndex=std::numeric_limits<u64>::max();
 std::array<unsigned char,10> minimumLabels{};unsigned minimumFamily=0;
};
static std::atomic<std::size_t> nextJob{0};
static std::atomic<u64> completed{0};
static std::atomic<bool> failed{false};
static std::mutex errorMutex;
static std::string errorMessage;
static std::vector<unsigned char> selection;
static constexpr std::array<unsigned,4> multiplicity={1,3,6,6};
static void process(const Input& in,const Job& state,u64 rank,Stats& stats){
 // The ten profiles are each leaf's ordinary/special-quinary Z decrement.
 std::array<std::array<u64,10>,32> upper{};std::array<u64,10> lower0{};
 for(unsigned leaf=0;leaf<5;++leaf){
  unsigned base=leaf<3?0:leaf==3?1:2;
  for(unsigned special=0;special<2;++special){unsigned p=2*leaf+special,n=base+special;
   std::size_t at=(n*1024+state.masks[leaf])*32;
   lower0[p]=in.lower[at];for(unsigned T=0;T<32;++T)upper[T][p]=in.upper[at+T];
  }
 }
 // Each candidate family is tested as one whole family. A failed corner may
 // reject it; acceptance occurs only after all20 corners and all512 fees.
 for(unsigned fi=0;fi<in.families.size();++fi){
  const auto& family=in.families[fi];bool all=true;wide localMinimum=wide(1)<<126;
  for(const auto& corner:family.corners){
   ++stats.attemptedCorners;
   wide gate=wide(in.g)*wide(corner.modes[0][0].eval(lower0));
   for(unsigned T=0;T<32&&gate>=family.threshold;++T){
    for(unsigned mode=0;mode<16;++mode){
     u64 maximum=0;for(const auto& sel:corner.modes[mode])maximum=std::max(maximum,sel.eval(upper[T]));
     ++stats.screenMaxima;
     gate-=wide(in.costs[32*mode+T])*wide(maximum);
    }
   }
   if(gate<family.threshold){all=false;break;}
   localMinimum=std::min(localMinimum,gate);
  }
  if(all){
   // Accepted numerators are positive, so ordinary integer division is floor.
   i64 q=static_cast<i64>(localMinimum/wide(family.publicDen));
   require(q>=static_cast<i64>(in.target),"accepted gate below target");
   selection[rank]=static_cast<unsigned char>(fi);++stats.layouts;++stats.regularClasses[state.used];++stats.familyCounts[fi];stats.actual+=multiplicity[state.used];
   if(q<stats.minimum||(q==stats.minimum&&rank<stats.minimumIndex)){stats.minimum=q;stats.minimumIndex=rank;stats.minimumLabels=state.labels;stats.minimumFamily=fi;}
   return;
  }
 }
 failed=true;std::lock_guard<std::mutex> lock(errorMutex);errorMessage="no entire family at canonical rank "+std::to_string(rank);
}
static void recurse(const Input& in,Job state,unsigned depth,u64& rank,Stats& stats){
 if(failed.load(std::memory_order_relaxed))return;
 if(depth==10){process(in,state,rank++,stats);return;}
 for(unsigned label=0;label<5;++label){
  if(label<3&&label>state.used)continue;
  Job next=state;next.labels[depth]=static_cast<unsigned char>(label);next.masks[label]|=1U<<depth;
  if(label<3&&label==state.used)++next.used;
  recurse(in,next,depth+1,rank,stats);
 }
}
static void worker(const Input& in,Stats& stats){
 try{
  while(!failed.load(std::memory_order_relaxed)){
   auto j=nextJob.fetch_add(1);if(j>=jobs.size())break;u64 rank=jobs[j].begin;
   recurse(in,jobs[j],jobs[j].depth,rank,stats);
   if(!failed.load(std::memory_order_relaxed))require(rank==jobs[j].end,"prefix subtree enumeration count");
   auto before=completed.fetch_add(rank-jobs[j].begin);auto now=before+rank-jobs[j].begin;
   if(before/262144!=now/262144)std::cerr<<"independent verified layouts "<<now<<"\n";
  }
 }catch(const std::exception& e){failed=true;std::lock_guard<std::mutex> lock(errorMutex);errorMessage=e.what();}
}
int main(int argc,char** argv){
 try{
  require(argc==4||argc==5,"usage: checker INPUT_BIN SELECTION_OUT THREADS [smoke]");
  Input in(argv[1]);unsigned n=static_cast<unsigned>(std::stoul(argv[3]));require(n>=1&&n<=64,"thread count");
  if(argc==5){
   require(std::string(argv[4])=="smoke","mode");unsigned ns=4;selection.assign(ns,255);Stats stats(in.families.size());
   for(unsigned rank=0;rank<ns;++rank){Job state;unsigned label=rank==0?4:rank==1?3:0;state.labels.fill(label);if(rank==3){state.labels.fill(4);state.labels[0]=state.labels[3]=3;}for(unsigned e=0;e<10;++e)state.masks[state.labels[e]]|=1U<<e;state.used=rank==2?1:0;process(in,state,rank,stats);require(!failed,"smoke fixed layout failed");}
   require(stats.layouts==ns,"all smoke layouts");
   std::ofstream out(argv[2],std::ios::binary);out.write(reinterpret_cast<const char*>(selection.data()),selection.size());require(bool(out),"smoke selection output");
   std::cout<<"{\"schema\":\"column1-independent-smoke-v1\",\"status\":\"PASS\",\"checked_layouts\":"<<ns<<",\"family_count\":"<<in.families.size()<<",\"accepted_complete_corner_gates\":"<<20*ns<<",\"accepted_complete_screen_maxima\":"<<10240*ns<<",\"minimum_selected_lower_q40\":"<<stats.minimum<<"}\n";return 0;
  }
  prefixes(Job{},0);require(cursor==in.expected,"independent canonical total");selection.resize(cursor,255);
  std::vector<Stats> stats(n,Stats(in.families.size()));std::vector<std::thread> pool;for(unsigned k=0;k<n;++k)pool.emplace_back(worker,std::cref(in),std::ref(stats[k]));for(auto& t:pool)t.join();
  if(failed){std::cerr<<"FAIL: "<<errorMessage<<"\n";return 3;}
  Stats total(in.families.size());
  for(const auto& s:stats){
   total.layouts+=s.layouts;total.actual+=s.actual;total.attemptedCorners+=s.attemptedCorners;total.screenMaxima+=s.screenMaxima;
   for(unsigned k=0;k<4;++k)total.regularClasses[k]+=s.regularClasses[k];
   for(unsigned k=0;k<in.families.size();++k)total.familyCounts[k]+=s.familyCounts[k];
   if(s.minimum<total.minimum||(s.minimum==total.minimum&&s.minimumIndex<total.minimumIndex)){total.minimum=s.minimum;total.minimumIndex=s.minimumIndex;total.minimumLabels=s.minimumLabels;total.minimumFamily=s.minimumFamily;}
  }
  require(total.layouts==1657470&&total.actual==9765625,"complete enumerated layout totals");
  require(total.regularClasses==std::array<u64,4>{1024,58025,465751,1132670},"complete regular-class strata");
  require(std::all_of(selection.begin(),selection.end(),[&](unsigned char x){return x<in.families.size();}),"complete selection witness");
  std::ofstream out(argv[2],std::ios::binary);require(bool(out),"selection output open");out.write(reinterpret_cast<const char*>(selection.data()),selection.size());require(bool(out),"selection output complete");out.close();
  std::cout<<"{\n  \"schema\": \"column1-layout-independent-enumeration-v2\",\n  \"status\": \"PASS\",\n  \"new_lean_verification\": false,\n  \"read_same_round_producer\": false,\n  \"target_q40\": "<<in.target<<",\n  \"canonical_layout_count\": "<<total.layouts<<",\n  \"actual_layout_count\": "<<total.actual<<",\n  \"regular_class_counts\": [";
  for(unsigned k=0;k<4;++k)std::cout<<(k?", ":"")<<total.regularClasses[k];std::cout<<"],\n  \"family_selection_counts\": [";
  for(unsigned k=0;k<in.families.size();++k)std::cout<<(k?", ":"")<<total.familyCounts[k];std::cout<<"],\n  \"accepted_complete_corner_gates\": "<<total.layouts*20<<",\n  \"accepted_complete_screen_maxima\": "<<total.layouts*20*512<<",\n  \"all_attempted_corner_gates\": "<<total.attemptedCorners<<",\n  \"all_computed_screen_maxima\": "<<total.screenMaxima<<",\n  \"minimum_selected_lower_q40\": "<<total.minimum<<",\n  \"minimum_canonical_index\": "<<total.minimumIndex<<",\n  \"minimum_family\": "<<total.minimumFamily<<",\n  \"minimum_labels\": [";
  for(unsigned k=0;k<10;++k)std::cout<<(k?", ":"")<<unsigned(total.minimumLabels[k]);
  std::cout<<"]\n}\n";
  return 0;
 }catch(const std::exception& e){std::cerr<<"FAIL: "<<e.what()<<"\n";return 2;}
}
