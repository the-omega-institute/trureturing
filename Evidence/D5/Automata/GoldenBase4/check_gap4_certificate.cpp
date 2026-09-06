// Solver-free, independently written checker for gap4-proof-v1.
// Recomputes every power, Fibonacci value and digit with exact big integers.
// The producer's branching heuristic is neither imported nor executed.
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using boost::multiprecision::cpp_int;
static void need(bool p,const std::string& why){if(!p)throw std::runtime_error(why);}
static cpp_int root(cpp_int n){
 if(n==0)return 0;
 cpp_int x=cpp_int(1)<<((boost::multiprecision::msb(n)+2)/2);
 for(;;){cpp_int y=(x+n/x)/2;if(y>=x){need(x*x<=n&&(x+1)*(x+1)>n,"sqrt bracket");return x;}x=y;}
}
static cpp_int floorphi(const cpp_int& n){return (n+root(5*n*n))/2;}
struct Record{int index,digit,tail,node;std::vector<int> gap;};
struct Arc{int source,target,table;};
struct Instance{
 std::vector<Record> records;std::vector<Arc> arcs;
 std::vector<std::map<int,int>> next{1};std::map<int,int> labels;
 int tables=0,one=-1,twentysix=-1;
 explicit Instance(const char* path){
  std::ifstream in(path);need(bool(in),"cannot open sample file");
  std::string line;int last=-1;
  while(std::getline(in,line)){
   need(!line.empty(),"empty sample row");std::istringstream s(line);Record r{};
   need(bool(s>>r.index>>r.digit>>r.tail),"bad sample row");
   need(r.index>last&&r.index<=10000,"indices must increase and be bounded");last=r.index;
   need(r.tail==0||r.tail==1,"sample must end in zero or one trailing zero");
   int gap;while(s>>gap){need(gap>=1&&gap<=100000,"nonpositive or oversized gap");r.gap.push_back(gap);}
   need(s.eof(),"noninteger sample data");need(r.gap.size()<=100000,"oversized sample");
   cpp_int q=1,v=2;
   auto bit=[&](int a){cpp_int nq=v+a;v=q+v+2*a;q=nq;};
   for(int g:r.gap){for(int j=0;j<g;++j)bit(0);bit(1);}for(int j=0;j<r.tail;++j)bit(0);
   need(q==(cpp_int(1)<<(2*r.index)),"sample does not represent 4^n");
   need(floorphi(4*q)-4*floorphi(q)==r.digit,"incorrect exact digit");
   need(r.tail==0?(r.digit>=1&&r.digit<=3):(r.digit==0||r.digit==1),"normalization output domain");
   int u=0;
   for(int g:r.gap){
    if(!labels.count(g)){int id=labels.size();labels.emplace(g,id);}
    auto found=next[u].find(g);
    if(found==next[u].end()){int id=next.size();next[u].emplace(g,id);next.emplace_back();u=id;}
    else u=found->second;
   }
   r.node=u;if(r.index==1)one=u;if(r.index==26)twentysix=u;
   records.push_back(r);
  }
  need(!records.empty()&&records.front().index==0&&records.front().node==0&&records.front().digit==2&&records.front().tail==0,"missing root anchor");
  need(one>=0&&twentysix>=0,"missing named-state anchors");
  for(auto r:records){if(r.index==1)need(r.digit==1&&r.tail==0,"anchor n=1");if(r.index==26)need(r.digit==3&&r.tail==0,"anchor n=26");}
  tables=4*labels.size();
  for(int u=0;u<(int)next.size();++u)for(auto [g,v]:next[u])arcs.push_back({tables+u,tables+v,4*labels.at(g)});
 }
 std::vector<int> domains(int extra,int pattern)const{
  std::vector<int>d(tables+next.size(),15);d[tables]=1;
  std::array<int,4> output{2,1,3,extra};
  for(auto r:records){int allowed=0;for(int a=0;a<4;++a)if((r.tail?((pattern>>a)&1):output[a])==r.digit)allowed|=1<<a;d[tables+r.node]&=allowed;}
  d[tables+one]&=2;d[tables+twentysix]&=4;return d;
 }
};
// Work-list scheduling is LIFO, unlike the FIFO producer. All local updates
// remove only unsupported assignments; both schedules reach the same closure.
struct Replay{
 const Instance& instance;std::vector<int>d;
 std::vector<std::vector<int>> incident;
 std::vector<std::pair<int,int>> undo;
 std::vector<int> pending;std::vector<unsigned char> enqueued;
 int empty=0;unsigned long long nodes=0,branches=0,leaves=0,updates=0;int maxdepth=0;
 Replay(const Instance& a,int extra,int pattern):instance(a),d(a.domains(extra,pattern)),incident(d.size()),enqueued(a.arcs.size(),0){
  empty=std::count(d.begin(),d.end(),0);
  for(int i=0;i<(int)a.arcs.size();++i){auto e=a.arcs[i];incident[e.source].push_back(i);incident[e.target].push_back(i);for(int t=0;t<4;++t)incident[e.table+t].push_back(i);schedule(i);}
 }
 void schedule(int i){if(!enqueued[i]){enqueued[i]=1;pending.push_back(i);}}
 void intersect(int variable,int mask){
  int value=d[variable]&mask;if(value==d[variable])return;
  undo.emplace_back(variable,d[variable]);if(value==0)++empty;d[variable]=value;++updates;
  for(int e:incident[variable])schedule(e);
 }
 bool saturate(){
  while(!empty&&!pending.empty()){
   int id=pending.back();pending.pop_back();enqueued[id]=0;auto e=instance.arcs[id];
   int parents=0,children=0;
   for(int a=0;a<4;++a){if(!(d[e.source]&(1<<a)))continue;int supported=d[e.table+a]&d[e.target];if(supported){parents|=1<<a;children|=supported;}}
   intersect(e.source,parents);intersect(e.target,children);
   if(parents&&!(parents&(parents-1))){int a=0;while(!(parents&(1<<a)))++a;intersect(e.table+a,d[e.target]);}
  }
  return empty==0;
 }
 void restore(std::size_t mark){
  for(int i:pending)enqueued[i]=0;pending.clear();
  while(undo.size()>mark){auto [i,old]=undo.back();undo.pop_back();if(d[i]==0)--empty;d[i]=old;}
 }
 void readTree(std::istream& in,int depth=0){
  need(depth<=4*instance.tables,"proof exceeds finite-domain depth bound");maxdepth=std::max(maxdepth,depth);++nodes;
  bool consistent=saturate();std::string symbol;need(bool(in>>symbol),"truncated certificate");
  if(symbol=="L"){need(!consistent,"false contradiction leaf");++leaves;return;}
  need(symbol=="B","unknown proof opcode");need(consistent,"branch at a contradictory domain");
  int variable,mask;need(bool(in>>variable>>mask),"truncated branch");
  need(variable>=0&&variable<instance.tables,"branch index not a transition variable");
  need(mask==d[variable]&&mask>=1&&mask<=15&&(mask&(mask-1)),"incomplete or wrong branch mask");
  ++branches;auto mark=undo.size();
  for(int a=0;a<4;++a)if(mask&(1<<a)){intersect(variable,1<<a);readTree(in,depth+1);restore(mark);}
 }
};
int main(int argc,char**argv){
 try{
  need(argc>=3,"usage: check_gap4_certificate samples.tsv proof1 [proof2 ...]");auto start=std::chrono::steady_clock::now();Instance instance(argv[1]);
  std::set<int> cases;unsigned long long nodes=0,branches=0,leaves=0,updates=0;int maxdepth=0;
  for(int i=2;i<argc;++i){
   std::ifstream file(argv[i]);need(bool(file),"cannot open proof");std::string token;
   need(bool(file>>token)&&token=="gap4-proof-v1","bad proof header");
   while(file>>token){
    need(token=="P","extra or invalid top-level proof data");int extra,pattern;need(bool(file>>extra>>pattern),"missing case parameters");
    need(extra>=1&&extra<=3&&pattern>=0&&pattern<16,"bad case parameters");
    int id=16*(extra-1)+pattern;need(cases.insert(id).second,"duplicate output case");
    Replay replay(instance,extra,pattern);replay.readTree(file);
    nodes+=replay.nodes;branches+=replay.branches;leaves+=replay.leaves;updates+=replay.updates;maxdepth=std::max(maxdepth,replay.maxdepth);
    std::cerr<<"checked case "<<id<<" nodes "<<replay.nodes<<"\n";
   }
   need(file.eof(),"malformed proof stream");
  }
  need(cases.size()==48,"incomplete output-case coverage");
  double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
  std::cout<<"{\"status\":\"PASS\",\"exact_power_rows\":"<<instance.records.size()<<",\"maximum_index\":"<<instance.records.back().index<<",\"gap_letters\":"<<instance.labels.size()<<",\"trie_nodes\":"<<instance.next.size()<<",\"transition_variables\":"<<instance.tables<<",\"output_cases\":48,\"certificate_nodes\":"<<nodes<<",\"branch_nodes\":"<<branches<<",\"contradiction_leaves\":"<<leaves<<",\"domain_updates\":"<<updates<<",\"maximum_depth\":"<<maxdepth<<",\"seconds\":"<<elapsed<<",\"solver_used\":false,\"lean_executed\":false,\"recurrent_capacity_restricted\":false}\n";
 }catch(const std::exception& e){std::cerr<<"REJECT: "<<e.what()<<"\n";return 1;}
}
