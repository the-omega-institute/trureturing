// Independent replay of the actual EJMCacheState initial/step/lower path.
// Every reachable DAG occurrence carries its actual state and partial event.
// Finite association memoization keys the whole local partial and compares
// the actual row AND earned action at every occurrence; shape IDs never key it.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
namespace fs=std::filesystem;
struct Node{uint32_t kind,payload;std::array<uint32_t,4>child;};
struct Action{std::array<int,20>source;std::array<int,4>outcome;};
struct LocalRow{int key;int64_t lower;std::array<std::array<uint32_t,4>,10>words{};};
struct State{std::array<uint32_t,32>value;int64_t lower;};
struct LocalCache{
 int n,count;std::vector<LocalRow>rows;std::array<std::array<int,10>,12>perm{};
 std::array<std::array<int,12>,12>cmul{};
 std::array<std::array<int,16>,20>incidence{};
 std::vector<uint32_t>association;std::unordered_set<uint64_t>additional;
 uint64_t unique=0,checks=0,multiple_representation_checks=0;
 LocalCache(std::istream&in,int expected_n,int expected_count){
  in>>n>>count;if(n!=expected_n||count!=expected_count)throw std::runtime_error("cache dimension");
  for(auto&r:perm)for(int i=0;i<n;i++)in>>r[i];
  for(auto&r:cmul)for(auto&v:r)in>>v;
  for(auto&r:incidence)for(auto&v:r)in>>v;
  rows.resize(count);for(auto&r:rows){in>>r.key>>r.lower;for(int i=0;i<n;i++)for(auto&v:r.words[i])in>>v;}
  int keys=1;for(int i=0;i<n;i++)keys*=5;association.resize(keys,UINT32_MAX);
  if(!in||rows[count-1].key!=keys-1)throw std::runtime_error("cache input/root");
 }
 void associated(uint32_t state,int actual_key,const std::array<int,12>&inverse,
   const std::array<std::array<int,4>,24>&outcomes){
  checks++;if(actual_key<0||actual_key>=int(association.size()))throw std::runtime_error("actual key");
  auto&saved=association[actual_key];if(saved==state)return;
  uint64_t binding=(uint64_t(actual_key)<<32)|state;
  if(saved!=UINT32_MAX){multiple_representation_checks++;if(additional.count(binding))return;}
  int row=state/288,action=state%288;if(row>=count)throw std::runtime_error("row");
  int c=action/24,o=action%24,actual[10];for(int i=0,key=actual_key;i<n;i++,key/=5)actual[i]=key%5;
  for(int i=0,key=rows[row].key;i<n;i++,key/=5){
   int value=actual[perm[c][i]],transport=value==4?4:outcomes[o][value];
   if(key%5!=transport)throw std::runtime_error("full actual transported association");
  }
  if(saved==UINT32_MAX)saved=state;else additional.insert(binding);unique++;
 }
 uint32_t step(uint32_t state,int coordinate,int a,const std::array<int,12>&inverse,
   const std::array<std::array<int,4>,24>&outcomes,
   const std::array<std::array<int,24>,24>&omul){
  int row=state/288,c=(state%288)/24,o=state%24;
  int i=perm[inverse[c]][coordinate],key=rows[row].key;for(int j=0;j<i;j++)key/=5;
  if(key%5!=4)throw std::runtime_error("actual transition updates known coordinate");
  auto word=rows[row].words[i][outcomes[o][a]];
  int nextrow=word%65536,action=(word/65536)%512;
  if(nextrow>=count||action>=288)throw std::runtime_error("transition bounds");
  return nextrow*288+24*cmul[c][action/24]+omul[action%24][o];
 }
};
int main(int argc,char**argv){try{
 if(argc!=2)throw std::runtime_error("usage: incremental-cache-check directory");
 fs::path dir=argv[1];auto started=std::chrono::steady_clock::now();
 std::ifstream ci(dir/"actual-incremental-cache.txt");std::string magic;ci>>magic;
 if(magic!="EJM_ACTUAL_INCREMENTAL_CACHE_V1")throw std::runtime_error("cache magic");
 std::array<std::array<int,4>,24>outcomes{};for(auto&r:outcomes)for(auto&v:r)ci>>v;
 std::array<std::array<int,24>,24>omul{};for(auto&r:omul)for(auto&v:r)ci>>v;
 std::array<int,12>inverse{};for(auto&v:inverse)ci>>v;
 LocalCache triangle(ci,10,41294),singleton(ci,9,8689);
 std::string trailing;if(!ci||(ci>>trailing))throw std::runtime_error("cache input length");
 std::ifstream input(dir/"instance.txt");int n,F;int64_t threshold;input>>n>>F>>threshold;
 if(n!=20||F!=32||threshold!=6987435)throw std::runtime_error("instance");
 for(int i=0,v;i<20;i++){input>>v;if(v!=i)throw std::runtime_error("natural Node order");}
 std::array<std::vector<int>,32>scopes;for(int f=0;f<32;f++){
  int arity;input>>arity;if(arity!=(f<16?10:9))throw std::runtime_error("arity");
  scopes[f].resize(arity);for(auto&c:scopes[f])input>>c;
  auto&local=f<16?triangle:singleton;
  for(int g=0;g<20;g++){
   int expected=-1;for(int i=0;i<arity;i++)if(scopes[f][i]==g){if(expected!=-1)throw std::runtime_error("noninjective scope");expected=i;}
   if(local.incidence[g][f%16]!=expected)throw std::runtime_error("actual incidence differs from original scope");
  }
 }
 if(!input)throw std::runtime_error("instance input");
 std::ifstream ai(dir/"actions.txt");int ac;ai>>ac;if(ac!=4608)throw std::runtime_error("action count");
 std::vector<Action>actions(ac);for(auto&a:actions){for(auto&v:a.source)ai>>v;for(auto&v:a.outcome)ai>>v;}
 if(!ai)throw std::runtime_error("action input");
 std::ifstream ck(dir/"stream-checkpoint.txt");std::string binding,dag_name;ck>>magic>>binding>>dag_name;
 if(magic!="EJM_SOURCE_CUT_STREAM_V2")throw std::runtime_error("checkpoint version");
 uint64_t want_nodes,want_bounds,want_syms,want_splits,comparisons;uint32_t count,root;
 ck>>want_nodes>>want_bounds>>want_syms>>want_splits>>comparisons>>count>>root;
 if(root!=1558776||count!=1558777)throw std::runtime_error("complete DAG identity");
 std::ifstream di(dir/dag_name,std::ios::binary);uint32_t dm,dc;di.read((char*)&dm,4);di.read((char*)&dc,4);
 if(dm!=0x454a4d32||dc!=count)throw std::runtime_error("DAG header");
 std::vector<Node>dag(count);for(auto&x:dag){di.read((char*)&x.kind,4);di.read((char*)&x.payload,4);di.read((char*)x.child.data(),16);}
 if(!di||di.peek()!=EOF)throw std::runtime_error("DAG length");
 std::array<int,20>event;event.fill(4);
 State initial{};for(int f=0;f<32;f++){auto&l=f<16?triangle:singleton;initial.value[f]=(l.count-1)*288;initial.lower+=l.rows.back().lower;}
 uint64_t nodes=0,bounds=0,syms=0,splits=0,transitions=0,failed=0,bw=0,sw=0;
 int64_t minimum=std::numeric_limits<int64_t>::max();
 std::function<void(uint32_t,int,const State&)>visit=[&](uint32_t id,int depth,const State&state){
  if(id>=count||depth>20)throw std::runtime_error("reached DAG index");
  nodes++;const auto&x=dag[id];
  if(x.kind==0){
   int64_t direct=0;
   for(int f=0;f<32;f++){
    auto&l=f<16?triangle:singleton;int key=0;
    for(auto p=scopes[f].rbegin();p!=scopes[f].rend();++p)key=5*key+event[*p];
    l.associated(state.value[f],key,inverse,outcomes);direct+=l.rows[state.value[f]/288].lower;
   }
   if(direct!=state.lower)throw std::runtime_error("incremental lower mismatch");
   if(direct<threshold){failed++;if(failed==1){std::ofstream err(dir/"first-incremental-cache-failure.txt");for(auto a:event)err<<a<<' ';err<<"\nlower "<<direct<<'\n';}}
   minimum=std::min(minimum,direct);bounds++;bw+=uint64_t(1)<<(2*(20-depth));return;
  }
  if(x.kind==1){
   if(x.payload>=92160)throw std::runtime_error("cut payload");
   int pivot=x.payload%20;const auto&a=actions[x.payload/20];
   if(event[pivot]==4||event[a.source[pivot]]==4||a.outcome[event[a.source[pivot]]]>=event[pivot])throw std::runtime_error("actual pivot");
   for(int j=0;j<pivot;j++){
    bool fixed=a.source[j]==j;for(int v=0;v<4;v++)fixed=fixed&&a.outcome[v]==v;
    if(!fixed&&(event[j]==4||event[a.source[j]]==4||a.outcome[event[a.source[j]]]!=event[j]))throw std::runtime_error("actual earlier Node");
   }
   syms++;sw+=uint64_t(1)<<(2*(20-depth));return;
  }
  if(x.kind!=2||depth>=20||x.payload!=uint32_t(depth))throw std::runtime_error("actual split");
  splits++;for(int a=0;a<4;a++){
   State child=state;event[depth]=a;
   for(int f=0;f<32;f++){
    auto&l=f<16?triangle:singleton;int coordinate=l.incidence[depth][f%16];
    if(coordinate<0)continue;auto before=state.value[f];
    auto after=l.step(before,coordinate,a,inverse,outcomes,omul);transitions++;
    child.value[f]=after;child.lower+=l.rows[after/288].lower-l.rows[before/288].lower;
   }
   if(x.child[a]>=id)throw std::runtime_error("nondecreasing child");
   visit(x.child[a],depth+1,child);
  }
  event[depth]=4;
 };
 visit(root,0,initial);
 if(nodes!=want_nodes||bounds!=want_bounds||syms!=want_syms||splits!=want_splits||bw+sw!=(uint64_t(1)<<40))throw std::runtime_error("complete counts");
 double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
 std::ofstream result(dir/"actual-incremental-cache-check.json");
 result<<"{\"status\":\"native_actual_incremental_cache_complete_DAG_not_kernel\",\"kernel_accepted\":false,\"complete\":true,\"checked_contexts\":"<<nodes<<",\"bound_leaves\":"<<bounds<<",\"symmetry_leaves\":"<<syms<<",\"splits\":"<<splits<<",\"actual_local_transitions\":"<<transitions<<",\"actual_association_checks\":"<<triangle.checks+singleton.checks<<",\"unique_triangle_partial_row_action_bindings\":"<<triangle.unique<<",\"unique_singleton_partial_row_action_bindings\":"<<singleton.unique<<",\"multiple_representation_checks\":"<<triangle.multiple_representation_checks+singleton.multiple_representation_checks<<",\"minimum_actual_incremental_lower\":"<<minimum<<",\"threshold\":"<<threshold<<",\"failed_bound_leaves\":"<<failed<<",\"bound_worlds\":"<<bw<<",\"symmetry_descent_obligation_worlds\":"<<sw<<",\"elapsed_seconds\":"<<elapsed<<"}\n";
 std::cout<<"actual incremental cache complete contexts="<<nodes<<" min="<<minimum<<" failed="<<failed<<" seconds="<<elapsed<<'\n';
 return failed?2:0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
