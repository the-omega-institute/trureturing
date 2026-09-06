// Complete finite-domain proof producer for the four-transient-state relaxation.
// Canonical outputs G=(2,1,3,g), g in {1,2,3}; E runs over all 16 Boolean maps.
// Names 0,1,2 are fixed by the distinct-output observations n=0,1,26.
// No restriction is imposed on the number of previous-zero states.
// All gap maps are arbitrary total maps. B/L certificates are replayable.
#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using Clock=std::chrono::steady_clock;
std::ofstream proof;
struct Row{int n,d,tail;std::vector<int> gaps;};
struct Node{std::map<int,int> next;std::vector<std::pair<int,int>> obs;};
struct Edge{int p,c,h;};
struct Timeout{};
struct Search {
 std::vector<int> dom;std::vector<Edge> edges;std::vector<std::vector<int>> watch;
 std::vector<std::pair<int,int>> trail;std::deque<int> queue;std::vector<bool> queued;
 std::vector<int> baseWeights;int hcount;long long branches=0,conflicts=0;
 Clock::time_point start;double limit;
 Search(std::vector<int> d,std::vector<Edge> e,int hc,Clock::time_point st,double lim):dom(std::move(d)),edges(std::move(e)),watch(dom.size()),queued(edges.size(),false),baseWeights(hc),hcount(hc),start(st),limit(lim){
  for(int i=0;i<(int)edges.size();++i){auto x=edges[i];watch[x.p].push_back(i);watch[x.c].push_back(i);for(int j=0;j<4;++j)watch[x.h+j].push_back(i);}
  for(int h=0;h<hcount;++h)baseWeights[h]=watch[h].size();
 }
 void enqueue(int e){if(!queued[e]){queue.push_back(e);queued[e]=true;}}
 bool narrow(int v,int m){int n=dom[v]&m;if(n==dom[v])return n!=0;trail.emplace_back(v,dom[v]);dom[v]=n;for(int e:watch[v])enqueue(e);return n!=0;}
 bool propagate(){
  while(!queue.empty()){
   int i=queue.front();queue.pop_front();queued[i]=false;auto e=edges[i];int pd=dom[e.p],cd=dom[e.c],np=0,nc=0;
   for(int p=0;p<4;++p)if(pd&(1<<p)){int inter=dom[e.h+p]&cd;if(inter){np|=1<<p;nc|=inter;}}
   if(!narrow(e.p,np)||!narrow(e.c,nc))return false;
   if(__builtin_popcount((unsigned)np)==1){int p=__builtin_ctz((unsigned)np);if(!narrow(e.h+p,dom[e.c]))return false;}
  }
  return true;
 }
 void rollback(std::size_t n){while(!queue.empty()){queued[queue.front()]=false;queue.pop_front();}while(trail.size()>n){auto [v,d]=trail.back();trail.pop_back();dom[v]=d;}}
 bool dfs(){
  ++branches;if((branches&15)==0&&std::chrono::duration<double>(Clock::now()-start).count()>limit)throw Timeout{};
  if(!propagate()){if(proof)proof<<"L\n";++conflicts;return false;}
  int choice=-1,score=-1;
  std::vector<int> weights(hcount,0);
  for(auto e:edges){int pd=dom[e.p],cd=dom[e.c];int factor=(__builtin_popcount((unsigned)pd)==1?16:4)*(5-__builtin_popcount((unsigned)cd));for(int p=0;p<4;++p)if(pd&(1<<p))weights[e.h+p]+=factor;}
  for(int h=0;h<hcount;++h){int n=__builtin_popcount((unsigned)dom[h]);if(n>1){int s=weights[h]*(n==2?3:(n==3?2:1));if(s>score){score=s;choice=h;}}}
  if(choice<0){if(proof)proof<<"S\n";return true;}
  int choices=dom[choice];auto mark=trail.size();if(proof)proof<<"B "<<choice<<" "<<choices<<"\n";
  for(int v=0;v<4;++v)if(choices&(1<<v)){
   if(narrow(choice,1<<v)&&dfs())return true;
   rollback(mark);
  }
  return false;
 }
};
int main(int argc,char**argv){
 if(argc<2){std::cerr<<"usage: gap4_produce rows.tsv seconds proof.txt case_begin case_end\n";return 2;}
 double limit=argc>=3?std::stod(argv[2]):35;auto start=Clock::now();if(argc>=4 && std::string(argv[3])!="-"){proof.open(argv[3]);proof<<"gap4-proof-v1\n";}
 std::ifstream f(argv[1]);if(!f){std::cerr<<"Cannot read rows\n";return 2;}
 int nodeOne=-1,node26=-1;std::vector<Row> rows;std::vector<Node> nodes(1);std::map<int,int> gaps;
 std::string line;while(std::getline(f,line)){
  std::istringstream ss(line);Row r;if(!(ss>>r.n>>r.d>>r.tail))continue;int g;while(ss>>g)r.gaps.push_back(g);
  if(r.tail>1)continue;
  if(r.tail==0&&(r.d<1||r.d>3)){std::cerr<<"Invalid terminal label\n";return 2;}
  if(r.tail==1&&(r.d<0||r.d>1)){std::cerr<<"Invalid one-zero label\n";return 2;}
  int v=0;for(int g:r.gaps){if(!gaps.count(g)){int k=gaps.size();gaps[g]=k;}if(!nodes[v].next.count(g)){int k=nodes.size();nodes[v].next[g]=k;nodes.emplace_back();}v=nodes[v].next[g];}
  nodes[v].obs.emplace_back(r.tail,r.d);rows.push_back(r);if(r.n==1)nodeOne=v;if(r.n==26)node26=v;
 }
 int hc=4*gaps.size();std::vector<Edge> edges;
 for(int i=0;i<(int)nodes.size();++i)for(auto [g,j]:nodes[i].next)edges.push_back({hc+i,hc+j,4*gaps[g]});
 long long branches=0,conflicts=0;int finished=0;
 try{
  for(int extra=1;extra<=3;++extra) for(int pattern=0;pattern<16;++pattern){if(argc>=6 && (16*(extra-1)+pattern<std::stoi(argv[4]) || 16*(extra-1)+pattern>=std::stoi(argv[5])))continue;if(proof)proof<<"P "<<extra<<" "<<pattern<<"\n";
   std::vector<int>d(hc+nodes.size(),15);d[hc]=1; int gout[4]={2,1,3,extra};
   for(int i=0;i<(int)nodes.size();++i)for(auto [tail,out]:nodes[i].obs){int mask=0;if(tail==0){for(int t=0;t<4;++t)if(gout[t]==out)mask|=1<<t;}else for(int t=0;t<4;++t)if(((pattern>>t)&1)==out)mask|=1<<t;d[hc+i]&=mask;}
   if(nodeOne>=0)d[hc+nodeOne]&=2;if(node26>=0)d[hc+node26]&=4;
   if(std::find(d.begin(),d.end(),0)!=d.end()){if(proof)proof<<"L\n";++finished;continue;}
   Search s(d,edges,hc,start,limit);for(int i=0;i<(int)edges.size();++i)s.enqueue(i);
   bool sat=false;try{sat=s.dfs();}catch(Timeout&){branches+=s.branches;conflicts+=s.conflicts;throw;}
   branches+=s.branches;conflicts+=s.conflicts;
   if(sat){std::cerr<<"SAT extra="<<extra<<" pattern="<<pattern<<"\n";std::cout<<"{\"status\":\"SAT\",\"E1_pattern\":"<<pattern<<",\"branches\":"<<branches<<"}\n";return 0;}
   ++finished;std::cerr<<"finished "<<extra<<" "<<pattern<<" branches "<<branches<<" conflicts "<<conflicts<<" seconds "<<std::chrono::duration<double>(Clock::now()-start).count()<<"\n";
  }
 }catch(Timeout&){std::cout<<"{\"status\":\"UNKNOWN\",\"completed_output_cases\":"<<finished<<",\"branches\":"<<branches<<",\"conflicts\":"<<conflicts<<"}\n";return 0;}
 std::cout<<"{\"status\":\"UNSAT\",\"completed_output_cases\":"<<finished<<",\"branches\":"<<branches<<",\"conflicts\":"<<conflicts<<",\"rows\":"<<rows.size()<<",\"gap_letters\":"<<gaps.size()<<",\"trie_nodes\":"<<nodes.size()<<",\"seconds\":"<<std::chrono::duration<double>(Clock::now()-start).count()<<"}\n";
}
