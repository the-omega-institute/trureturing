// Exact sublevel-set extension of the existing root-cover verifier.
// This is a computational certificate, not a Lean kernel proof.
// The original evaluator, interval operations, root data, and chart maps are reused.
#define main original_root_cover_main
#include "check_real_x_global_cover.cpp"
#undef main

// If |f_a(x)| <= epsilon, then the usual Krawczyk image must be
// enlarged by C[-epsilon,epsilon]^5. No uninflated contraction is used
// on the sublevel traversal. Root isolation in load_roots still uses eta=0.
bool sublevel_krawczyk(Box const& X, int mask, ll epsilon, Kr& out) {
  try {
    Box m;
    for (int j=0;j<5;j++) m[j]=I::point(mid(X[j]));
    I f[5], J[5][5], f0[5], J0[5][5], Cpre[5][5];
    eval(m,mask,f0,J0);
    if (!propose(J0,Cpre)) return false;
    eval(X,mask,f,J);
    out.contraction=0;
    for(int i=0;i<5;i++) {
      out.k[i]=m[i];
      for(int a=0;a<5;a++) out.k[i]=out.k[i]-Cpre[i][a]*f0[a];
      ll row=0;
      for(int j=0;j<5;j++) {
        I err=I(i==j);
        for(int a=0;a<5;a++) err=err-Cpre[i][a]*J[a][j];
        row=checked((wide)row+absmax(err));
        out.k[i]=out.k[i]+err*(X[j]-m[j]);
      }
      // Essential extra summand. Removing this changes the theorem to root-only coverage.
      for(int a=0;a<5;a++) out.k[i]=out.k[i]+Cpre[i][a]*I(-epsilon,epsilon);
      out.contraction=max(out.contraction,row);
    }
    return true;
  } catch(overflow_error const&) { return false; }
}

int main(int argc,char** argv) {
 try {
  if(argc!=7 && argc!=8) throw runtime_error(
    "usage: barrier centers chart max_nodes epsilon_bits guard_radius_bits report [matrix_bounds]");
  int mask=stoi(argv[2]),eb=stoi(argv[4]),gb=stoi(argv[5]);
  long cap=stol(argv[3]);
  if(mask<0||mask>32||cap<1||eb<1||eb>39||gb<1||gb>16)
    throw runtime_error("invalid chart, budget, or exponent");
  ll epsilon=1LL<<(40-eb),guard=1LL<<(40-gb);
  seed(); if(argc==8) interval_seed(argv[7]);
  load_roots(argv[1]);
  ll max_root_contraction=0;
  for(auto& root: roots) {
    for(auto& t: root.x) { ll center=mid(t); t=I(checked((wide)center-guard),checked((wide)center+guard)); }
    Kr q;
    if(!krawczyk(root.x,root.mask,q)||q.contraction>=ONE)
      throw runtime_error("enlarged guard is not a uniqueness neighborhood");
    for(int j=0;j<5;j++) if(!strictsub(q.k[j],root.x[j]))
      throw runtime_error("enlarged guard does not strictly contain its root image");
    max_root_contraction=max(max_root_contraction,q.contraction);
  }
  if(mask==32) {
    dump_roots(string(argv[6])+".roots");
    ofstream local(argv[6]);if(!local)throw runtime_error("cannot write local report");
    local<<"{\"status\":\"LOCAL_GUARDS_VERIFIED\",\"guards\":60,\"guard_radius_bits\":"<<gb
      <<",\"max_guard_contraction_dyadic\":"<<max_root_contraction
      <<",\"dyadic_bits\":40,\"lean_kernel_verified\":false}\n";
    return 0;
  }
  Box initial;for(auto& t:initial)t=I(-ONE,ONE);
  vector<Node> pending{{initial,0}};
  long nodes=0,excluded=0,known=0,contracted=0,unresolved=0;
  int maxdepth=0;
  auto begin=chrono::steady_clock::now();
  while(!pending.empty()&&nodes<cap) {
    auto [X,depth]=pending.back();pending.pop_back();++nodes;maxdepth=max(maxdepth,depth);
    if(in_known(X,mask)>=0) {++known;continue;}
    I f[5]; eval(X,mask,f,nullptr);
    bool no_sublevel=false;
    for(auto const& value:f) no_sublevel|=(value.l>epsilon||value.h<-epsilon);
    if(no_sublevel){++excluded;continue;}
    Kr q;
    if(sublevel_krawczyk(X,mask,epsilon,q)) {
      bool empty=false;for(int j=0;j<5;j++)empty|=(q.k[j].h<X[j].l||q.k[j].l>X[j].h);
      if(empty){++excluded;continue;}
      Box Y;bool shrink=false;
      for(int j=0;j<5;j++) {
        Y[j]=I(max(X[j].l,q.k[j].l),min(X[j].h,q.k[j].h));
        shrink|=((wide)5*(Y[j].h-Y[j].l)<(wide)3*(X[j].h-X[j].l));
      }
      if(in_known(Y,mask)>=0){++known;continue;}
      if(shrink){pending.push_back({Y,depth+1});++contracted;continue;}
    }
    int j=0;for(int k=1;k<5;k++)if(X[k].h-X[k].l>X[j].h-X[j].l)j=k;
    ll m=mid(X[j]);
    if(depth>180||m<=X[j].l||m>=X[j].h){++unresolved;continue;}
    Box Y=X;Y[j].l=m;X[j].h=m;pending.push_back({Y,depth+1});pending.push_back({X,depth+1});
  }
  bool pass=pending.empty()&&unresolved==0;
  double secs=chrono::duration<double>(chrono::steady_clock::now()-begin).count();
  string report=string("{\"status\":\"")+(pass?"SUBLEVEL_COVERED":"INCOMPLETE")+
   "\",\"chart\":"+to_string(mask)+",\"nodes\":"+to_string(nodes)+
   ",\"excluded\":"+to_string(excluded)+",\"guard_leaves\":"+to_string(known)+
   ",\"contracted\":"+to_string(contracted)+",\"unresolved\":"+to_string(unresolved)+
   ",\"pending\":"+to_string(pending.size())+",\"max_depth\":"+to_string(maxdepth)+
   ",\"epsilon_bits\":"+to_string(eb)+",\"guard_radius_bits\":"+to_string(gb)+
   ",\"max_guard_contraction_dyadic\":"+to_string(max_root_contraction)+
   ",\"dyadic_bits\":40,\"seconds\":"+to_string(secs)+
   ",\"lean_kernel_verified\":false}";
  ofstream out(argv[6]);if(!out)throw runtime_error("cannot write report");out<<report<<'\n';
  cout<<report<<'\n';return pass?0:2;
 } catch(exception const& e){cerr<<"FAIL CLOSED: "<<e.what()<<'\n';return 1;}
}
