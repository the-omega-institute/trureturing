#!/usr/bin/env python3
"""Check the rational constants and local hypotheses of a robust MUB gap.

Reuses the exact residual evaluator and interval primitives. It does not
consume a previous PASS. The full global sublevel traversal is a separate
obligation; use audit_real_x_sublevel_rows.py to replay that obligation.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, subprocess
from fractions import Fraction as F
from pathlib import Path
import check_real_x_global_cover as old

I,C=old.I,old.C

def require(test: bool, message: str) -> None:
    if not test: raise ValueError(message)

def digest(p:Path)->str:return hashlib.sha256(p.read_bytes()).hexdigest()

HELPER=r'''
#define main previous_main
#include "check_real_x_global_cover.cpp"
#undef main
int main(int argc,char**argv){try{
 if(argc!=5)throw runtime_error("usage: guards centers matrix_bounds output enclosure");
 interval_seed(argv[2]);load_roots(argv[1]);ll maxq=0,maxc=0;
 for(auto &root:roots){
  for(auto &t:root.x){ll c=mid(t);t=I(checked((wide)c-(ONE>>12)),checked((wide)c+(ONE>>12)));}
  Kr k;if(!krawczyk(root.x,root.mask,k)||k.contraction>=ONE/2)throw runtime_error("q>=1/2");
  for(int j=0;j<5;j++)if(!strictsub(k.k[j],root.x[j]))throw runtime_error("no root inclusion");
  Box m;for(int j=0;j<5;j++)m[j]=I::point(mid(root.x[j]));
  I f[5],J[5][5],A[5][5];eval(m,root.mask,f,J);
  if(!propose(J,A))throw runtime_error("no preconditioner");
  for(int i=0;i<5;i++){ll s=0;for(int j=0;j<5;j++)s=checked((wide)s+absmax(A[i][j]));maxc=max(maxc,s);}
  maxq=max(maxq,k.contraction);
 }
 if(maxc>(wide)6*ONE)throw runtime_error("preconditioner exceeds conservative bound");
 dump_roots(argv[4]);ofstream out(argv[3]);if(!out)throw runtime_error("output failure");
 out<<"{\"guards\":60,\"scale\":"<<ONE<<",\"max_q\":"<<maxq<<",\"max_C\":"<<maxc<<"}\n";
 return 0;
}catch(exception const&e){cerr<<e.what()<<'\n';return 1;}}
'''

def run(datafile:Path,centers:Path,out:Path)->dict:
 require(__debug__,'do not use Python -O with the reused interval implementation')
 out.mkdir(parents=True,exist_ok=True)
 delta=F(1,2**24);epsilon=F(1,2**19);eta=F(1,2**18)
 b=C.point(F(-3,5),F(4,5));e=C(I.point(F(-2,5)),old.base.sqrtI(21)/5)
 vals=['40'];scale=2**40
 for i in range(6):
  for j in range(6):
   if i<3 and j<3:z=b if i==j else C.point(1)
   elif i<3:z=e if i==j-3 else C.point(1)
   elif j<3:z=e.conj() if i-3==j else C.point(1)
   else:z=-b.conj() if i==j else C.point(-1)
   row=[]
   for v in (z.re,z.im):
    a,h=v.lo-delta,v.hi+delta
    row.extend([a.numerator*scale//a.denominator,-((-h.numerator*scale)//h.denominator)])
   vals.append(' '.join(map(str,row)))
 bounds=out/'ambient_bounds.txt';bounds.write_text('\n'.join(vals)+'\n')
 helper=out/'guard_constants.cpp';helper.write_text(HELPER)
 binary=out/'guard_constants'
 core=Path(old.__file__).with_suffix('.cpp')
 subprocess.run(['g++','-std=c++17','-O2','-Wall','-Wextra','-Werror','-I',str(core.parent),str(helper),'-o',str(binary)],check=True)
 local=out/'local.json';raysfile=out/'root_enclosures.txt'
 local.unlink(missing_ok=True);raysfile.unlink(missing_ok=True)
 subprocess.run([str(binary),str(centers),str(bounds),str(local),str(raysfile)],check=True)
 loc=json.loads(local.read_text());require(loc['guards']==60 and 2*loc['max_q']<loc['scale'],'bad contraction')
 require(loc['max_C']<=6*loc['scale'],'bad preconditioner bound')
 data=json.loads(datafile.read_text());canonical=set(data['canonical_vertices']);colors=data['noncanonical_colors'];edges={tuple(e) for e in data['allowed_edges']}
 require(len(canonical)==6 and canonical<=set(range(60)),'bad canonical set')
 require(len(edges)==114 and len(edges)==len(data['allowed_edges']) and len(colors)==60,'bad graph shape')
 require(all(0<=i<j<60 for i,j in edges),'bad edge endpoint')
 require(all(colors[i] in (0,1) for i in range(60) if i not in canonical),'bad colors')
 require(all((i in canonical and j in canonical) or (i not in canonical and j not in canonical and colors[i]!=colors[j]) for i,j in edges),'not an exclusion supergraph')
 lines=raysfile.read_text().splitlines();require(len(lines)==61 and lines[0]=='60','bad rays')
 rays={}
 for line in lines[1:]:
  v=list(map(int,line.split()));require(len(v)==12,'bad enclosure')
  idx,mask=v[:2];require(idx not in rays and 0<=idx<60 and 0<=mask<32,'bad ray label')
  X=[I(F(v[2+2*j],scale),F(v[3+2*j],scale)) for j in range(5)]
  rays[idx]=old.base.phase_map(X,[0]+[2*((mask>>j)&1) for j in range(5)])
 require(set(rays)==set(range(60)),'incomplete rays')
 lower=F(1);count=0
 for i,j in itertools.combinations(range(60),2):
  ip=sum((a.conj()*b for a,b in zip(rays[i],rays[j])),C.point())/6;n=ip.normsq()
  require(n.hi<1,'distinctness not certified')
  if (i,j) not in edges:
   require(n.lo>F(1,10**8),'forbidden pair not separated');count+=1;lower=min(lower,n.lo)
 require(count==1656,'wrong nonedge count')
 # Conservative constants are fixed in the proposed mathematical theorem.
 shift=epsilon+30*delta+36*delta**2
 r=24*epsilon;gamma=F(1,10000);sigma=F(1,200000)
 tests={
  'approximate_root_enters_base_sublevel':shift<eta,
  'small_residual_amplitude_bound':6+epsilon<F(25,4),
  'nonedges_stay_nonorthogonal':2*r+sigma<gamma,
  'same_label_not_internal_orthogonal':1-2*r>sigma,
  'shared_label_overlap_large':(1-2*r)**2>F(9998,10000),
  'potential_controls_internal_tolerance':epsilon<sigma,
  'cross_target_conflicts_with_shared_label':F(1,6)+epsilon<F(9998,10000)}
 require(all(tests.values()),'a rational margin failed')
 # Deliberately overoptimistic residual tolerances must be rejected.
 corrupt=F(1,2**14)
 require(not(2*(24*corrupt)+sigma<gamma),'negative tolerance test failed')
 result={
  'schema':'mub-robust-candidate-gap-constants-v1','status':'PASS',
  'scope':'local ambient guards, graph inequalities, and rational constants checked; full sublevel cover is a separate premise',
  'entry_radius':str(delta),'base_sublevel':str(eta),'candidate_residual_tolerance':str(epsilon),
  'preconditioner_bound':'6','guard_contraction_bound':'1/2',
  'actual_local':loc,'root_ket_distance_bound':str(r),
  'internal_overlap_tolerance':str(sigma),'nonedge_amplitude_lower':'1/10000',
  'candidate_merit_lower_bound':str(epsilon**2),'candidate_merit_exponent':38,
  'candidate_domain':'two six-tuples of normalized vectors with exactly equal coordinate moduli 1/sqrt(6)',
  'tests':tests,'certified_nonedges':count,'minimum_nonedge_squared_lower':str(lower),
  'negative_test_large_tolerance_rejected':True,
  'global_sublevel_replayed_here':False,'lean_kernel_verified':False,
  'hashes':{'driver':digest(Path(__file__)),'root_core':digest(core),'centers':digest(centers),'graph_input':digest(datafile),'ambient_bounds':digest(bounds),'root_enclosures':digest(raysfile)}}
 (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 return result

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('graph_input',type=Path);p.add_argument('centers',type=Path);p.add_argument('--output',required=True,type=Path)
 a=p.parse_args();print(json.dumps(run(a.graph_input,a.centers,a.output),indent=2))
