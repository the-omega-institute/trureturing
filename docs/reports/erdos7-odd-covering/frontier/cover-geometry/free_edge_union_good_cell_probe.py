#!/usr/bin/env python3
"""Three preregistered coherent central layouts for free within-edge endpoints.
Exact finite good-cell deletion and full512-cost gate; no general-phase result,
no Lean verification, and no large layout search.
"""
import argparse,hashlib,json
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
QS=(7,11,13,17,19)
EDGES=list(combinations(range(5),2))
PIN='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
W=[F()if l==3 else F(1,5)for l in range(6)]
V=[F()if m==5 else F(1,19)for m in range(20)]
CELLS=[(l,m)for l,m in product(range(6),range(20))if W[l]and V[m]and(l//3,m//5)!=(0,0)]
STAR=(0,2,0,2,0,10)
LAYOUTS=[('A_source_null_decorations',(2,4,0,0)),('B_aligned_decorations',(0,2,0,2)),('C_opposite_decorations',(1,1,1,1))]
CHECKS=[]
def check(name,value):
 if not value:raise ArithmeticError(name)
 CHECKS.append(name)
def matching(Z,beta):
 M=[F()]*32;M[0]=F(1);b={e:x for e,x in zip(EDGES,beta)}
 for S in range(1,32):
  q=(S&-S).bit_length()-1;rest=S^(1<<q);M[S]=Z[q]*M[rest]
  for s in range(5):
   if rest>>s&1:M[S]-=b[min(q,s),max(q,s)]*M[rest^(1<<s)]
 return M
def shearer(u):
 def value(mask):
  es=[e for e in range(10)if mask>>e&1]
  return 1-sum((u[e]for e in es),F())+sum((u[e]*u[f]for e,f in combinations(es,2)if set(EDGES[e]).isdisjoint(EDGES[f])),F())
 for q in range(5):
  mask=sum(1<<e for e,pair in enumerate(EDGES)if q in pair);v=value(mask)
  if v<=0:return False,dict(reason='vertex_clique',mask=mask,polynomial=str(v))
 full=value(1023)
 if full<=0:return False,dict(reason='full_polynomial',mask=1023,polynomial=str(full))
 disjoint=max(sum((u[f]for f in range(10)if set(e).isdisjoint(EDGES[f])),F())for e in EDGES)
 if disjoint<1:return True,dict(reason='full_positive_and_monotone',full=str(full),disjoint_sum=str(disjoint))
 vals=[value(mask)for mask in range(1024)];i=min(range(1024),key=vals.__getitem__)
 return vals[i]>0,dict(reason='all1024',mask=i,polynomial=str(vals[i]))
def quinary(h):
 out=[F()]*4
 for j in range(4):
  root=F()
  for k in range(5):
   m=5*j+k
   if not V[m]:continue
   x=V[m]*h[m];root+=x;out[2]=max(out[2],x);out[3]=max(out[3],F(4,5)*h[m])
  out[0]+=root;out[1]=max(out[1],root)
 return out
def screens(h):
 out=[F()]*16;roots=[[F()]*20 for _ in range(2)]
 for l in range(6):
  if not W[l]:continue
  v=quinary(h[l])
  for e in range(4):out[8+e]=max(out[8+e],W[l]*v[e]);out[12+e]=max(out[12+e],v[e])
  for m in range(20):roots[l//3][m]+=W[l]*h[l][m]
 v=quinary([roots[0][m]+roots[1][m]for m in range(20)]);a=quinary(roots[0]);b=quinary(roots[1])
 for e in range(4):out[e]=v[e];out[4+e]=max(F(),a[e],b[e])
 return out
def direct_menu(n,block,weights,zero,deep,mode):
 if mode==0:return[weights]
 if mode==1:return[[weights[k]if k//block==j else F()for k in range(n)]for j in range(n//block)]+[[F()]*n]
 return[[(weights[k]if mode==2 else deep)if k==leaf else F()for k in range(n)]for leaf in range(n)if leaf!=zero]+[[F()]*n]
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=Path(__file__).with_name('actual_pair_activation_certificate.json'));ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=ap.parse_args()
 raw=args.source.read_bytes();check('full_coefficient_pin',hashlib.sha256(raw).hexdigest()==PIN);data=json.loads(raw);c=F(data['constants']['continuation_c']);g=1-c;co=[g*F(l)+c*F(w)for l,w in zip(data['complete_coefficients']['loss'],data['complete_coefficients']['weighted_nonunit_query'])];check('all512_nonnegative_costs',len(co)==512 and min(co)>=0)
 r=[F(1,q-1)for q in QS];a=[F(1,q*(q-2))for q in QS];kappa=[r[q]*r[s]+a[q]*r[s]+r[q]*a[s]for q,s in EDGES]
 rows=[sum(W[3*i:3*i+3],F())for i in range(2)];cols=[sum(V[5*j:5*j+5],F())for j in range(4)];masked=rows[0]*cols[0];mu=1-masked
 results=[]
 for name,(R,C,I,J)in LAYOUTS:
  H=[[[F()]*20 for _ in range(6)]for T in range(32)];cells=[];intB=F()
  for l,m in CELLS:
   B=1+int(l//3==R)+int(m//5==C)+int((l//3,m//5)==(I,J));intB+=W[l]*V[m]*B
   Z=[1-(r[q]+a[q])*(int(l//3==STAR[0])+int(m//5==STAR[1]))-r[q]*(int((l//3,m//5)==STAR[2:4])+int(l==STAR[4])+int(m==STAR[5]))for q in range(5)]
   beta=[x*B for x in kappa];u=[b/(Z[q]*Z[s])for b,(q,s)in zip(beta,EDGES)];good,evidence=shearer(u)
   if good:
    M=matching(Z,beta);check(name+f'_positive_response_{l}_{m}',min(M)>0)
    for T in range(32):H[T][l][m]=M[31^T]
   cells.append(dict(cell=[l,m],activation_count=B,good=good,shearer=evidence))
  rowmass=rows[R]-(masked if R==0 else 0)if R<2 else F();colmass=cols[C]-(masked if C==0 else 0)if C<4 else F();point=rows[I]*cols[J]if(I,J)!=(0,0)else F()
  check(name+'_global_activation_identity',intB==mu+rowmass+colmass+point)
  mass=sum((W[l]*V[m]*H[0][l][m]for l,m in CELLS),F());debit=F();scr=[]
  for T in range(32):
   s=screens(H[T]);scr.append(s);debit+=sum((co[32*mode+T]*s[mode]for mode in range(16)),F())
  for T in (0,31):
   for e3,e5 in product(range(4),repeat=2):
    menus3=direct_menu(6,3,W,3,F(1),e3);menus5=direct_menu(20,5,V,5,F(4,5),e5)
    direct=max(sum((x[l]*y[m]*H[T][l][m]for l,m in CELLS),F())for x,y in product(menus3,menus5))
    check(name+f'_generic_menu_{T}_{e3}_{e5}',direct==scr[T][4*e3+e5])
  gate=g*mass-debit;bad=[row['cell']for row in cells if not row['good']];goodmass=sum((W[l]*V[m]for l,m in CELLS if [l,m]not in bad),F())
  results.append(dict(name=name,star_template=STAR,all_edges_all_exponent_groups_roles=[R,C,I,J],unmasked_central_mass=str(mu),integrated_activation_count=str(intB),good_cells=len(CELLS)-len(bad),bad_cells=bad,good_central_mass=str(goodmass),retained_mass=str(mass),complete_debit=str(debit),gate=str(gate),gate_float=float(gate),positive=gate>0,cell_evidence=cells))
  print(name,'good',len(CELLS)-len(bad),'gate',gate,float(gate),flush=True)
 answer=dict(scope=__doc__,source_sha256=PIN,weights3=list(map(str,W)),weights5=list(map(str,V)),results=results,checks=CHECKS,check_count=len(CHECKS),new_lean_verification=False,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 args.output.write_text(json.dumps(answer,indent=2)+'\n')
if __name__=='__main__':main()
