#!/usr/bin/env python3
"""One coherent extension of Report626's registered worst conditional root layout.

Actual restricted pure laws, Report629's full twelve-label free-endpoint caps,
one shared thinning, all32 responses and all512 costs. Standard-library exact
verification; solver output is not proof. No general-layout or Lean claim.
"""
import argparse, hashlib, json
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path

QS=(7,11,13,17,19)
EDGES=tuple(combinations(range(5),2))
ROOTS=((0,3,0,3),(1,2,0,2),(1,2,0,2),(1,1,0,1),(1,1,0,1))
LEAVES=((0,15),(5,11),(5,11),(5,6),(5,6))
PAIR_CODES=(27,27,27,27,50,50,50,50,50,41)
W=tuple(F(n,9)for n in (2,2,2,0,1,2))
V=tuple(F(n,75)for n in (4,4,4,4,4,0,4,4,4,4,3,4,4,4,4,4,4,4,4,4))
CELLS=tuple((l,m)for l,m in product(range(6),range(20))if W[l]and V[m]and(l//3,m//5)!=(0,0))
COEFF_PIN='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f'
# Historical selection provenance only: this producer does not read that file.
SELECTION_SOURCE626_SHA256='b8c38f05cbcd65607e25bc138ecc5a20961cd5bb786b18ad41df5583986bb1a4'
ALPHA=F(2673,110656)
THETA_DEN=2**24
THETA_NUMS=(15364270, 14186737, 14186737, 14186737, 16127671, 16127671, 16127671, 16127671, 16127671, 0, 0, 0, 0, 0, 15364270, 14186737, 14186737, 14186737, 16127671, 16127671, 16127671, 16127671, 16127671, 0, 10780734, 10780734, 10780734, 10773780, 15364270, 14186737, 14186737, 14186737, 16127671, 16127671, 16127671, 16127671, 16127671, 0, 10780734, 10780734, 10780734, 10773780, 11564512, 499837, 11564512, 11564512, 11564512, 14616745, 13465477, 13465477, 13465477, 13956016, 13464518, 13956016, 13956016, 13956016, 0, 16039474, 16039474, 16039474, 16039474, 15361506, 15361506, 15361506, 15361506, 6529186, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216, 16777216)
CHECKS=[]
def check(name,p):
 if not p:raise ArithmeticError(name)
 CHECKS.append(name)
def enc(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):enc(v)for k,v in x.items()}
 if isinstance(x,(list,tuple)):return[enc(v)for v in x]
 return x
def matching(Z,beta):
 H=[F()]*32;H[0]=F(1);b=dict(zip(EDGES,beta))
 for S in range(1,32):
  q=(S&-S).bit_length()-1;rest=S^(1<<q);H[S]=Z[q]*H[rest]
  for s in range(5):
   if rest>>s&1:H[S]-=b[min(q,s),max(q,s)]*H[rest^(1<<s)]
 return H
def strict(u):
 def val(mask):
  es=[e for e in range(10)if mask>>e&1]
  return 1-sum((u[e]for e in es),F())+sum((u[e]*u[f]for e,f in combinations(es,2)if set(EDGES[e]).isdisjoint(EDGES[f])),F())
 # A negative clique is already a complete rejection certificate.
 for q in range(5):
  mask=sum(1<<e for e,pair in enumerate(EDGES)if q in pair);v=val(mask)
  if v<=0:return False,dict(kind='nonpositive_induced',mask=mask,value=v)
 full=val(1023)
 if full<=0:return False,dict(kind='nonpositive_induced',mask=1023,value=full)
 dis=max(sum((u[f]for f in range(10)if set(e).isdisjoint(EDGES[f])),F())for e in EDGES)
 if dis<1:return True,dict(kind='full_positive_monotone',full=full,disjoint_sum=dis)
 vals=[val(mask)for mask in range(1024)];k=min(range(1024),key=vals.__getitem__)
 return vals[k]>0,dict(kind='all1024',minimum_mask=k,minimum=vals[k])
def one_menus(n,block,weights,deep,mode):
 if mode==0:return [tuple(weights)]
 if mode==1:return [tuple(weights[k]if k//block==j else F()for k in range(n))for j in range(n//block)]+[(F(),)*n]
 return [tuple((weights[k]if mode==2 else deep)if k==leaf else F()for k in range(n))for leaf in range(n)if weights[leaf]]+[(F(),)*n]
def make_model(source):
 raw=source.read_bytes();check('full_coefficient_pin',hashlib.sha256(raw).hexdigest()==COEFF_PIN);data=json.loads(raw)
 c=F(data['constants']['continuation_c']);g=1-c;co=[g*F(x)+c*F(y)for x,y in zip(data['complete_coefficients']['loss'],data['complete_coefficients']['weighted_nonunit_query'])]
 check('all512_costs',len(co)==512 and min(co)>=0 and co[0]==0)
 check('actual_central_probabilities',sum(W)==sum(V)==1 and min(W+V)>=0 and max(W)<=F(2,9)and max(V)<=F(4,75))
 check('positive_central_outside15',len(CELLS)==80 and all(W[l]*V[m]>0 and(l//3,m//5)!=(0,0)for l,m in CELLS))
 check('ten_fixed_global_pair_roles',PAIR_CODES==tuple(32*ROOTS[q][0]+8*ROOTS[q][1]+4*ROOTS[q][2]+ROOTS[q][3]for q,s in EDGES))
 H=[[F()]*80 for _ in range(32)];records=[];r=[F(1,q-1)for q in QS];a=[F(1,q*(q-2))for q in QS]
 for ci,(l,m)in enumerate(CELLS):
  Z=[1-(r[q]+a[q])*(int(l//3==R)+int(m//5==C))-r[q]*(int((l//3,m//5)==(I,J))+int(l==L)+int(m==M))for q,((R,C,I,J),(L,M))in enumerate(zip(ROOTS,LEAVES))]
  check('positive_star_mass',min(Z)>0)
  beta=[]
  for q,s in EDGES:
   R,C,I,J=ROOTS[q];B=1+int(l//3==R)+int(m//5==C)+int((l//3,m//5)==(I,J))
   beta.append((r[q]*r[s]+a[q]*r[s]+r[q]*a[s])*B)
  good,evidence=strict([b/(Z[q]*Z[s])for b,(q,s)in zip(beta,EDGES)])
  if good:
   values=matching(Z,beta);check('all32_response_positive',min(values)>0)
   for T in range(32):H[T][ci]=values[31^T]
  records.append(dict(cell=[l,m],Z=Z,beta=beta,good=good,strict=evidence))
 menus=[]
 for e3,e5 in product(range(4),repeat=2):
  seen=set();rows=[]
  for x,y in product(one_menus(6,3,W,F(1),e3),one_menus(20,5,V,F(4,5),e5)):
   row=tuple((i,x[l]*y[m])for i,(l,m)in enumerate(CELLS)if x[l]*y[m])
   if row not in seen:seen.add(row);rows.append(row)
  menus.append(rows)
 active=[j for j,x in enumerate(co)if x];check('511_complete_query_rows',len(active)==511)
 mass=[W[l]*V[m]*H[0][i]for i,(l,m)in enumerate(CELLS)]
 return dict(g=g,co=co,H=H,menus=menus,mass=mass,records=records,active=active)
def evaluate(model,theta):
 check('one_shared_bounded_thinning',len(theta)==80 and min(theta)>=0 and max(theta)<=1)
 mass=sum((x*y for x,y in zip(theta,model['mass'])),F());debit=F();screens=[];argmax=[]
 for j in range(512):
  mode,T=divmod(j,32);vals=[sum((coef*theta[i]*model['H'][T][i]for i,coef in s),F())for s in model['menus'][mode]]
  k=max(range(len(vals)),key=vals.__getitem__);screens.append(vals[k]);argmax.append(k);debit+=model['co'][j]*vals[k]
 return dict(mass=mass,debit=debit,gate=model['g']*mass-debit,screens=screens,argmax=argmax)
def actual_family(model):
 rows=[]
 def add(kind,parts):
  n=prod(m for m,r in parts);x=sum(r*(n//m)*pow(n//m,-1,m)for m,r in parts)%n
  check('fixed_crt_class',all(x%m==r%m for m,r in parts));rows.append(dict(kind=kind,modulus=n,residue=x,parts=parts))
 for n,x in [(3,2),(9,1),(5,4),(25,1)]+[(q,0)for q in QS]:add('pure',[(n,x)])
 add('central15',[(15,0)])
 stars=[]
 for q,((R,C,I,J),(L,M))in zip(QS,zip(ROOTS,LEAVES)):
  st=[([(3,R)],q,1), ([(5,C)],q,2), ([(3,I),(5,J)],q,3), ([(9,L//3+3*(L%3))],q,4), ([(25,M//5+5*(M%5))],q,5), ([(3,R)],q*q,1), ([(5,C)],q*q,2)]
  stars.append(st)
  for central,n,x in st:add('star',central+[(n,x)])
 for qi,si in EDGES:
  q,s=QS[qi],QS[si];R,C,I,J=ROOTS[qi]
  for tid,(u,v)in enumerate(((1,1),(2,1),(1,2))):
   for slot,(a,b)in enumerate(product(range(2),repeat=2)):
    central=[]
    if a:central.append((3,I if b else R))
    if b:central.append((5,J if a else C))
    xq=1+(4*tid+slot)%(q-1);xs=1+(4*tid+slot+1)%(s-1)
    add('pair',central+[(q**u,xq),(s**v,xs)])
    rows[-1].update(edge=[q,s],outside_exponents=[u,v],central_exponents=[a,b])
 check('165_distinct_odd_actual_originals',len(rows)==len({r['modulus']for r in rows})==165 and all(r['modulus']>1 and r['modulus']%2 for r in rows))
 # Explicit central measures, in root-major indices; higher digits are uniform.
 for l,w in enumerate(W):
  x=l//3+3*(l%3);check('central3_source_support',not w or(x%3!=2 and x%9!=1))
 for m,v in enumerate(V):
  x=m//5+5*(m%5);check('central5_source_support',not v or(x%5!=4 and x%25!=1))
 for ci,rec in enumerate(model['records']):
  l,m=CELLS[ci];x3=l//3+3*(l%3);x5=m//5+5*(m%5)
  for ei,(qi,si)in enumerate(EDGES):
   q,s=QS[qi],QS[si];cap=F()
   for row in rows:
    if row['kind']!='pair' or row['edge']!=[q,s]:continue
    central=[(n,x)for n,x in row['parts']if n in (3,5)]
    if all((x3 if n==3 else x5)%n==x for n,x in central):
     u,v=row['outside_exponents'];cq=F(1,q-1)if u==1 else F(1,q*(q-2));cs=F(1,s-1)if v==1 else F(1,s*(s-2));cap+=cq*cs
   check('full_slot_beta_matches_fixed_actual_labels',cap==rec['beta'][ei])
  for qi,(q,st)in enumerate(zip(QS,stars)):
   active=[(n,x)for central,n,x in st if all((x3 if p in (3,9)else x5)%p==a for p,a in central)]
   count=sum(1 for x in range(q*q)if x%q and all(x%n!=a for n,a in active));f=F(count,q*(q-1))
   check('actual_star_law_dominates_thinning_target',f>=rec['Z'][qi]>0)
   check('actual_root_and_square_caps',F(1,q*(q-1))<=F(1,q*(q-2)))
 return rows
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=Path(__file__).with_name('actual_pair_activation_certificate.json'));ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=ap.parse_args()
 model=make_model(args.source);theta=[F(n,THETA_DEN)for n in THETA_NUMS];value=evaluate(model,theta);check('positive_exact_complete_gate',value['gate']>0);check('gate_above_one_over55',value['gate']>F(1,55));check('bad_cells_zero_in_common_witness',all(not theta[i]for i,r in enumerate(model['records'])if not r['good']));baseline=evaluate(model,[F(int(r['good']))for r in model['records']]);check('retaining_all_good_cells_is_negative',baseline['gate']<0);actual=actual_family(model)
 caps=[F(2),F(4,3)]+[F(q,q-2)for q in QS]+[F(5,3),F(20,11),F(2)]
 check('inherited_same_source_Haar_factor',ALPHA*prod(caps)==1)
 value.update(Haar_factor=ALPHA,Haar_lower=ALPHA*value['gate'])
 check('head_Haar_above_one_over2300',value['Haar_lower']>F(1,2300))
 check('simple_gate_threshold_pays_Haar_bound',ALPHA*F(1,55)>F(1,2300))
 out=dict(schema='free-endpoint-worst-root-common-thinning-v1',scope=__doc__,selection_source626=dict(recorded_sha256=SELECTION_SOURCE626_SHA256,current_input_checked=False,role='selection provenance only; producer does not read the626 certificate'),coefficient_sha256=COEFF_PIN,selection=dict(case=14,shared_states=[6,19,19,17,17],roots=ROOTS,leaf_indices=[14,86,86,81,81],leaves=LEAVES,pair_codes=PAIR_CODES,warning='coherent extension of registered worst conditional root layout; not claimed globally worst actual layout'),central_law=dict(weights3=W,weights5=V,pure_inventory=[(3,2),(9,1),(5,4),(25,1)],additional_live_central_pure='absent',higher_digits='uniform',density_caps=[2,F(4,3)]),outside_pure_scope='arbitrary finite pure inventories under the actual root-balanced source construction of624/626; the explicit165-class witness uses only0modq',inherited_head_Haar_caps=caps,cells=CELLS,cell_evidence=model['records'],selector_counts=[len(x)for x in model['menus']],thinning=dict(denominator=THETA_DEN,numerators=THETA_NUMS),positive=value,all_good_cells_baseline=baseline,actual_originals=actual,good_cells=sum(r['good']for r in model['records']),checks=CHECKS,check_count=len(CHECKS),new_lean_verification=False,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 args.output.write_text(json.dumps(enc(out),indent=2)+'\n');print('PASS',len(CHECKS),'checks; good cells',out['good_cells'],'gate',value['gate'],float(value['gate']),'baseline',float(baseline['gate']))
if __name__=='__main__':main()
