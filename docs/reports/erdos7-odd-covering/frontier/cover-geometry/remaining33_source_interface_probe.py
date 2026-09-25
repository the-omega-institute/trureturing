#!/usr/bin/env python3
"""Bounded exact remaining33 interface diagnostic; no universal positive-gate claim.

Fix one whole33 layout, one source corner and old631 theta. Rebuild all central
masks, star budgets, strict cells and32 responses. Compare baseline30+paid leaf
pairs with baseline30+conditioned leaf pairs. No LP and no layout/source scan.
"""
import argparse,json
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,gcd
from pathlib import Path
from hashlib import sha256
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--layout',type=Path)
ap.add_argument('--demo',choices=['regression','stress'],default='regression')
ap.add_argument('--source',nargs=4,type=int,default=[3,4,5,6],metavar=('Z3','WEAK3','Z5','WEAK5'))
ap.add_argument('--output',type=Path)
args=ap.parse_args();CHECKS={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 CHECKS[k]=True
qs=(7,11,13,17,19);core=(3,5)+qs;r=[F(1,q-1)for q in qs];a=[F(1,q*(q-2))for q in qs]
edges=tuple(combinations(range(5),2));em=[sum(1<<q for q in e)for e in edges]
dis=tuple((i,j)for i,j in combinations(range(10),2)if not(em[i]&em[j]))
kap=[r[q]*r[s]+a[q]*r[s]+r[q]*a[s]for q,s in edges]
raw=(args.source_dir/'actual_pair_activation_certificate.json').read_bytes();b=json.loads(raw)
ck('coefficient_pin',sha256(raw).hexdigest()=='2e9eac2581f6c0e09b75fa91252c251cb62463e96038e6bdb5ed99a48ede8a3f')
c=F(b['constants']['continuation_c']);g=1-c;alpha=F(2673,110656)
L=list(map(F,b['complete_coefficients']['loss']));W=list(map(F,b['complete_coefficients']['weighted_nonunit_query']))
P=[F()]*512;D=[F()]*512;remaining=[]
for e in product(range(3),repeat=7):
 n=sum(x>0 for x in e)
 if not(2<=n<=4 and(e[0]==2 or e[1]==2)):continue
 if n==2 and sum(x>0 for x in e[:2])==1 and sum(e[2:])==1:continue
 outer=[x for x in e[2:]if x]
 keep=n==4 or(n==3 and 2 in outer)or(e[:2]==(0,2)and((n==2 and outer==[2])or(n==3 and outer==[1,1])))
 m=prod(p**x for p,x in zip(core,e))
 if not keep:remaining.append(m);continue
 T=sum(1<<i for i,x in enumerate(e[2:])if x);cap=prod(r[i]if x==1 else a[i]for i,x in enumerate(e[2:])if x)
 D[32*(4*e[0]+e[1])+T]+=cap
for k in range(10):
 for mode in(1,4,5):P[32*mode+em[k]]=kap[k]
co=[g*(l+p+d)+c*w for l,p,d,w in zip(L,P,D,W)]
ck('remaining33_census',len(remaining)==33 and len(set(remaining))==33)
ck('full512_nonnegative',len(co)==512 and min(co)>=0)
# Every record is a whole original modulus with ONE full residue.
if args.layout:
 layout=json.loads(args.layout.read_text())['originals']
else:
 layout=[]
 for m in sorted(remaining):
  d=gcd(m,225);out=m//d
  central=0 if args.demo=='regression' or out==1 else 57%d
  residue=central if out==1 else central+d*((-central*pow(d,-1,out))%out)
  layout.append({'modulus':m,'residue':residue})
ck('one_global_residue_per_original',len(layout)==33 and len({x['modulus']for x in layout})==33 and {x['modulus']for x in layout}==set(remaining))
for row in layout:ck('valid_residue_'+str(row['modulus']),isinstance(row['residue'],int)and 0<=row['residue']<row['modulus'])
roles={row['modulus']:row['residue']%gcd(row['modulus'],225)for row in layout}
def active(m,x):return x%gcd(m,225)==roles[m]
THIN=(F(0),F(0),F(0),F(147,250),F(0),F(1),F(97,250),F(389,1000),F(377,500),F(119,200))
CATS=tuple((i,j)for i,j in product(range(3),range(4))if not(i<2 and j==0))
def theta(l,m):
 if l<3 and m<5:return F()
 cat=(0 if l==0 else 1 if l<3 else 2,0 if m<5 else 2 if m==10 else 3 if m//5==2 else 1)
 return THIN[CATS.index(cat)]
def crt225(l,m):
 x=3*(l%3)+l//3;y=5*(m%5)+m//5
 return x+9*((y-x)*14%25)
# These are fixed BEFORE source weights and before screen maxima.
geom={};grids={name:[[[F()]*20 for _ in range(6)]for _ in range(32)]for name in('baseline30','leaf40')}
counts={name:{'central_masked':0,'star_nonpositive':0,'strict_bad':0,'strict_good':0,'theta_positive_good':0}for name in grids}
for l,m in product(range(6),range(20)):
 x=crt225(l,m);M=x%15!=0 and all(not active(n,x)for n in(45,75,225))
 old=[1-(r[i]+a[i])*(int(l<3)+int(m//5==2))-r[i]*(int(l<3 and m//5==2)+int(l==0)+int(m==10))for i in range(5)]
 Z=[old[i]-a[i]*int(active(9*q*q,x))-r[i]*sum(int(active(d*q,x))for d in(45,75,225))for i,q in enumerate(qs)]
 row={'cell':[l,m],'crt225':x,'central_allowed':M,'Z':list(map(str,Z)),'routes':{}}
 for name in grids:
  stat=counts[name]
  if not M:stat['central_masked']+=1;row['routes'][name]={'kind':'central_masked'};continue
  if min(Z)<=0:stat['star_nonpositive']+=1;row['routes'][name]={'kind':'star_nonpositive'};continue
  beta=[kap[i]+(r[q]*r[s]*int(active(9*qs[q]*qs[s],x))if name=='leaf40'else F())for i,(q,s)in enumerate(edges)]
  u=[beta[i]/(Z[q]*Z[s])for i,(q,s)in enumerate(edges)]
  vals=[]
  for mask in range(1024):
   val=1-sum((u[e]for e in range(10)if mask>>e&1),F())+sum((u[e]*u[f]for e,f in dis if mask>>e&1 and mask>>f&1),F())
   vals.append(val)
  worst=min(range(1024),key=lambda j:vals[j])
  if vals[worst]<=0:stat['strict_bad']+=1;row['routes'][name]={'kind':'strict_bad','subset':worst,'polynomial':str(vals[worst])};continue
  stat['strict_good']+=1;stat['theta_positive_good']+=theta(l,m)>0
  R=[prod(Z[i]for i in range(5)if not T>>i&1)for T in range(32)]
  h=[]
  for T in range(32):
   value=R[T]-sum((beta[e]*R[T|em[e]]for e in range(10)if not T&em[e]),F())+sum((beta[e]*beta[f]*R[T|em[e]|em[f]]for e,f in dis if not T&(em[e]|em[f])),F())
   ck(f'{name}_response_{l}_{m}_{T}',0<value<=R[T]);grids[name][T][l][m]=theta(l,m)*value;h.append(str(value))
  row['routes'][name]={'kind':'strict_good','minimum_induced':str(vals[worst]),'H':h,'beta':list(map(str,beta))}
 geom[l,m]=row
z,w,zz,ww=args.source
ck('source_corner_domain',0<=z<6 and 0<=w<6 and z!=w and 0<=zz<20 and 0<=ww<20 and zz!=ww)
U=[F()if l==z else F(1,9)if l==w else F(2,9)for l in range(6)];V=[F()if m==zz else F(3,75)if m==ww else F(4,75)for m in range(20)]
def qscreen(h):
 out=[F()]*4
 for j in range(4):
  total=F()
  for m in range(5*j,5*j+5):
   if not V[m]:continue
   value=V[m]*h[m];total+=value;out[2]=max(out[2],value);out[3]=max(out[3],F(4,5)*h[m])
  out[0]+=total;out[1]=max(out[1],total)
 return out
def screen(h):
 out=[F()]*16;roots=[[F()]*20 for _ in range(2)]
 for l in range(6):
  if not U[l]:continue
  a=qscreen(h[l])
  for j in range(4):out[8+j]=max(out[8+j],U[l]*a[j]);out[12+j]=max(out[12+j],a[j])
  for m in range(20):roots[l//3][m]+=U[l]*h[l][m]
 total=qscreen([roots[0][m]+roots[1][m]for m in range(20)]);left=qscreen(roots[0]);right=qscreen(roots[1])
 for j in range(4):out[j]=total[j];out[4+j]=max(left[j],right[j])
 return out
results={}
for name,H in grids.items():
 values=[screen(h)for h in H];ss=[values[T][mode]for mode in range(16)for T in range(32)]
 mass=ss[0];debit=sum((v*s for v,s in zip(co,ss)),F())
 leaf_debit=F()
 if name=='baseline30':
  for i,(q,s)in enumerate(edges):
   leaf_debit+=r[q]*r[s]*sum((U[l]*V[m]*H[em[i]][l][m]for l,m in geom if active(9*qs[q]*qs[s],geom[l,m]['crt225'])),F())
 gate=g*mass-debit-g*leaf_debit
 results[name]={'conditional_mass':str(mass),'complete512_debit':str(debit),'actual_global_leaf_pair_debit':str(leaf_debit),'gate':str(gate),'gate_float':float(gate),'positive_gate_at_supplied_corner':gate>0,'converted_comparison_gate_if_positive':str(alpha*gate)if gate>0 else None,'source_corner':args.source,'counts_before_null_source_exclusion':counts[name]}
 if not args.layout and args.demo=='regression'and args.source==[3,4,5,6]:ck('regression_exact635_'+name,gate==F(3365813748958907912564595063607,2483100709386434494156800000000000))
if not args.layout and args.demo=='stress':
 ck('stress_old_positive_cell',theta(1,11)==1 and geom[1,11]['central_allowed'])
 ck('stress_negative_new_Z7',F(geom[1,11]['Z'][0])==-F(3,35))
out={'schema':'remaining33-fixed-layout-common-source-diagnostic-v1','status':'COMPLETED_BOUNDED_DIAGNOSTIC','scope':'One supplied coherent33 layout, one source corner, old631 theta, two reconstructed common-source interfaces. No layout scan, no all-source-corner certificate, no LP, no claim that33 are uniformly admitted.',
 'originals':layout,'source_corner':args.source,'results':results,'cell_data':list(geom.values()),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'dependencies':{'actual_pair_activation_certificate.json':sha256(raw).hexdigest()},'checks':CHECKS,'check_count':len(CHECKS),'new_lean_verification':False}
p=args.output or Path(__file__).with_name('remaining33_interface_'+args.demo+'.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('status','scope','source_corner','results','check_count')},indent=2))
