#!/usr/bin/env python3
"""A realizable obstruction to one fixed sufficient fifteen-star release gate.

Uses exact rational arithmetic only. The fixed full fee table and network
upper budget are part of the tested criterion; they are not actual loss
lower bounds. An explicit CRT survivor certifies that the fixture itself
is not covering. No new Lean verification is claimed.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
from hashlib import sha256
import json,sys
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=HERE,
                    help='directory containing the pinned648 coefficient data')
parser.add_argument('--dual',type=Path,default=HERE/'linear15_exact_factor_dual_weights.json')
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
SOURCE=args.directory/'induced_square_pair_boundary_certificate.json'
DUAL=args.dual
raw=SOURCE.read_bytes();data=json.loads(raw);dual=json.loads(DUAL.read_text())
checks={}
def check(k,v):
 checks[k]=checks.get(k,0)+1
 if not v:raise RuntimeError('FAIL '+k)
check('pinned648 coefficient input',sha256(raw).hexdigest()=='1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
check('pinned dyadic selector dual',sha256(DUAL.read_bytes()).hexdigest()=='718782274441fdfe7be9fc10b12efc81ea4d81df03ca8dc99b01ca1433581783')
Q=(7,11,13,17,19);HEAD=(3,5)+Q+(23,29,31);g=F(200163067,201247200)
r=[F(1,q-1)for q in Q];b=[F(1,q*(q-1))for q in Q];a=[F(1,q*(q-2))for q in Q]
roles=[((0,1),(0,6),(0,7)),((1,1),(0,8),(1,9)),((2,2),(0,10),(2,11)),((0,2),(0,12),(0,13)),((1,3),(0,14),(1,15))]
check('fixed full15 central layout',dual['roles']==[[list(x)for x in row]for row in roles])
check('fixed corner',dual['corner']==[3,4,5,6])
C=list(map(F,data['unchanged512_coefficients']))
for i,q in enumerate(Q):
 if q!=7:C[32*9+(1<<i)]-=g*a[i]
check('complete nonnegative512 coefficients',len(C)==512 and min(C)>=0)
# The four removed fees were646's guarded9q² portions; all15 actual square stars are now deleted.
def a3(l):return 3*(l%3)+l//3
def a5(m):return 5*(m%5)+m//5
fixture={};parts={}
def put(tag,components):
 n=prod(mod for _,mod in components);out=sum(res*(n//mod)*pow(n//mod,-1,mod)for res,mod in components)%n
 check('distinct original numerical moduli',n not in fixture)
 for res,mod in components:check('fixed original CRT component',out%mod==res%mod)
 fixture[n]={'label':tag,'residue':out,'components':[[res%mod,mod]for res,mod in components]};parts[tag]=dict((mod,res%mod)for res,mod in components)
for p in HEAD:put('pure'+str(p),[((2 if p==3 else 4 if p==5 else 0),p)])
put('pure9',[(1,9)]);put('pure25',[(1,25)])
height=12
for p,weak in ((3,4),(5,6)):
 for e in range(3,height+1):put('pure'+str(p**e),[(weak+p**(e-1),p**e)])
# Optional finite pure tails concentrate the declared deep caps in a clean root,
# without changing any unary or pair event category used below.
for q in Q:
    caproot=4 if q==7 else 8
    for e in range(2,height+1):put('pure'+str(q**e),[(caproot+q**(e-1),q**e)])
put('15',[(0,3),(0,5)])
for i,q in enumerate(Q):
 for label,central in [('3q',[(0,3)]),('5q',[(0,5)]),('15q',[(0,3),(0,5)]),('9q',[(1,9)]),('25q',[(1,25)])]:
  put(label+':'+str(q),central+[(1,q)])
 c45,c75,c225=roles[i]
 put('45q:'+str(q),[(a3(c45[0]),9),(c45[1],5),(2,q)])
 put('75q:'+str(q),[(c75[0],3),(a5(c75[1]),25),(3,q)])
 put('225q:'+str(q),[(a3(c225[0]),9),(a5(c225[1]),25),(4,q)])
 put('3q2:'+str(q),[(1,3),(5,q*q)])
 put('5q2:'+str(q),[(2,5),(6,q*q)])
 put('9q2:'+str(q),[(7,9),(5+q,q*q)])
# Two edge-disjoint Hamilton cycles force every live root choice on the two positive row1 leaves.
cycles=((0,1,2,3,4),(0,2,4,1,3));oriented={}
for leaf,cy in zip((4,5),cycles):
 for k,i in enumerate(cy):
  j=cy[(k+1)%5];edge=tuple(sorted((i,j)))
  check('Hamilton edge partition',edge not in oriented);oriented[edge]=(leaf,i,j)
check('all ten retained pair edges',len(oriented)==10)
neighbors=[[j for j in range(5)if j!=i]for i in range(5)]
def sqphase(i,j):return (5+Q[i]*(neighbors[i].index(j)+2))if i==0 else (7+Q[i]*neighbors[i].index(j))
for i,j in combinations(range(5),2):
 q,s=Q[i],Q[j];put('qs:'+str(i)+','+str(j),[(1,q),(1,s)])
 leaf,pred,succ=oriented[(i,j)]
 put('9qs:'+str(i)+','+str(j),[(a3(leaf),9),(1,Q[pred]),(2,Q[succ])])
 put('q2s:'+str(i)+','+str(j),[(sqphase(i,j),q*q),(5 if j==0 else 7,s)])
 put('qs2:'+str(i)+','+str(j),[(5 if i==0 else 7,q),(sqphase(j,i),s*s)])
check('complete finite fixture size',len(fixture)==183)
# One actual CRT survivor: local assignments are consistent across all powers.
local_survivor={3:0,5:6,7:6,11:6,13:6,17:6,19:6,23:1,29:1,31:1}
resolving={p:p for p in HEAD}
for row in fixture.values():
    for res,mod in row['components']:
        bases=[p for p in HEAD if mod%p==0]
        check('component has one declared prime base',len(bases)==1)
        p=bases[0];t=mod
        while t%p==0:t//=p
        check('component is a prime power',t==1)
        resolving[p]=max(resolving[p],mod)
fixture_lcm=prod(resolving.values())
survivor=sum(local_survivor[p]*(fixture_lcm//mod)*pow(fixture_lcm//mod,-1,mod)
             for p,mod in resolving.items())%fixture_lcm
for p,mod in resolving.items():
    check('actual survivor CRT component',survivor%mod==local_survivor[p])
for modulus,row in fixture.items():
    check('actual survivor avoids every original',survivor%modulus!=row['residue'])
actual_survivor=dict(local_residues=local_survivor,resolving_prime_powers=resolving,
                     lcm=fixture_lcm,residue=survivor)
wx=[F(0),F(0)] # rebuilt below, no candidate probabilities read
wx=[F(0)if l==3 else F(1,9)if l==4 else F(2,9)for l in range(6)]
vy=[F(0)if m==5 else F(3,75)if m==6 else F(4,75)for m in range(20)]
coords=[(l,m)for l in range(6)for m in range(20)if wx[l]and vy[m]and not(l<3 and m<5)]
check('eighty actual positive central cells',len(coords)==80)
for l,m in coords:
 for i,q in enumerate(Q):
  if l<3:
   check('root forced by actual3q',parts['3q:'+str(q)][3]==a3(l)%3 and parts['3q:'+str(q)][q]==1)
  else:
   force=[(edge,t)for edge,t in oriented.items()if t[0]==l and t[1]==i]
   check('unique root-forcing9qs edge',len(force)==1)
   edge,(_,pred,succ)=force[0];ss=Q[succ]
   core=parts['qs:'+str(edge[0])+','+str(edge[1])];extra=parts['9qs:'+str(edge[0])+','+str(edge[1])]
   check('root-forcing pair of incompatible other endpoints',core[q]==extra[q]==1 and core[ss]==1 and extra[ss]==2 and extra[9]==a3(l))
# Pure source capacities force all allowed central weight vectors close to the corner.
eps3=F(1,3**height);eps5=F(1,3*5**height)
for p,weak,cap,target,eps in ((3,4,F(2),F(1,9),eps3),(5,6,F(4,3),F(3,75),eps5)):
 rawweak=F(1,p*p)-sum((F(1,p**e)for e in range(3,height+1)),F(0))
 check('exact weak leaf capacity',cap*rawweak==target+eps)
 check('corner law is actually realizable',target/rawweak<=cap)
 for e,f in combinations(range(3,height+1),2):
  check('higher pure deletions disjoint in weak leaf',(weak+p**(e-1))%p**e != (weak+p**(f-1))%p**e)
# The additional pure tails leave root masses and every relevant partial-prefix mass unchanged.
for i,q in enumerate(Q):
    caproot=4 if q==7 else 8
    check('deep-cap root separated from partial-event roots',caproot not in (0,1,5,6,7))
    root_haar=F(1,q)-sum((F(1,q**e)for e in range(2,height+1)),F(0))
    actual_square=F(1,q*q)/((q-1)*root_haar)
    check('exact almost-sharp deep cap',actual_square/a[i]>1-F(1,10**9) and actual_square<a[i])
    for e,f in combinations(range(2,height+1),2):
        check('outside pure deletions disjoint',(caproot+q**(e-1))%q**e!=(caproot+q**(f-1))%q**e)
# Allowed compressed pair states for each unqueried set;0=nonroot,1=ordinary root,
# 2..5=the four distinct actual square prefixes directed at the four other coordinates.
allowed={}
for T in range(32):
 U=[i for i in range(5)if not T>>i&1];aU=[]
 for states in product(range(6),repeat=len(U)):
  ss=dict(zip(U,states));ok=True
  for i in U:
   state=ss[i]
   if state>=2:
    j=neighbors[i][state-2]
    if j in ss and ss[j]!=0:ok=False;break
  if ok:aU.append(states)
 allowed[T]=(U,aU)
H=[[]for _ in range(32)];minmass=None
for l,m in coords:
 ns=int(l//3==1)+int(m//5==2)+int(l==5)
 Z=[];R=[];N=[]
 for i,q in enumerate(Q):
  c45,c75,c225=roles[i]
  nl=int((l,m//5)==c45)+int((l//3,m)==c75)+int((l,m)==c225)
  zi=q*(q-2)-q*nl-ns
  ri=q-(int(l//3==1)+int(l==5)if i==0 else 0)
  ni=zi-ri
  check('actual coordinate counts nonnegative',min(zi,ri-4,ni)>=0)
  # All four pair square prefixes survive the actual unary deletions.
  for j in neighbors[i]:
   prefix=sqphase(i,j)
   check('pair special first root',prefix%q==(5 if i==0 else 7))
   check('pair special avoids every unary prefix',prefix not in (5,6,5+q) and prefix%q not in (0,1,2,3,4))
  Z.append(zi);R.append(ri);N.append(ni)
 for T in range(32):
  U,states=allowed[T];den=prod(Q[i]*(Q[i]-1)for i in U)
  num=0
  for smask in range(1<<len(U)):
   S=[i for k,i in enumerate(U)if smask>>k&1]
   num+=prod(R[i]-len(S)+1 if i in S else N[i]for i in U)
  brute=sum(prod(N[i]if state==0 else R[i]-4 if state==1 else 1 for i,state in zip(U,st))for st in states)
  check('all32 exact factors match actual category enumeration',num==brute)
  hval=F(num,den);H[T].append(hval)
  check('induced actual response between zero and one',0<hval<=1)
minmass=min(H[0])
# Full central selector menus, with deep selectors unweighted by current leaf mass.
def menus(v,roots,deep):
 out=[[v],[[v[i]if roots[i]==a else F(0)for i in range(len(v))]for a in sorted(set(roots))],[],[]]
 for i,x in enumerate(v):
  if x:
   out[2].append([x if j==i else F(0)for j in range(len(v))])
   out[3].append([deep if j==i else F(0)for j in range(len(v))])
 return out
sx=menus(wx,[l//3 for l in range(6)],F(1));sy=menus(vy,[m//5 for m in range(20)],F(4,5))
selectors=[[[x[l]*y[m]for l,m in coords]for x in sx[mode//4]for y in sy[mode%4]]for mode in range(16)]
D=dual['denominator'];check('positive exact dual denominator',D==2**40)
k=[g*wx[l]*vy[m]*H[0][i]for i,(l,m)in enumerate(coords)]
for j in range(512):
 weights=dual['weights'].get(str(j),[]);check('dyadic convex selector row',sum(n for _,n in weights)<=D and all(n>0 for _,n in weights))
 mode,T=divmod(j,32)
 for si,n in weights:
  check('valid actual central selector',0<=si<len(selectors[mode]))
  coeff=C[j]*F(n,D)
  for i,x in enumerate(selectors[mode][si]):k[i]-=coeff*x*H[T][i]
# Max(theta_c in[0,1]) of this exact linear majorant.
upper=sum((max(F(0),x)for x in k),F(0))
perturb=2*(g+sum(C,F(0)))*(eps3+eps5)
uniform=upper+perturb
network=F(397,50000)+F(1,65536)+F(8,3)*F(19740202146111572828188083,495176015714152109959649689600)
check('strict exact corner obstruction',upper<F(1,300))
check('uniform central-capacity obstruction',uniform<F(1,300))
check('strict short-network comparison',F(1,300)<network)
result={'schema':'linear15-fixed-gate-obstruction-v1','status':'PASS','conclusion_kind':'fixed-sufficient-criterion-obstruction','scope':'Obstruction to the fixed complete512 factor-erasure gate and fixed647 prepaid upper budget, for the specified root-balanced outside product source, supported cap-bounded central product laws and cellwise central thinning. It is not a lower bound on actual continuation loss or an upper bound on actual survivor mass.','actual_survivor':actual_survivor,'actual_fixture_covering':False,'unrestricted_erdos7_resolved':False,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False,'source_sha256':sha256(raw).hexdigest(),'dual_sha256':sha256(DUAL.read_bytes()).hexdigest(),'fixture_originals':len(fixture),'fixture':[{'modulus':n,**row}for n,row in sorted(fixture.items())],'corner':[3,4,5,6],'roles':roles,'pure_tail_height':height,'positive_central_cells':len(coords),'minimum_actual_conditional_survivor':str(minmass),'complete512_coefficients':list(map(str,C)),'induced_responses':[[str(x)for x in hs]for hs in H],'dual_linear_coefficients':list(map(str,k)),'exact_corner_gate_upper':str(upper),'exact_corner_gate_upper_decimal':float(upper),'central_capacity_perturbation':str(perturb),'central_capacity_perturbation_decimal':float(perturb),'uniform_gate_upper':str(uniform),'uniform_gate_upper_decimal':float(uniform),'simple_gate_upper':'1/300','r4_network_budget':str(network),'r4_network_budget_decimal':float(network),'checks':checks,'check_count':sum(checks.values())}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in ('status','fixture_originals','positive_central_cells','minimum_actual_conditional_survivor','exact_corner_gate_upper_decimal','central_capacity_perturbation_decimal','uniform_gate_upper_decimal','r4_network_budget_decimal','check_count')}))
