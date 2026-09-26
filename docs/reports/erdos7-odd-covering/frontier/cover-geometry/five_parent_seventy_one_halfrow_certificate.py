"""Exact coefficients for the one-source four/five/arbitrary-parent policies.
Source, branch domination and infinite analytic inequalities are ordinary
mathematical proofs supplied separately. This is not new Lean verification.
"""
from fractions import Fraction as F
from math import prod,isqrt,comb,factorial
from pathlib import Path
import json,hashlib,argparse
parser=argparse.ArgumentParser();parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);parser.add_argument('--output',type=Path);args=parser.parse_args()
source_path=args.directory/'unqueried_head_four_parent_certificate.json'
source_bytes=source_path.read_bytes();source=json.loads(source_bytes)
S=10**75;TMAX=1249-13
K1={3:F(2,3),5:F(4,15),7:F(1,6),11:F(1,10),13:F(1,12),37:F(1,10)}
DEEP={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),37:F(37,10)}
Z={13:F(1549,1716),17:F(3793,4080),19:F(5455,5814)}
branches={'four':((3,5,7,11),Z[13]*Z[17]*Z[19]),'five_head':((3,5,7,11,13),Z[17]*Z[19]),'five_outside':((3,5,7,11,37),Z[13]*Z[17]*Z[19])}
checks={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 checks[k]=checks.get(k,0)+1
def ceildiv(n,d):return -(-n//d)
AT={}
for p in K1:
 low=[0]*(TMAX+1);up=[0]*(TMAX+1)
 first=(1-K1[p],K1[p]-DEEP[p]/p**2)
 for j,a in enumerate(first,1):low[j]=a.numerator*S//a.denominator;up[j]=ceildiv(a.numerator*S,a.denominator)
 ppow=p**3
 for j in range(3,TMAX+1):
  num=DEEP[p].numerator*(p-1);den=DEEP[p].denominator*ppow
  low[j]=num*S//den;up[j]=ceildiv(num*S,den);ppow*=p
 AT[p]=(low,up)
cache={():([0,S]+[0]*(TMAX-1),[0,S]+[0]*(TMAX-1))}
def distribution(parents):
 if parents in cache:return cache[parents]
 low0,up0=distribution(parents[:-1]);lo,hi=AT[parents[-1]]
 low=[0]*(TMAX+1);up=[0]*(TMAX+1)
 for i in range(1,TMAX+1):
  for j in range(1,TMAX//i+1):low[i*j]+=low0[i]*lo[j];up[i*j]+=up0[i]*hi[j]
 for i in range(1,TMAX+1):low[i]//=S;up[i]=ceildiv(up[i],S);ck('distribution_interval',0<=low[i]<=up[i])
 cache[parents]=(low,up);return low,up
H={};means={};factors={}
for name,(ps,factor) in branches.items():
 em=prod(1+K1[p]+DEEP[p]/(p*(p-1)) for p in ps)-1;means[name]=str(em);factors[name]=str(factor)
 low,up=distribution(ps);pl=pu=ml=mu=0;hl=[];hu=[]
 for t in range(TMAX+1):
  if t:pl+=low[t];pu+=up[t];ml+=t*low[t];mu+=t*up[t]
  base=(em.numerator-t*em.denominator)*S
  nl=base+em.denominator*((t+1)*pl-ml);nu=base+em.denominator*((t+1)*pu-mu)
  dl=em.denominator*S
  l=nl*factor.numerator*S//(dl*factor.denominator)
  u=ceildiv(nu*factor.numerator*S,dl*factor.denominator)
  ck('hinge_interval',0<=l<=u);hl.append(l);hu.append(u)
 H[name]=(hl,hu)
primes=[p for p in range(37,1253) if all(p%d for d in range(2,isqrt(p)+1))]
ck('owner_count',len(primes)==193)
rows={4:[],5:[]}
for r in (4,5):
 for v in primes:
  names=('four',) if r==4 else ('five_head',) if v==37 else ('five_head','five_outside')
  D=v-3;best=None
  for h in range(10,D):
   t=D-h
   n,name=max((H[name][1][t],name) for name in names)
   if best is None or n*best[1]<best[0]*h:best=(n,h,name)
  n,h,name=best;t=D-h
  lower=max(H[nm][0][t] for nm in names)
  feeup=F(n,h*S);feelow=F(lower,h*S);cap=F(v-1,h)
  ck('actual_cap_invariant',cap<F(v,10));ck('narrow_fee_interval',feeup-feelow<F(1,10**60))
  rows[r].append(dict(owner=v,r=r,h=h,t=t,D=D,N=0,cap=str(cap),worst_branch=name,fee_lower=str(feelow),fee_upper=str(feeup),fee_decimal=float(feeup)))
# The branch domination is proved for every threshold. Here both complete
# auxiliary hinges are also enclosed throughout the finite evaluation window.
Alo,Aup=H['five_head'];Blo,Bup=H['five_outside']
ck('finite_head_over_outside',all(a>=b for a,b in zip(Alo,Bup)))
gamma=F(203129722400814193208791597,20692505911553620784640000000);alpha=F(2673,110656)
ck('source_status',source['status']=='PASS')
ck('source_hash_pin',hashlib.sha256(source_bytes).hexdigest()=='8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f')
ck('source_reserve',F(source['head_gate'])==gamma)
ck('source_projection',F(source['projection_alpha'])==alpha)
for q in (13,17,19):ck('source_omission_mass',F(source['unqueried_coordinate_mass_caps'][str(q)])==Z[q])
chosen=[rows[4 if p<71 else 5][i] for i,p in enumerate(primes)]
ck('one_row_per_finite_owner',len(chosen)==193 and len({x['owner'] for x in chosen})==193)
ck('finite_four_parent_census',sum(row['r']==4 for row in chosen)==8)
ck('finite_five_parent_census',sum(row['r']==5 for row in chosen)==185)
finite_fee=sum((F(row['fee_upper']) for row in chosen),F(0))
# Uniform all-five-role comparison, requiring no omitted-source factor.
gp=(3,5,7,11,13);gk=tuple(map(F,('2/3','4/15','1/6','1/10','1/10')));gd=tuple(map(F,('2','4/3','7/5','11/9','13/10')))
headcaps=dict(zip((3,5,7,11,13,17,19,23,29,31),map(F,('2','4/3','7/5','11/9','13/11','17/15','19/17','5/3','20/11','2'))))
headfirst={p:(F(1,p-1) if p in (7,11,13,17,19) else c/p) for p,c in headcaps.items()}
for i,refp in enumerate(gp):
 for p,c in headcaps.items():
  if p>=refp:
   ck('head_role_shallow',headfirst[p]<=gk[i])
   ck('head_role_deep',c/p**2<=gd[i]/refp**2)
 ck('outside_role_shallow',F(1,10)<=gk[i])
 ck('outside_role_deep',F(1,370)<=gd[i]/refp**2)
def xmom(p,k1,d,R=7):
 q=F(1,p);geom=[1/(1-q)]
 for r in range(1,R+1):geom.append(q/(1-q)*sum(comb(r,j)*geom[j] for j in range(r)))
 E=[F(1)]
 for r in range(1,R+1):
  delta=2**r-1
  E.append(1+k1*delta+d*(sum(comb(r,j)*geom[j] for j in range(r))-1-q*delta))
 return E
XM=[xmom(p,k,d) for p,k,d in zip(gp,gk,gd)]
M7=sum((-1)**(7-j)*comb(7,j)*prod(e[j] for e in XM) for j in range(8))
A7=F(2**7*6**6,7**7)
ck('sharp_halfrow_scalar_constant',2*F(7,12)-1==A7*F(7,12)**7)
ck('positive_full_moment',M7>0)
five_tail=A7*M7/(6*1249**6)
# Actual finite caps and actual N=0 half rows in the complete Euler baseline.
B0=3**7;Pprimes=[p for p in range(3,B0+1,2) if all(p%d for d in range(2,isqrt(p)+1))]
finitecaps={r['owner']:F(r['cap']) for r in chosen}
scale=2**160;mlo=mhi=plo=phi=scale;counts=dict(head=0,finite=0,half=0)
for p in Pprimes:
 if p in headcaps:c=headcaps[p];counts['head']+=1
 elif p in finitecaps:c=finitecaps[p];counts['finite']+=1
 else:
  c=F(2*(p-1),p-3);counts['half']+=1
  ck('halfrow_cap_invariant',c<F(p,10))
  ck('halfrow_factor_identity',1+c*(F(3,p-1)+F(2,(p-1)**2))==F((p+1)**2,(p-1)*(p-3)))
 T=1+c*(F(3,p-1)+F(2,(p-1)**2))
 mlo=mlo*T.numerator//T.denominator;mhi=ceildiv(mhi*T.numerator,T.denominator)
 plo=plo*p//(p-1);phi=ceildiv(phi*p,p-1)
ck('full_finite_product_count',counts==dict(head=10,finite=193,half=123))
Mlo,Mhi,Plo,Phi=(F(x,scale) for x in (mlo,mhi,plo,phi))
# For every p>=11, T_half/(p/(p-1))^6 <=1+2/p^2 follows
# after multiplication from p^4(p-11)+5p^3+p^2-3p+1>=0.
ck('Euler_polynomial_base',11**5-11*11**4+5*11**3+11**2-3*11+1>0)
Gamma=F(1,B0);Ctail=F(B0,B0-1)
ck('Euler_exponential_upper',Ctail==1/(1-Gamma))
basefee=finite_fee+five_tail+F(1,65536)
ck('pre_arbitrary_positive_reserve',basefee<gamma)
# Rosser--Schoenfeld Theorem8 is an external analytic premise;
# the ratio99/97 and log baseline below are elementary consequences.
K=46;V=2**K;poly6=sum(F(factorial(6),factorial(6-j))*F(7*K,10)**(6-j) for j in range(7))
Er=Mhi*Ctail*F(99,97)**6*F(V,V-3)**2*poly6/(2*(V-1)*F(1841,240)**6)
rawr=gamma-basefee-Er;densityr=alpha*rawr
ck('RS_complete_budget',densityr>F(1,1250000))
K=68;A6=Mhi*Ctail/Plo**6;ratio=F(1,2)*F(K+3,K+2)**6
ck('elementary_geometric_ratio',ratio<1)
Ee=2*A6*(4*(K+2))**6/F(2**K)/(1-ratio)
rawe=gamma-basefee-Ee;densitye=alpha*rawe
ck('elementary_complete_budget',densitye>F(1,6000000))
out=dict(schema='five-parent-seventy-one-halfrow-v1',status='PASS',new_lean_verification=False,scope='Exact coefficients for the fixed RS46 and elementary68 policies; source, branch domination and infinite-tail statements are ordinary mathematical proofs',source_sha256=hashlib.sha256(source_bytes).hexdigest(),producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),first_five_parent_owner=71,finite_endpoint=1253,head_gate=str(gamma),projection_alpha=str(alpha),scale=str(S),threshold_max=TMAX,branch_parameters={name:dict(parents=ps,factor=factors[name],exact_EC=means[name]) for name,(ps,_) in branches.items()},finite_rows=chosen,finite_fee_upper=str(finite_fee),generic_reference=dict(primes=gp,first_caps=list(map(str,gk)),deep_caps=list(map(str,gd))),coordinate_moments=[list(map(str,e)) for e in XM],complete_fifth_role_count_moment7=str(M7),sharp_halfrow_constant7=str(A7),complete_five_parent_tail=str(five_tail),Euler_endpoint=B0,Euler_counts=counts,Euler_scale=str(scale),M0_lower=str(Mlo),M0_upper=str(Mhi),Podd_lower=str(Plo),Podd_upper=str(Phi),Gamma=str(Gamma),Ctail=str(Ctail),ordinary_typeI_fee=str(F(1,65536)),fee_before_arbitrary=str(basefee),RS_policy=dict(K=46,arbitrary_threshold=2**46,fee=str(Er),raw_margin=str(rawr),projected_margin=str(densityr),density_denominator=1250000),elementary_policy=dict(K=68,arbitrary_threshold=2**68,fee=str(Ee),raw_margin=str(rawe),projected_margin=str(densitye),density_denominator=6000000),checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],check_count=out['check_count'],Euler_counts=counts,finite_fee=float(finite_fee),five_tail=float(five_tail),M0_upper=float(Mhi),RS_fee=float(Er),RS_raw=float(rawr),RS_projected=float(densityr),elementary_fee=float(Ee),elementary_raw=float(rawe),elementary_projected=float(densitye)),indent=2))
