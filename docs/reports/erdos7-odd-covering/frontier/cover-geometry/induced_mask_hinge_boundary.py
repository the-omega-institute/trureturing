"""Exact arithmetic for the induced response and central-mask boundary.

Recompute complete-height hinges and all-real-parameter row minima on the
old controlling branches.  The negative result obstructs this sufficient
comparison-fee expression, not actual survivors or all source designs.
Run with Python 3; only the two named sibling JSON certificates are inputs.
"""
from fractions import Fraction as F
from math import prod,isqrt
from itertools import combinations
from pathlib import Path
import json,hashlib,argparse
parser=argparse.ArgumentParser()
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
S=10**75;TMAX=1249-13
K1={3:F(2,3),5:F(4,15),7:F(1,6),11:F(1,10),13:F(1,12)}
DEEP={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11)}
branches={'four':((3,5,7,11),F(1)),'five':((3,5,7,11,13),F(1)),'four_baseline':((7,11),F(1)),'five_baseline':((7,11,13),F(1))}
checks={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 checks[k]=checks.get(k,0)+1
def ceildiv(n,d):return -(-n//d)
source_pins={
 'unqueried_head_four_parent_certificate.json':'8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f',
 'five_parent_seventy_one_halfrow_certificate.json':'e1a24ebc1c8a6a4582631d8df16cfac04a5d830dfb8e244deb1b32def7c4b6b6',
}
sources={}
for name,pin in source_pins.items():
 raw=(args.directory/name).read_bytes()
 ck('source_hash_pin',hashlib.sha256(raw).hexdigest()==pin)
 sources[name]=json.loads(raw)
 ck('source_status',sources[name]['status']=='PASS')
s651=sources['unqueried_head_four_parent_certificate.json']
s655=sources['five_parent_seventy_one_halfrow_certificate.json']
gamma=F(203129722400814193208791597,20692505911553620784640000000)
alpha=F(2673,110656)
typeI=F(1,65536)
for source in sources.values():
 ck('source_head_gate',F(source['head_gate'])==gamma)
 ck('source_projection',F(source['projection_alpha'])==alpha)
 ck('source_typeI',F(source['ordinary_typeI_fee'])==typeI)
ck('source_chain',s655['source_sha256']==source_pins['unqueried_head_four_parent_certificate.json'])
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

Q=(7,11,13,17,19)
mass={7:F(5,6),**{q:F(q-2,q-1)-F(2,q*(q-2)) for q in Q if q!=7}}
beta={(q,s):F(1,q*(q-2)*(s-1))+F(1,(q-1)*s*(s-2)) for q,s in combinations(Q,2)}
def induced(U):
 return prod((mass[q] for q in U),start=F(1))-sum(beta[q,s]*prod((mass[z] for z in U if z not in(q,s)),start=F(1)) for q,s in combinations(U,2))
lam=F(328686693796069,337134711943765)
low7_mass={**mass,7:F(157,210)}
computed_lambda=1-sum(beta[q,s]/(low7_mass[q]*low7_mass[s]) for q,s in combinations(Q,2))
ck('lambda_exact',computed_lambda==lam)
ck('insertion3_payment',mass[7]*lam>=F(4,5));ck('insertion5_payment',mass[11]*lam>=F(5,6))
for n in range(6):
 for U in combinations(Q,n):
  ck('positive_induced_response',induced(U)>0)
  ck('subset_lambda_floor',induced(U)/prod((mass[q] for q in U),start=F(1))>=lam)
  for q in Q:
   if q not in U:
    V=tuple(sorted(U+(q,)))
    ck('response_ratio_lower',induced(V)/induced(U)>=mass[q]*lam)
    ck('response_ratio_upper',induced(V)/induced(U)<=mass[q])
    for p in U:
     if p<q:ck('response_exchange',induced(tuple(sorted(tuple(z for z in U if z!=p)+(q,))))>=induced(U))
Hresp={4:induced((13,17,19)),5:induced((17,19))}
ck('last_outside_comparison',Hresp[4]/Hresp[5]<=mass[13])
ck('source_four_mean',F(s655['branch_parameters']['four']['exact_EC'])==F(means['four']))
ck('source_five_mean',F(s655['branch_parameters']['five_head']['exact_EC'])==F(means['five']))
ck('four_baseline_mean',F(means['four_baseline'])==F(1,3))
ck('five_baseline_mean',F(means['five_baseline'])==F(5,11))
primes=[p for p in range(37,1253) if all(p%d for d in range(2,isqrt(p)+1))]
ck('owner_census',len(primes)==193 and primes[-1]==1249)
rows={4:[],5:[]}
for r,name in ((4,'four'),(5,'five')):
 for v in primes:
  D=v-3;best=None;minimum_lower=None;minimum_unmasked=None
  for h in range(10,D+1):
   t=D-h
   # Full upper minus baseline lower gives an enclosing corrected upper.
   upper=F(H[name][1][t],S)-F(H[name+'_baseline'][0][t],15*S)
   fee=Hresp[r]*upper/h
   unmasked_fee=Hresp[r]*F(H[name][1][t],S)/h
   if minimum_unmasked is None or unmasked_fee<minimum_unmasked:minimum_unmasked=unmasked_fee
   current_lower=Hresp[r]*(F(H[name][0][t],S)-F(H[name+'_baseline'][1][t],15*S))/h
   ck('all_candidate_intervals',0<=current_lower<=fee and fee-current_lower<F(1,10**60))
   if minimum_lower is None or current_lower<minimum_lower:minimum_lower=current_lower
   if best is None or fee<best[0]:best=(fee,h)
  fee,h=best;t=D-h
  lower=Hresp[r]*(F(H[name][0][t],S)-F(H[name+'_baseline'][1][t],15*S))/h
  unmasked=Hresp[r]*F(H[name][1][t],S)/h
  ck('mask_fee_enclosure',0<=lower<=fee and fee-lower<F(1,10**60))
  rows[r].append(dict(owner=v,r=r,h=h,fee_upper=str(fee),fee_lower=str(lower),minimum_lower_over_all_h=str(minimum_lower),minimum_unmasked_over_all_h=str(minimum_unmasked),unmasked_same_h=str(unmasked),mask_saving_at_h=str(unmasked-fee)))
policies=[]
for cut in (67,):
 chosen=[rows[4 if p<cut else 5][i] for i,p in enumerate(primes)]
 upper=sum(F(r['fee_upper']) for r in chosen);lower=sum(F(r['minimum_lower_over_all_h']) for r in chosen)
 old=sum(F(r['minimum_unmasked_over_all_h']) for r in chosen)
 saving=old-upper
 policies.append(dict(five_start=cut,finite_lower=str(lower),finite_upper=str(upper),finite_decimal=float(upper),additional_mask_gain=str(saving),additional_mask_gain_decimal=float(saving),reserve_after_typeI=str(gamma-upper-typeI),reserve_decimal=float(gamma-upper-typeI),controlling_branch_only=True,uniform_expression_failure=(lower+typeI>gamma)))
ck('five_from67_expression_failure',policies[0]['uniform_expression_failure'])
out=dict(schema='induced-mask-hinge-boundary-v1',status='PASS',new_lean_verification=False,source_sha256=source_pins,head_gate=str(gamma),projection_alpha=str(alpha),ordinary_typeI_fee=str(typeI),scale=str(S),threshold_max=TMAX,finite_prime_count=len(primes),finite_endpoint=1253,scope='Induced response and full-menu controlling-branch comparison fees; the 67 expression fails, no noncoverage impossibility is asserted',producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),H4=str(Hresp[4]),H5=str(Hresp[5]),lambda_lower=str(lam),not_a_full_branch_max_certificate=True,branches={k:dict(parents=v[0],EC=means[k]) for k,v in branches.items()},policies=policies,rows=rows,checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],check_count=out['check_count'],policies=[{k:p[k] for k in ('five_start','finite_decimal','additional_mask_gain_decimal','reserve_decimal','uniform_expression_failure')} for p in policies]),indent=2))
