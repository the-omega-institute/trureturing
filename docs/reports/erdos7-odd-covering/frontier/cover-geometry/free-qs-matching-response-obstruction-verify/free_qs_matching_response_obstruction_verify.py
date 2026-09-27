#!/usr/bin/env python3
"""Standard-library exact verifier for the free-qs response-table obstruction.
No optimizer, candidate field search, producer import or floating-point inequality is used.
"""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction as R
from functools import lru_cache
from hashlib import sha256
from itertools import combinations,product
import json
p=ArgumentParser(description=__doc__)
p.add_argument('--candidate',type=Path,default=Path(__file__).with_name('free_qs_matching_response_obstruction.json'))
p.add_argument('--source640',type=Path)
p.add_argument('--output',type=Path,default=Path(__file__).with_name('free_qs_matching_response_obstruction_verification.json'))
a=p.parse_args();data=json.loads(a.candidate.read_text());counts={}
def test(name,value):
 counts[name]=counts.get(name,0)+1
 if not value:raise RuntimeError(name)
test('schema',data['schema']=='free-qs-matching-response-obstruction-v1')
source=a.source640 or a.candidate.parent/data['source640']['filename'];raw=source.read_bytes()
test('source_pin',sha256(raw).hexdigest()==data['source640']['sha256'])
original=json.loads(raw)['combined512_coefficients']
test('complete_source_coefficients',original==data['source640_combined512_coefficients'] and len(original)==512)
Q=tuple(data['primes']);test('literal_head',Q==(7,11,13,17,19))
test('literal_nulls',data['nulls']==[3,5]);test('literal_role',data['square7_role']==[0,2,4]);test('literal_corner',data['weak_corner']==[4,6]);test('literal_labelled_alphas',data['alpha_by_lex_edge']==[5]*10)
E=tuple(combinations(range(5),2));edge_index={e:k for k,e in enumerate(E)}
root=[R(1,q-1) for q in Q];square=[R(1,q*(q-2)) for q in Q]
B=[]
for l in range(6):
 B.append([square[i]*root[j]+root[i]*square[j]+root[i]*root[j]*(1+int(data['alpha_by_lex_edge'][e]==l)) for e,(i,j) in enumerate(E)])
Z=[[R(5,6)-R(n,35)]+[R(q-2,q-1)-2*square[k] for k,q in enumerate(Q) if k] for n in range(4)]
margin=1-sum(((square[i]*root[j]+root[i]*square[j]+2*root[i]*root[j])/(Z[3][i]*Z[3][j]) for i,j in E),R(0))
test('strict_whole_box',margin>0 and str(margin)==data['expected']['strict_whole_box_margin'])
# A vertex deletion recurrence reconstructs the matching polynomial independently.
@lru_cache(None)
def response(n,l,vertices):
 if vertices==0:return R(1)
 i=next(i for i in range(5) if vertices>>i&1);remaining=vertices^(1<<i)
 value=Z[n][i]*response(n,l,remaining)
 for j in range(i+1,5):
  if remaining>>j&1:value-=B[l][edge_index[i,j]]*response(n,l,remaining^(1<<j))
 return value
xweights=[2,2,2,0,1,2];yweights=[0 if m==5 else 3 if m==6 else 4 for m in range(20)]
test('actual_corner_totals',sum(xweights)==9 and sum(yweights)==75)
cells=tuple((l,m) for l in range(6) for m in range(20) if xweights[l] and yweights[m] and not(l<3 and m<5))
H={}
for l,m in cells:
 n=int(l//3==0)+int(m//5==2)+int(l==4)
 for T in range(32):
  H[l,m,T]=response(n,l,31^T);test('positive_induced_response',0<H[l,m,T]<=1)
g=R(200163067,201247200);fees=list(map(R,original))
for i in range(1,5):fees[288+(1<<i)]+=g*square[i]
test('fees_nonnegative',min(fees)>=0)
def menu(weights,level,blocksize,deep):
 live=[i for i,w in enumerate(weights) if w]
 if level==0:return [weights]
 if level==1:return [[w if i//blocksize==r else 0 for i,w in enumerate(weights)] for r in range(len(weights)//blocksize)]
 if level==2:return [[w if i==t else 0 for i,w in enumerate(weights)] for t in live]
 return [[deep if i==t else 0 for i in range(len(weights))] for t in live]
menus=[]
for mode in range(16):
 u,v=divmod(mode,4);menus.append((menu(xweights,u,3,9),menu(yweights,v,5,60)))
test('literal_selector_count',sum(len(x)*len(y) for x,y in menus)==data['expected']['literal_selectors']==559)
mass=sum((R(xweights[l]*yweights[m],675)*H[l,m,0] for l,m in cells),R(0));unit_debit=R(0)
for mode,(xs,ys) in enumerate(menus):
 for T in range(32):
  values=[sum((R(x[l]*y[m],675)*H[l,m,T] for l,m in cells),R(0)) for x,y in product(xs,ys)]
  unit_debit+=fees[32*mode+T]*max(values);test('complete_screen_evaluated',len(values)>0)
unit=g*mass-unit_debit;test('exact_unit_gate',str(unit)==data['expected']['unit_gate'])
D=data['dual_denominator'];test('positive_dual_denominator',isinstance(D,int) and D>0)
loads=[R(0)]*512;caps={(l,m):g*R(xweights[l]*yweights[m],675)*H[l,m,0] for l,m in cells};seen=set()
for mode,T,xi,yi,N in data['dual_rows']:
 test('literal_dual_address',0<=mode<16 and 0<=T<32 and 0<=xi<len(menus[mode][0]) and 0<=yi<len(menus[mode][1]))
 test('nonnegative_integer_dual',isinstance(N,int) and N>0)
 address=(mode,T,xi,yi);test('no_duplicate_dual_address',address not in seen);seen.add(address)
 lam=R(N,D);loads[32*mode+T]+=lam;x=menus[mode][0][xi];y=menus[mode][1][yi]
 for l,m in cells:caps[l,m]-=lam*R(x[l]*y[m],675)*H[l,m,T]
for j in range(512):test('exact_fee_budget',loads[j]<=fees[j])
upper=sum((max(R(0),v) for v in caps.values()),R(0));test('exact_upper',str(upper)==data['expected']['universal_field_upper'])
test('strict_obstruction',upper<R(data['expected']['upper_ceiling'])<R(data['expected']['target']))
test('literal_dimensions',len(cells)==data['expected']['cell_count']==80 and len(data['dual_rows'])==data['expected']['dual_nonzero_count']==354 and len(fees)==data['expected']['fee_count']==512)
# A simultaneous globally fixed phase witness establishes that the native layout is admissible.
def crt2(a,m,b,n):return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
phases={3:2,9:1,5:4,25:1,15:0}
for q in Q:
 phases[q]=0
 for c in (3,5,15,9,25,45,75,225):
  M=c*q;value=crt2(0,c,1,q);test('distinct_linear_original',M not in phases);phases[M]=value;test('retained_common_root',value%q==1)
 for c,residue in ((3,0),(5,2),(9,4)):
  M=c*q*q;value=crt2(residue,c,2,q*q);test('distinct_square_star',M not in phases);phases[M]=value;test('square_star_actual_role',value%c==residue%c and value%(q*q)==2)
for q,s in combinations(Q,2):
 for M,value in ((q*s,2),(9*q*s,crt2(7,9,3,q*s)),(q*q*s,4),(q*s*s,5)):
  test('distinct_pair_original',M not in phases);phases[M]=value
 test('free_qs_actual_endpoints',phases[q*s]%q==2 and phases[q*s]%s==2)
 test('fixed_9qs_actual_phase',phases[9*q*s]%9==7 and phases[9*q*s]%q==3 and phases[9*q*s]%s==3)
 endpoint_pairs=[(phases[M]%q,phases[M]%s) for M in (q*s,9*q*s,q*q*s,q*s*s)]
 test('four_distinct_edge_firstroot_pairs',endpoint_pairs==[(2,2),(3,3),(4,4),(5,5)] and len(set(endpoint_pairs))==4)
result=dict(schema='free-qs-matching-response-obstruction-verification-v1',status='PASS',candidate_sha256=sha256(a.candidate.read_bytes()).hexdigest(),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),source640_sha256=sha256(raw).hexdigest(),new_lean_verification=False,optimizer_used=False,check_count=sum(counts.values()),checks=counts,strict_whole_box_margin=str(margin),unit_gate=str(unit),source_mass=str(mass),unit_debit=str(unit_debit),universal_field_upper=str(upper),upper_ceiling=data['expected']['upper_ceiling'],target=data['expected']['target'],dual_nonzero_count=len(data['dual_rows']),positive_cell_cap_count=sum(v>0 for v in caps.values()),actual_phase_witness_count=len(phases),actual_phase_witness=[dict(modulus=m,residue=v) for m,v in sorted(phases.items())],scope=data['scope'])
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ('status','check_count','unit_gate','universal_field_upper','upper_ceiling','target','optimizer_used')}))
