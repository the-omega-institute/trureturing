#!/usr/bin/env python3
"""Independent exact ceiling for one constant four-root response box.

Uses only canonical640 numerical coefficients. No actual-phase counterexample,
full-layout scan, sequential-kernel result or Lean verification is claimed.
"""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from pathlib import Path
from hashlib import sha256
import argparse,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args();checks={}
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]=checks.get(name,0)+1
name='remaining33_global_root_exclusion_certificate.json';pin='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4'
raw=(args.directory/name).read_bytes();ck('source_pin',sha256(raw).hexdigest()==pin);source=json.loads(raw)
Q=(7,11,13,17,19);r={q:F(1,q-1)for q in Q};a={q:F(1,q*(q-2))for q in Q}
Z={q:1-4*r[q]-(3 if q==7 else 2)*a[q]for q in Q}
E=tuple(combinations(Q,2));beta={e:a[e[0]]*r[e[1]]+r[e[0]]*a[e[1]]+2*r[e[0]]*r[e[1]]for e in E}
g=F(200163067,201247200);ck('same_source_coefficient',g==F(source['constants']['g']))
C=list(map(F,source['combined512_coefficients']));ck('nonnegative_full_coefficients',len(C)==512 and all(c>=0 for c in C))
old_mode0=C[:32]
for u,q in enumerate(Q):
 if q>7:C[32*9+(1<<u)]+=g*a[q]
ck('mode0_unchanged_by_guarded_additions',C[:32]==old_mode0)
for q in Q:ck('unary_mass',0<Z[q]<=1)
for e in E:ck('nonnegative_pair_cap',beta[e]>=0)

def response(support,allowed_edges):
 vertices=tuple(q for q in Q if q not in support)
 edges=tuple(e for e in allowed_edges if all(q not in support for q in e))
 # A matching in a graph with at most five vertices has at most two edges.
 zprod=lambda occupied:prod((Z[q]for q in vertices if q not in occupied),start=F(1))
 return zprod(())-sum((beta[e]*zprod(e)for e in edges),F())+sum((beta[e]*beta[f]*zprod(e+f)for e,f in combinations(edges,2)if not set(e)&set(f)),F())

all_induced=[]
for mask in range(1<<len(E)):
 edges=[e for k,e in enumerate(E)if mask>>k&1]
 value=response((),edges);ck('all_event_induced_positive',value>0)
 all_induced.append(value/prod(Z.values(),start=F(1)))
H=[]
for mask in range(32):
 support=tuple(q for u,q in enumerate(Q)if mask>>u&1)
 value=response(support,E);ck('query_response_positive',0<value<=1);H.append(value)
ck('fully_queried_response',H[31]==1)
mode0_fee=sum((C[T]*H[T]for T in range(32)),F())
A=g*H[0]-mode0_fee
ck('positive_mode0_reserve',A>0)
I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5);weak=(4,6)
w={l:F(1,9)if l==weak[0]else F(2,9)for l in I};v={m:F(3,75)if m==weak[1]else F(4,75)for m in J}
ck('corner_weights_normalized',sum(w.values())==sum(v.values())==1)
LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5))
mass=sum((w[l]*v[m]for l,m in LIVE),F());ck('masked_mass',mass==F(37,45))
upper=A*mass;target=F(193,100000)
ck('strict_obstruction_to_public_floor',upper<target)
ck('stated_source_reserve',A==F(8482754828806680432735281,3678667717609532583936000000))
record=dict(schema='constant-four-root-response-mode0-ceiling-v1',status='PASS',new_lean_verification=False,scope='Upper bound for the specified cell-independent worst-box response table and old central15 mask, for any field in[0,1]. It does not exclude actual coherent-phase sources, covering survivors, other bounds, or a new sequential120 kernel.',source_sha256={name:pin},program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),primes=Q,unary_masses={str(q):str(Z[q])for q in Q},pair_caps={str(e):str(beta[e])for e in E},all_induced_count=len(all_induced),minimum_induced_normalized_polynomial=str(min(all_induced)),responses=list(map(str,H)),mode0_coefficients=list(map(str,C[:32])),complete_nonnegative_fee_count=sum(c>0 for c in C),g=str(g),empty_mass=str(H[0]),mode0_fee=str(mode0_fee),mode0_reserve=str(A),weak_corner=weak,old_mask_live_mass=str(mass),complete_gate_upper=str(upper),complete_gate_upper_decimal=float(upper),public_target=str(target),strict_deficit=str(target-upper),checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=record['check_count'],A=str(A),upper=str(upper),upper_decimal=float(upper),target=str(target),strict_deficit=str(target-upper),minimum_induced=record['minimum_induced_normalized_polynomial'])))
