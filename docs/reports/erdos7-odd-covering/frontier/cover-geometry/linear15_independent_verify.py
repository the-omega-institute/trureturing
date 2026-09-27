#!/usr/bin/env python3
"""Independent actual-CRT/source/category audit and selector-dual recomputation."""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations,product
from math import prod
from hashlib import sha256
import json,sys
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
parser=ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=HERE,
                    help='directory containing the producer result, dual and648 input')
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
CERT=args.directory/'linear15_exact_boundary_obstruction.json'
DUAL=args.directory/'linear15_exact_factor_dual_weights.json'
SRC=args.directory/'induced_square_pair_boundary_certificate.json'
raw=CERT.read_bytes();doc=json.loads(raw);draw=DUAL.read_bytes();dual=json.loads(draw)
sraw=SRC.read_bytes();source=json.loads(sraw)
checks={}
def need(name,claim):
    if not claim:raise RuntimeError(name)
    checks[name]=checks.get(name,0)+1
need('pinned_complete_fee_source',sha256(sraw).hexdigest()=='1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
need('same_dual',sha256(draw).hexdigest()==doc['dual_sha256'])
need('pinned_selector_dual',sha256(draw).hexdigest()=='718782274441fdfe7be9fc10b12efc81ea4d81df03ca8dc99b01ca1433581783')
need('producer_input_attribution',doc['source_sha256']==sha256(sraw).hexdigest())
need('producer_result_kind',doc['schema']=='linear15-fixed-gate-obstruction-v1'
     and doc['status']=='PASS' and doc['conclusion_kind']=='fixed-sufficient-criterion-obstruction')
need('producer_check_receipt',doc['check_count']==12089==sum(doc['checks'].values()))
need('producer_scope_flags',doc['new_lean_verification'] is False
     and doc['unrestricted_erdos7_resolved'] is False and doc['actual_fixture_covering'] is False)
fixture=doc['fixture'];originals={row['modulus']:row for row in fixture}
need('distinct_odd_originals',len(fixture)==len(originals)==183 and all(m>1 and m%2 for m in originals))
for m,row in originals.items():
    need('CRT_modulus',prod(d for a,d in row['components'])==m)
    need('CRT_reduced_phase',0<=row['residue']<m)
    for a,d in row['components']:need('CRT_phase',row['residue']%d==a)
P=(3,5,7,11,13,17,19,23,29,31);qs=(7,11,13,17,19)
def prime_power(n):
    for p in P:
        e=0
        while n%p==0:n//=p;e+=1
        if n==1:return p,e
    raise RuntimeError('component not a declared prime power')
parsed=[]
for row in fixture:
    pieces={}
    for a,m in row['components']:
        p,e=prime_power(m);need('one_power_per_coordinate',p not in pieces);pieces[p]=(e,a)
    parsed.append((row,pieces))
pures={p:[] for p in P}
for row,pieces in parsed:
    if len(pieces)==1:
        p=next(iter(pieces));e,a=pieces[p];pures[p].append((e,a))
for p in P:
    for (e,a),(f,b) in combinations(pures[p],2):
        need('same_prime_pure_cylinders_disjoint',a%p**min(e,f)!=b%p**min(e,f))

def leaf(p,i):return p*(i%p)+i//p
w=[Q(2,9),Q(2,9),Q(2,9),Q(0),Q(1,9),Q(2,9)]
v=[Q(4,75)]*20;v[5]=Q(0);v[6]=Q(3,75)
need('normalized_central_corner',sum(w)==sum(v)==1)
central_capacity={}
for p,weights,cap in [(3,w,Q(2)),(5,v,Q(4,3))]:
    capacities=[]
    for i,x in enumerate(weights):
        a=leaf(p,i)
        if any(e<=2 and a%p**e==b for e,b in pures[p]):haar=Q(0)
        else:haar=Q(1,p*p)-sum((Q(1,p**e) for e,b in pures[p] if e>2 and b%(p*p)==a),Q(0))
        capacities.append(cap*haar)
        need('corner_supported_density_realization',0<=x<=cap*haar)
    eps=Q(1,3**12) if p==3 else Q(1,3*5**12)
    need('finite_capacity_surplus',sum(capacities)==1+eps)
    weak=4 if p==3 else 6
    need('only_weak_capacity_differs',all(capacities[i]==weights[i]+(eps if i==weak else 0) for i in range(len(weights))))
    central_capacity[p]=capacities
coords=[(i,j) for i in range(6) for j in range(20) if w[i] and v[j] and not(leaf(3,i)%3==0 and leaf(5,j)%5==0)]
need('complete_central_support',len(coords)==80)
# An explicit CRT-compatible survivor demonstrates the fixture itself is not covering.
local_survivor={3:0,5:6,7:6,11:6,13:6,17:6,19:6,23:1,29:1,31:1}
# Reconstruct the simultaneous residue by incremental CRT; the producer uses
# a direct cofactor sum. No producer function or proof routine is imported.
resolving={p:max([p]+[p**pcs[p][0] for row,pcs in parsed if p in pcs]) for p in P}
residue=0;modulus=1
for p in P:
    power=resolving[p]
    residue+=modulus*((local_survivor[p]-residue)*pow(modulus,-1,power)%power)
    modulus*=power
    need('incremental_survivor_CRT',0<=residue<modulus and residue%power==local_survivor[p])
need('producer_survivor_local_values',
     {int(p):x for p,x in doc['actual_survivor']['local_residues'].items()}==local_survivor)
need('producer_survivor_resolving_powers',
     {int(p):x for p,x in doc['actual_survivor']['resolving_prime_powers'].items()}==resolving)
need('producer_survivor_full_CRT',doc['actual_survivor']['lcm']==modulus
     and doc['actual_survivor']['residue']==residue)
for original,row in originals.items():
    need('global_actual_survivor',residue%original!=row['residue'])
for row,pcs in parsed:
    need('explicit_actual_survivor',any(local_survivor[p]%p**e!=a for p,(e,a) in pcs.items()))
# Isolate the actual20 square-pair originals by arity/degrees, not labels.
pairs=[]
for row,pcs in parsed:
    if len(pcs)==2 and set(pcs)<=set(qs) and sorted(e for e,a in pcs.values())==[1,2]:pairs.append((row,pcs))
need('complete_square_pair_inventory',len(pairs)==20)
# Explicit source mass at every q^2 prefix, including every finite pure tail.
prefix_weights={}
for p in qs:
    masses={}
    for x in range(p*p):
        root=x%p
        if any(e==1 and root==a for e,a in pures[p]):masses[x]=Q(0);continue
        root_haar=Q(1,p)-sum((Q(1,p**e) for e,a in pures[p] if e>=2 and a%p==root),Q(0))
        prefix_haar=Q(1,p*p)-sum((Q(1,p**e) for e,a in pures[p] if e>=2 and a%(p*p)==x),Q(0))
        need('actual_pure_prefix_haar',root_haar>0 and prefix_haar>=0)
        masses[x]=prefix_haar/((p-1)*root_haar)
    need('actual_root_balanced_source_mass',sum(masses.values())==1)
    for root in range(1,p):need('balanced_actual_first_roots',sum(masses[x] for x in masses if x%p==root)==Q(1,p-1))
    caproot=4 if p==7 else 8
    clean=masses[caproot+2*p];claimed=Q(1,p*(p-2))
    need('clean_actual_deep_cap',claimed*(1-Q(1,10**9))<clean<claimed)
    prefix_weights[p]=masses

def central_active(pcs,l,m):
    for p,i in [(3,l),(5,m)]:
        if p in pcs:
            e,a=pcs[p]
            if leaf(p,i)%p**e!=a:return False
    return True

# Force roots from literal unary and retained pair clauses. Check all non1
# candidate values for each coordinate; a contradiction uses either unary or
# the pair of clauses with mutually incompatible values at one other endpoint.
retained=[]
for row,pcs in parsed:
    outside=set(pcs)&set(qs)
    if len(outside)==1 and row['label'].split(':')[0] in ['3q','5q','15q','9q','25q']:retained.append((row,pcs))
    if len(outside)==2 and all(pcs[p][0]==1 for p in outside):retained.append((row,pcs))
need('retained_inventory',len(retained)==45)
for l,m in coords:
    clauses=[]
    for row,pcs in retained:
        if central_active(pcs,l,m):clauses.append({p:a for p,(e,a) in pcs.items() if p in qs})
    need('all_one_root_solution',all(1 in clause.values() for clause in clauses))
    for p in qs:
        for alternative in range(2,p):
            residual=[]
            for clause in clauses:
                if p in clause:
                    if clause[p]==alternative:continue
                    residual.append({q:a for q,a in clause.items() if q!=p})
            impossible=any(not c for c in residual)
            singleton={}
            for c in residual:
                if len(c)==1:
                    q,a=next(iter(c.items()));singleton.setdefault(q,set()).add(a)
            impossible=impossible or any(len(s)>1 for s in singleton.values())
            need('unique_root_for_all_live_alternatives',impossible)
# Literal source-category enumeration. Membership bit e is set exactly when
# this coordinate matches its actual CRT component in square-pair originale.
H=[[] for _ in range(32)]
for l,m in coords:
    grouped=[]
    for p in qs:
        unaries=[]
        for row,pcs in parsed:
            outside=set(pcs)&set(qs)
            if outside=={p} and len(pcs)>1 and central_active(pcs,l,m):unaries.append(pcs[p])
        groups={}
        for x,mass in prefix_weights[p].items():
            if not mass or x%p==1:continue
            if any(x%p**e==a for e,a in unaries):continue
            mask=0
            for k,(row,pcs) in enumerate(pairs):
                if p in pcs:
                    e,a=pcs[p]
                    if x%p**e==a:mask|=1<<k
            groups[mask]=groups.get(mask,Q(0))+mass
        need('six_actual_membership_categories',len(groups)==6)
        integer_groups=[]
        for mask,mass in groups.items():
            scaled=mass*p*(p-1);need('actual_category_integer_mass',scaled.denominator==1 and scaled>=0)
            integer_groups.append((mask,scaled.numerator))
        grouped.append(integer_groups)
    for support in range(32):
        U=[i for i in range(5) if not(support>>i&1)]
        numerator=0
        for states in product(*(grouped[i] for i in U)):
            used=0;weight=1
            for mask,mu in states:
                if used&mask:weight=0;break
                used|=mask;weight*=mu
            numerator+=weight
        denominator=prod(qs[i]*(qs[i]-1) for i in U)
        value=Q(numerator,denominator)
        need('literal_CRT_induced_response',value==Q(doc['induced_responses'][support][len(H[support])]))
        need('strictly_positive_induced_response',0<value<=1)
        H[support].append(value)
need('conditional_survivor_minimum',min(H[0])==Q(doc['minimum_actual_conditional_survivor'])>Q(355,1000))
# Exact512 array and all menu indices reconstructed independently.
g=Q(200163067,201247200)
C=[Q(x) for x in source['unchanged512_coefficients']]
for i,p in enumerate(qs):
    if p!=7:C[9*32+(1<<i)]-=g*Q(1,p*(p-2))
need('all512_fees_match',len(C)==512 and min(C)>=0 and [str(x) for x in C]==doc['complete512_coefficients'])
def menu(weights,p,deep):
    whole=[list(weights)]
    roots=[[x if i//p==root else Q(0) for i,x in enumerate(weights)] for root in range(len(weights)//p)]
    leaves=[];deep_leaves=[]
    for i,x in enumerate(weights):
        if x:
            leaves.append([x if j==i else Q(0) for j in range(len(weights))])
            deep_leaves.append([deep if j==i else Q(0) for j in range(len(weights))])
    return [whole,roots,leaves,deep_leaves]
mx=menu(w,3,Q(1));my=menu(v,5,Q(4,5))
selectors=[]
for mode in range(16):
    aa,bb=divmod(mode,4)
    selectors.append([[x[l]*y[m] for l,m in coords] for x in mx[aa] for y in my[bb]])
    need('selector_mass_at_most_one',all(sum(s)<=1 for s in selectors[-1]))
D=dual['denominator'];need('dyadic_denominator',D==2**40)
need('no_unrecognized_fee_rows',all(0<=int(j)<512 for j in dual['weights']))
k=[g*w[l]*v[m]*H[0][ci] for ci,(l,m) in enumerate(coords)]
for j,coef in enumerate(C):
    mode,support=divmod(j,32)
    weights=dual['weights'].get(str(j),[])
    need('dual_subprobability',all(isinstance(n,int) and n>0 for si,n in weights) and sum(n for si,n in weights)<=D)
    for si,n in weights:
        need('valid_selector_index',isinstance(si,int) and 0<=si<len(selectors[mode]))
        for ci,x in enumerate(selectors[mode][si]):k[ci]-=coef*Q(n,D)*x*H[support][ci]
need('exact_linear_dual_coefficients',[str(x) for x in k]==doc['dual_linear_coefficients'])
upper=sum(max(Q(0),x) for x in k)
need('exact_dual_upper',upper==Q(doc['exact_corner_gate_upper']))
eps3=Q(1,3**12);eps5=Q(1,3*5**12)
perturbation=2*(g+sum(C))*(eps3+eps5)
need('uniform_perturbation',perturbation==Q(doc['central_capacity_perturbation']))
need('uniform_gate_upper',upper+perturbation==Q(doc['uniform_gate_upper'])<Q(1,300))
network=Q(397,50000)+Q(1,65536)+Q(8,3)*Q(19740202146111572828188083,495176015714152109959649689600)
need('fixed_budget_comparison',Q(1,300)<network==Q(doc['r4_network_budget']))
result=dict(schema='linear15-independent-verification-v1',status='PASS',producer_reported_checks=doc['check_count'],producer_sha256=doc['producer_sha256'],verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),check_count=sum(checks.values()),checks=checks,fixture_originals=len(fixture),source_sha256=sha256(sraw).hexdigest(),reviewed_result_sha256=sha256(raw).hexdigest(),dual_sha256=sha256(draw).hexdigest(),explicit_survivor=dict(local_residues=local_survivor,resolving_prime_powers=resolving,lcm=modulus,residue=residue),minimum_actual_H=str(min(H[0])),exact_dual_upper=str(upper),uniform_upper=str(upper+perturbation),fixed_network_upper_budget=str(network),new_lean_verification=False,scope='Obstruction only to the fixed complete512 response gate followed by the stated fixed647 upper budget, within the specified coordinate-product source and cellwise central thinning class. It does not assess the separate budget of Report651.')
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=result['check_count'],min_actual_H=float(min(H[0])),dual_upper=float(upper),uniform_upper=float(upper+perturbation),fixed_network_upper_budget=float(network)),indent=2))
