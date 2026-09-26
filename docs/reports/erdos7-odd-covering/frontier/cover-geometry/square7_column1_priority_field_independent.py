#!/usr/bin/env python3
"""Independently certify one new square7 priority field using exact arithmetic.
Reconstructs responses by matching deletion-contraction, never reads producer
implementation, retains every literal menu choice and every labelled corner.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product,combinations
from math import lcm
from pathlib import Path
import json

p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--witness',type=Path,default=Path(__file__).with_name('square7_column1_priority_field_certificate.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(name,condition):
    checks[name]=checks.get(name,0)+1
    if not condition:raise RuntimeError(name)
names=('remaining33_global_root_exclusion_certificate.json','joint_square_pair_225_star_certificate.json','binary_leaf_pair_library_certificate.json')
pins=('dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5','4f64080de7056488b7299992ce8da2b7615410e8ddccc597ade50b323bff470d')
raw=[(a.directory/name).read_bytes() for name in names]
for b,h in zip(raw,pins):ck('canonical_source_pin',sha256(b).hexdigest()==h)
base,net,lib=map(json.loads,raw)
witness_bytes=a.witness.read_bytes();witness=json.loads(witness_bytes)
for name,h in zip(names,pins):ck('witness_source_pin',witness['source_sha256'][name]==h)
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(j for j in range(20) if j!=5)
g=F(base['constants']['g']);alpha=F(base['constants']['alpha'])
ck('same_source_network_constants',g==F(net['g'])==F(200163067,201247200) and alpha==F(net['projection_alpha'])==F(2673,110656))
r=[F(1,q-1) for q in Q];square=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*square[k] for k,q in enumerate(Q) if k]
ck('same_outside_head_masses',all(z[k]==F(net['coordinate_mass_upper'][str(q)]) for k,q in enumerate(Q)))
C=list(map(F,base['combined512_coefficients']))
for k in range(1,5):C[32*9+(1<<k)]+=g*square[k]
ck('all512_nonnegative_fees',len(C)==512 and min(C)>=0)
ck('specified_roles_and_fixed_layout',witness['square7_roles']==[1,1,5] and witness['layout']==[5]*10 and len(list(combinations(Q,2)))==10)
# Each profile is produced by one actual central leaf and column. All ten edge
# activities agree at that cell because all ten original roles have leaf5.
profiles={(l,m):2*(int(l//3==1)+int(m//5==1)+int(l==5))+int(l==5) for l,m in product(I,J)}
@lru_cache(None)
def response(n,active,remaining):
    if not remaining:return F(1)
    k=(remaining&-remaining).bit_length()-1;rest=remaining^(1<<k)
    value=(z[k]-(F(n,35) if k==0 else 0))*response(n,active,rest)
    for j in range(5):
        if rest>>j&1:
            beta=square[k]*r[j]+r[k]*square[j]+active*r[k]*r[j]
            value-=beta*response(n,active,rest^(1<<j))
    return value
H=[[response(n,active,31^T) for n,active in product(range(4),range(2))] for T in range(32)]
for T,values in enumerate(H):
    for idx,value in enumerate(values):
        ck('positive_exact_matching_response',0<value<=1)
        if T&1:ck('deleted7_role_independence',value==values[idx%2])
Hden=[lcm(*(v.denominator for v in values)) for values in H]
Hint=[[int(value*den) for value in values] for values,den in zip(H,Hden)]
for values,ints,den in zip(H,Hint,Hden):
    for value,num in zip(values,ints):ck('exact_denominator_clear',value==F(num,den))
keys=[tuple(key) for key in lib['orbit_keys']];ki={key:k for k,key in enumerate(keys)}
def orbit(i,j,l,m):
    first='r' if i<3 else str(i)
    second=('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l)
    return first,second,j//5,m//5,j==m
ck('full_orbit_inventory',len(keys)==len(ki)==180 and {orbit(i,j,l,m) for i,j,l,m in product(I,J,I,J) if not(l<3 and m<5)}==set(keys))
ck('witness_same_orbit_order',keys==list(map(tuple,witness['orbit_keys'])))
den=witness['field_denominator'];nums=witness['field_numerators']
ck('new_field_shape',den==1<<20 and len(nums)==180)
for num in nums:ck('new_field_box',isinstance(num,int) and 0<=num<=den)
def theta(i,j,l,m):return 0 if l<3 and m<5 else nums[ki[orbit(i,j,l,m)]]
for i,j,l,m in product(I,J,I,J):
    t=theta(i,j,l,m)
    ck('complete95_ternary_priority',theta(l,j,l,m)>=t)
    ck('complete95_quinary_priority',theta(i,m,l,m)>=t)
# These are the unpruned original menu vectors, scaled by9 and75.
def menus(weights,block,live,deep):
    size=len(weights)
    return ([weights],
            [[weights[k] if k//block==b else 0 for k in range(size)] for b in range(size//block)],
            [[weights[k] if k==t else 0 for k in range(size)] for t in live],
            [[deep if k==t else 0 for k in range(size)] for t in live])
claimed={(x['weak3'],x['weak5']):F(x['gate']) for x in witness['corner_gates']}
ck('all95_labelled_corners',witness['corner_count']==len(claimed)==len(witness['corner_gates'])==95 and set(claimed)==set(product(I,J)))
floor=F(193,100000);ck('declared_public_floor',F(witness['uniform_gate'])==floor)
rows=[];screen_count=0;literal_count=0
for i,j in product(I,J):
    w=[0 if l==3 else 1 if l==i else 2 for l in range(6)]
    v=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
    xm=menus(w,3,I,9);ym=menus(v,5,J,60)
    th={(l,m):theta(i,j,l,m) for l,m in product(I,J)}
    ck('actual_corner_source_mass',sum(w)==9 and sum(v)==75)
    allmenus=[]
    for xs,ys in product(xm,ym):
        coefficients=[]
        for x,y in product(xs,ys):
            coeff=[0]*8
            for l,m in product(I,J):coeff[profiles[l,m]]+=x[l]*y[m]*th[l,m]
            ck('literal_selector_mass_bound',min(coeff)>=0 and sum(coeff)<=675*den)
            coefficients.append(coeff)
        allmenus.append(coefficients)
    count=sum(map(len,allmenus));ck('all559_literal_selectors_no_pruning',count==559)
    literal_count+=count;scale=675*den
    source=F(sum(c*h for c,h in zip(allmenus[0][0],Hint[0])),scale*Hden[0])
    fee=F(0);screens=[]
    for mode,coefficients in enumerate(allmenus):
        for T in range(32):
            values=[sum(c*h for c,h in zip(coeff,Hint[T])) for coeff in coefficients]
            maximum=max(values)
            ck('complete_literal_maximum',len(values)==len(coefficients) and maximum>=0)
            value=F(maximum,scale*Hden[T]);screens.append(value)
            fee+=C[32*mode+T]*value
    gate=g*source-fee
    ck('all512_screens_paid',len(screens)==512);screen_count+=len(screens)
    ck('exact_candidate_gate',gate==claimed[i,j])
    ck('strict_public_floor_at_corner',gate>floor)
    rows.append(dict(weak3=i,weak5=j,source=str(source),complete512_fee=str(fee),gate=str(gate),screen_sha256=sha256('\n'.join(map(str,screens)).encode()).hexdigest()))
minimum=min(rows,key=lambda row:F(row['gate']));minvalue=F(minimum['gate'])
ck('exact_global_minimum',minvalue==F(witness['minimum']['gate']) and minvalue==F(236786401859826794742637401832211,108488325393566247339373363200000000))
ck('first_lexicographic_minimum',minimum['weak3']==witness['minimum']['weak3']==0 and minimum['weak5']==witness['minimum']['weak5']==6)
ck('all_complete_screens',screen_count==95*512 and literal_count==95*559)
policies=[]
for policy in net['policies']:
    fee=F(net['fee_before_arbitrary'])+F(policy['fee'])
    margin=alpha*(minvalue-fee);floor_margin=alpha*(floor-fee)
    claimed_policy=next(x for x in witness['policies'] if (x['kind'],x['K'])==(policy['kind'],policy['K']))
    ck('candidate_complete658_policy',fee==F(claimed_policy['complete_fee']) and margin==F(claimed_policy['projected_margin']))
    ck('complete658_density_at_public_floor',floor_margin>F(1,2000000) and claimed_policy['density_denominator']==2000000)
    policies.append(dict(kind=policy['kind'],K=policy['K'],complete658_fee=str(fee),projected_margin_at_exact_minimum=str(margin),projected_margin_at_public_floor=str(floor_margin),strict_density_denominator=2000000))
result=dict(schema='square7-column1-priority-field-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,source_sha256=dict(zip(names,pins)),witness_sha256=sha256(witness_bytes).hexdigest(),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),method='Exact matching deletion-contraction; exact integer clearing of Fraction denominators; all559 original selectors in each of512 screens for each of95 labelled corners; both priority inequalities over all95x95 corner/cell pairs.',square7_roles=[1,1,5],layout=[5]*10,field_denominator=den,field_numerators_sha256=sha256(json.dumps(nums,separators=(',',':')).encode()).hexdigest(),corner_count=95,literal_selector_count=literal_count,complete_screen_count=screen_count,minimum=minimum,minimum_decimal=float(minvalue),uniform_gate=str(floor),minimum_excess=str(minvalue-floor),corner_gates=rows,policies=policies,checks=checks,check_count=sum(checks.values()),scope='One fixed all9qsleaf5 layout with square7 roles(1,1,5), all other inherited head incidences and actual-source hypotheses retained. This whole95 priority family pays gamma193/100000; it does not certify arbitrary9qs layouts or unrestricted square7 roles. Complete658 policies explicitly checked; the separately verified666 schedule may consume the same public gamma under its unchanged source interface.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],check_count=result['check_count'],minimum=result['minimum_decimal'],minimum_corner=[minimum['weak3'],minimum['weak5']],corner_count=95,complete_screen_count=screen_count,uniform_gate=str(floor))))
