#!/usr/bin/env python3
"""Independently verify two whole95 priority fields for fixed column1 layouts.
Uses only pinned mathematical JSON inputs, plus explicitly supplied numerical
witnesses. Does not read producer implementations. All menus stay unpruned.
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
p.add_argument('--witness',type=Path,default=Path(__file__).with_name('square7_column1_joint_layout_priority_certificate.json'))
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
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(j for j in range(20) if j!=5)
edges=list(combinations(range(5),2));floor=F(193,100000)
g=F(base['constants']['g']);alpha=F(base['constants']['alpha'])
ck('same_source_network_constants',g==F(net['g'])==F(200163067,201247200) and alpha==F(net['projection_alpha'])==F(2673,110656))
r=[F(1,q-1) for q in Q];square=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*square[k] for k,q in enumerate(Q) if k]
ck('same_outside_head_masses',all(z[k]==F(net['coordinate_mass_upper'][str(q)]) for k,q in enumerate(Q)))
C=list(map(F,base['combined512_coefficients']))
for k in range(1,5):C[32*9+(1<<k)]+=g*square[k]
ck('all512_nonnegative_fees',len(C)==512 and min(C)>=0)
edgeindex={e:k for k,e in enumerate(edges)}
@lru_cache(None)
def response(n,mask,remaining):
    if not remaining:return F(1)
    k=(remaining&-remaining).bit_length()-1;rest=remaining^(1<<k)
    value=(z[k]-(F(n,35) if k==0 else 0))*response(n,mask,rest)
    for j in range(k+1,5):
        if rest>>j&1:
            active=(mask>>edgeindex[k,j])&1
            beta=square[k]*r[j]+r[k]*square[j]+active*r[k]*r[j]
            value-=beta*response(n,mask,rest^(1<<j))
    return value
keys=[tuple(key) for key in lib['orbit_keys']];ki={key:k for k,key in enumerate(keys)}
def orbit(i,j,l,m):
    first='r' if i<3 else str(i)
    second=('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l)
    return first,second,j//5,m//5,j==m
ck('full_orbit_inventory',len(keys)==len(ki)==180 and {orbit(i,j,l,m) for i,j,l,m in product(I,J,I,J) if not(l<3 and m<5)}==set(keys))
def field_data(den,nums):
    ck('field_shape',isinstance(den,int) and den>0 and len(nums)==180)
    for num in nums:ck('field_box',isinstance(num,int) and 0<=num<=den)
    def theta(i,j,l,m):return 0 if l<3 and m<5 else nums[ki[orbit(i,j,l,m)]]
    for i,j,l,m in product(I,J,I,J):
        t=theta(i,j,l,m)
        ck('complete95_ternary_priority',theta(l,j,l,m)>=t)
        ck('complete95_quinary_priority',theta(i,m,l,m)>=t)
    return den,tuple(nums)
def load_field(witness):
    ck('witness_same_orbit_order',keys==list(map(tuple,witness['orbit_keys'])))
    ck('witness_specified_roles',witness['square7_roles']==[1,1,5])
    return field_data(witness['field_denominator'],witness['field_numerators'])
def layout_data(layout):
    ck('fixed_labelled_layout',len(layout)==10 and all(l in I for l in layout))
    masks={l:sum(1<<e for e,label in enumerate(layout) if label==l) for l in I}
    ck('each_edge_one_common_leaf',sum(masks.values())==1023 and all(not(masks[x]&masks[y]) for x,y in combinations(I,2)))
    cellprofile={(l,m):(int(l//3==1)+int(m//5==1)+int(l==5),masks[l]) for l,m in product(I,J)}
    profiles=sorted(set(cellprofile.values()));ix={q:k for k,q in enumerate(profiles)}
    cellindex={cell:ix[profile] for cell,profile in cellprofile.items()}
    H=[[response(n,mask,31^T) for n,mask in profiles] for T in range(32)]
    for values in H:
        for value in values:ck('positive_exact_matching_response',0<value<=1)
    Hden=[lcm(*(v.denominator for v in values)) for values in H]
    Hint=[[int(value*den) for value in values] for values,den in zip(H,Hden)]
    for values,ints,den in zip(H,Hint,Hden):
        for value,num in zip(values,ints):ck('exact_denominator_clear',value==F(num,den))
    return cellindex,Hint,Hden,len(profiles)
def menus(weights,block,live,deep):
    size=len(weights)
    return ([weights],[[weights[k] if k//block==b else 0 for k in range(size)] for b in range(size//block)],[[weights[k] if k==t else 0 for k in range(size)] for t in live],[[deep if k==t else 0 for k in range(size)] for t in live])
def gate(data,field,corner):
    cellindex,Hint,Hden,profilecount=data;den,nums=field;i,j=corner
    ck('corner_in_actual95',i in I and j in J)
    w=[0 if l==3 else 1 if l==i else 2 for l in range(6)]
    v=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
    xm=menus(w,3,I,9);ym=menus(v,5,J,60)
    th={(l,m):0 if l<3 and m<5 else nums[ki[orbit(i,j,l,m)]] for l,m in product(I,J)}
    ck('actual_corner_source_mass',sum(w)==9 and sum(v)==75)
    allmenus=[]
    for xs,ys in product(xm,ym):
        coefficients=[]
        for x,y in product(xs,ys):
            coeff=[0]*profilecount
            for l,m in product(I,J):coeff[cellindex[l,m]]+=x[l]*y[m]*th[l,m]
            ck('literal_selector_mass_bound',min(coeff)>=0 and sum(coeff)<=675*den)
            coefficients.append(coeff)
        allmenus.append(coefficients)
    ck('all559_literal_selectors_no_pruning',sum(map(len,allmenus))==559)
    scale=675*den
    source=F(sum(c*h for c,h in zip(allmenus[0][0],Hint[0])),scale*Hden[0])
    fee=F(0);screens=[]
    for mode,coefficients in enumerate(allmenus):
        for T in range(32):
            values=[sum(c*h for c,h in zip(coeff,Hint[T])) for coeff in coefficients]
            maximum=max(values)
            ck('complete_literal_maximum',len(values)==len(coefficients) and maximum>=0)
            value=F(maximum,scale*Hden[T]);screens.append(value)
            fee+=C[32*mode+T]*value
    value=g*source-fee
    ck('all512_screens_paid',len(screens)==512)
    return dict(weak3=i,weak5=j,source=str(source),complete512_fee=str(fee),gate=str(value),gate_decimal=float(value),screen_sha256=sha256('\n'.join(map(str,screens)).encode()).hexdigest())
wb=a.witness.read_bytes();witness=json.loads(wb)
ck('witness_same_orbits',keys==list(map(tuple,witness['orbit_keys'])))
ck('witness_roles',witness['square7_roles']==[1,1,5])
for name,h in zip(names,pins):ck('witness_source_pin',witness['source_sha256'][name]==h)
branches={b['name']:b for b in witness['branches']}
ck('exactly_two_branches',len(witness['branches'])==len(branches)==2 and set(branches)=={'all_leaf4','all_regular0'})
results=[]
for name,expected_leaf in (('all_leaf4',4),('all_regular0',0)):
    branch=branches[name]
    ck('specified_constant_leaf_layout',branch['layout']==[expected_leaf]*10)
    ck('declared_public_floor',F(branch['uniform_gate'])==floor)
    if expected_leaf==0:
        ck('constant_one_field',branch['field_kind']=='constant_one' and len(branch['field_numerators'])==180 and all(v==branch['field_denominator'] for v in branch['field_numerators']))
    field=field_data(branch['field_denominator'],branch['field_numerators']);data=layout_data(branch['layout'])
    claimed={(row['weak3'],row['weak5']):F(row['gate']) for row in branch['corner_gates']}
    ck('all95_witness_corners',branch['corner_count']==len(claimed)==len(branch['corner_gates'])==95 and set(claimed)==set(product(I,J)))
    rows=[]
    for corner in product(I,J):
        row=gate(data,field,corner);value=F(row['gate'])
        ck('exact_candidate_gate',value==claimed[corner]);ck('strict_public_floor_at_corner',value>floor);rows.append(row)
    minimum=min(rows,key=lambda row:F(row['gate']));minvalue=F(minimum['gate'])
    ck('exact_candidate_minimum',minvalue==F(branch['minimum']['gate']))
    ck('first_lexicographic_minimum',(minimum['weak3'],minimum['weak5'])==(branch['minimum']['weak3'],branch['minimum']['weak5']))
    policies=[]
    for policy in net['policies']:
        fee=F(net['fee_before_arbitrary'])+F(policy['fee']);margin=alpha*(minvalue-fee)
        claimed_policy=next(x for x in branch['policies'] if (x['kind'],x['K'])==(policy['kind'],policy['K']))
        ck('exact_candidate658_policy',fee==F(claimed_policy['complete_fee']) and margin==F(claimed_policy['projected_margin']))
        ck('public_floor_pays_complete658',alpha*(floor-fee)>F(1,2000000))
        policies.append(dict(kind=policy['kind'],K=policy['K'],complete658_fee=str(fee),margin_at_exact_minimum=str(margin),margin_at_public_floor=str(alpha*(floor-fee))))
    results.append(dict(name=name,layout=branch['layout'],field_kind=branch['field_kind'],field_denominator=field[0],field_numerators_sha256=sha256(json.dumps(list(field[1]),separators=(',',':')).encode()).hexdigest(),corner_count=95,complete_screen_count=95*512,literal_selector_count=95*559,minimum=minimum,minimum_excess=str(minvalue-floor),uniform_gate=str(floor),corner_gates=rows,policies=policies))
result=dict(schema='square7-column1-joint-layout-priority-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,source_sha256=dict(zip(names,pins)),witness_sha256=sha256(wb).hexdigest(),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),method='Exact matching deletion-contraction on one common cell, no interval tables; all559 literal selectors and full512 fees at each of95 actual corners per branch. Both priority inequalities checked over all95x95 corner/cell pairs. Exact Fraction denominator clearing preserves all quantities.',square7_roles=[1,1,5],branch_count=2,corner_count=190,complete_screen_count=190*512,literal_selector_count=190*559,branches=results,checks=checks,check_count=sum(checks.values()),scope='Two fixed layouts only: all9qsleaf4 and all9qsregular0, with square7roles(1,1,5) and inherited actual-source/incidence hypotheses. Each uses one entire whole95 field. Both exceed publicgamma193/100000; complete658 policies explicitly checked. Separately verified666 schedule consumes that same publicgamma under unchanged source interfaces. This numerical verifier does not certify arbitrary mixed layouts or infer actual independence.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],check_count=result['check_count'],minimum={b['name']:b['minimum']['gate_decimal'] for b in results},complete_screen_count=result['complete_screen_count'])))
