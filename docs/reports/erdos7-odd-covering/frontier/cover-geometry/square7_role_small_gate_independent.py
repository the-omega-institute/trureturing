#!/usr/bin/env python3
"""Exact independent rejection of reusing four fixed fields after square7 changes.
Only the standard library is used. Every literal selector participates. Matching
responses use deletion-contraction, not the producer's expansion or intervals.
No producer implementation is read; the optional witness contains result data.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import lcm
from pathlib import Path
import json

p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--witness',type=Path,default=Path(__file__).with_name('square7_role_small_gate_certificate.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args()
checks={}
def ck(name,condition):
    checks[name]=checks.get(name,0)+1
    if not condition: raise RuntimeError(name)
names=('remaining33_global_root_exclusion_certificate.json','joint_square_pair_225_star_certificate.json','binary_leaf_pair_library_certificate.json')
pins=('dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5','4f64080de7056488b7299992ce8da2b7615410e8ddccc597ade50b323bff470d')
raw=[(a.directory/name).read_bytes() for name in names]
for b,h in zip(raw,pins): ck('canonical_source_pin',sha256(b).hexdigest()==h)
base,net,lib=map(json.loads,raw)
witness_bytes=a.witness.read_bytes();witness=json.loads(witness_bytes)
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(j for j in range(20) if j!=5)
qindex={q:k for k,q in enumerate(Q)}
g=F(base['constants']['g'])
ck('source_and_network_same_g',g==F(net['g'])==F(200163067,201247200))
ck('source_and_network_same_projection',F(base['constants']['alpha'])==F(net['projection_alpha']))
r=[F(1,q-1) for q in Q];square=[F(1,q*(q-2)) for q in Q]
z=[F(5,6)]+[F(q-2,q-1)-2*square[k] for k,q in enumerate(Q) if k]
ck('same_outside_head_masses',all(z[k]==F(net['coordinate_mass_upper'][str(q)]) for k,q in enumerate(Q)))
C=list(map(F,base['combined512_coefficients']))
for k in range(1,5): C[32*9+(1<<k)]+=g*square[k]
ck('all512_nonnegative_fees',len(C)==512 and min(C)>=0)
ck('labelled_all_leaf5_layout',witness['layout']==[5]*10 and len(list(combinations(Q,2)))==10)
# Actual activity depends on a single common central cell. The bit 'active'
# states whether that cell's leaf is5; it is never chosen independently by edge.
@lru_cache(None)
def response(n,active,remaining):
    if not remaining: return F(1)
    k=(remaining&-remaining).bit_length()-1
    rest=remaining^(1<<k)
    zk=z[k]-(F(n,35) if k==0 else 0)
    ans=zk*response(n,active,rest)
    for j in range(5):
        if rest>>j&1:
            beta=square[k]*r[j]+r[k]*square[j]+active*r[k]*r[j]
            ans-=beta*response(n,active,rest^(1<<j))
    return ans
H=[[response(n,active,31^T) for n,active in product(range(4),range(2))] for T in range(32)]
for T in range(32):
    for idx,value in enumerate(H[T]):
        n,active=divmod(idx,2)
        ck('all_exact_responses_positive',0<value<=1)
        if T&1: ck('deleted7_removes_role_dependence',value==H[T][active])
ck('uniform7_value',z[0]-F(3,35)==F(157,210))
# Clear only the response denominators, preserving exact Fraction values.
# Integer scalar products then independently evaluate full literal menus.
Hden=[lcm(*(x.denominator for x in values)) for values in H]
Hint=[[int(x*d) for x in values] for d,values in zip(Hden,H)]
for values,ints,d in zip(H,Hint,Hden):
    for value,num in zip(values,ints):ck('exact_response_denominator_clear',value==F(num,d))
keys=[tuple(key) for key in lib['orbit_keys']];ki={key:k for k,key in enumerate(keys)}
def orbit(i,j,l,m):
    first='r' if i<3 else str(i)
    second=('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l)
    return first,second,j//5,m//5,j==m
ck('full_field_orbit_inventory',len(keys)==len(ki)==180 and {orbit(i,j,l,m) for i,j,l,m in product(I,J,I,J) if not(l<3 and m<5)}==set(keys))
ck('four_whole_families',len(lib['families'])==4)
fields=[]
for fi,fam in enumerate(lib['families']):
    den=fam['denominator'];nums=fam['numerators']
    ck('field_shape',len(nums)==180 and den==(180 if fi==0 else 1<<20))
    for num in nums:ck('field_box',isinstance(num,int) and 0<=num<=den)
    def theta(i,j,l,m):
        return 0 if l<3 and m<5 else nums[ki[orbit(i,j,l,m)]]
    for i,j,l,m in product(I,J,I,J):
        t=theta(i,j,l,m)
        ck('complete95_ternary_priority',theta(l,j,l,m)>=t)
        ck('complete95_quinary_priority',theta(i,m,l,m)>=t)
    fields.append((den,{(l,m):theta(4,15,l,m) for l,m in product(I,J)}))
# Menu integer denominators are9 and75. Deep quinary mass60/75=4/5.
w=[0 if l==3 else 1 if l==4 else 2 for l in range(6)]
v=[0 if m==5 else 3 if m==15 else 4 for m in range(20)]
def menus(weights,block,live,deep):
    size=len(weights)
    return ([weights],
            [[weights[k] if k//block==b else 0 for k in range(size)] for b in range(size//block)],
            [[weights[k] if k==t else 0 for k in range(size)] for t in live],
            [[deep if k==t else 0 for k in range(size)] for t in live])
xm=menus(w,3,I,9);ym=menus(v,5,J,60)
ck('all_literal559_selectors',sum(len(xs)*len(ys) for xs,ys in product(xm,ym))==559)
ck('full_source_mass',sum(w)==9 and sum(v)==75)
specs=[('baseline',1,2,5,False),('column1',1,1,5,False),('row0_column1',0,1,5,False),('uniform_unary',1,2,5,True)]
rows=[]
for name,row,col,leaf,uniform in specs:
    candidate=next(x for x in witness['rows'] if x['name']==name)
    ck('witness_roles_and_corner',(candidate['row'],candidate['column'],candidate['leaf'],candidate['uniform_unary'])==(row,col,leaf,uniform) and candidate['weak_corner']==[4,15])
    profiles={}
    for l,m in product(I,J):
        n=3 if uniform else int(l//3==row)+int(m//5==col)+int(l==leaf)
        profiles[l,m]=2*n+int(l==5)
    gates=[]
    for fi,(den,theta) in enumerate(fields):
        allmenus=[]
        for xs,ys in product(xm,ym):
            coeffs=[]
            for x,y in product(xs,ys):
                coeff=[0]*8
                for l,m in product(I,J):coeff[profiles[l,m]]+=x[l]*y[m]*theta[l,m]
                ck('literal_selector_mass_bound',min(coeff)>=0 and sum(coeff)<=675*den)
                coeffs.append(coeff)
            allmenus.append(coeffs)
        ck('no_selector_pruning',sum(map(len,allmenus))==559)
        scale=675*den
        source=F(sum(c*h for c,h in zip(allmenus[0][0],Hint[0])),scale*Hden[0])
        fee=F(0);screens=[]
        for mode,coeffs in enumerate(allmenus):
            for T in range(32):
                vals=[sum(c*h for c,h in zip(coeff,Hint[T])) for coeff in coeffs]
                maximum=max(vals)
                ck('full_literal_maximum',maximum>=0 and len(vals)==len(coeffs))
                screen=F(maximum,scale*Hden[T]);screens.append(screen)
                fee+=C[32*mode+T]*screen
        gate=g*source-fee
        ck('all512_screens_paid',len(screens)==512)
        cg=next(x for x in candidate['family_gates'] if x['family']==fi)
        ck('candidate_exact_gate_equality',gate==F(cg['gate']))
        if name!='baseline':ck('each_existing_family_bad_corner',gate<0)
        if name=='baseline' and fi==0:ck('baseline_family0_strictly_pays',gate>F(193,100000))
        gates.append(dict(family=fi,source=str(source),complete512_fee=str(fee),gate=str(gate),gate_decimal=float(gate),literal_selector_count=sum(map(len,allmenus)),screen_count=len(screens),screen_sha256=sha256('\n'.join(map(str,screens)).encode()).hexdigest()))
    upper=max(F(x['gate']) for x in gates)
    if name!='baseline':ck('max_family_mincorner_strict_negative_upper',upper<0)
    rows.append(dict(name=name,row=row,column=col,leaf=leaf,uniform_unary=uniform,weak_corner=[4,15],family_gates=gates,max_family_mincorner_upper=str(upper),max_family_mincorner_upper_decimal=float(upper)))
result=dict(schema='square7-small-exact-gate-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,source_sha256=dict(zip(names,pins)),witness_sha256=sha256(witness_bytes).hexdigest(),verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),method='Exact Fraction matching deletion-contraction, integer denominator clearing, all559 literal selectors in all512 screens, complete95-corner priorities for each whole field.',layout=[5]*10,rows=rows,checks=checks,check_count=sum(checks.values()),scope='At one common corner each of four supplied whole families fails in each of three changed configurations. The maximum of these four corner values is an upper bound on max_family min_corner. Does not bound optimal other fields, actual survivor mass, unrestricted square7 roles, or odd covering. Negative gates are certificate failures, not source impossibility.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],check_count=result['check_count'],upper_bounds={x['name']:x['max_family_mincorner_upper_decimal'] for x in rows})))
