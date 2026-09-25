#!/usr/bin/env python3
"""Actual-phase obstruction to a fixed inherited gate plus product-source debit.

All 1759 depth-two Report598 mixed originals and all 190 Report603 additions
are present, as are the complete remaining 90 support-four originals. The
source is the actual product pure-survivor source. Standard library only;
explicit checks remain active under python -O. No covering counterexample.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

CORE=(3,5,7,11,13,17,19)
OUTSIDE=CORE[2:]
TAIL=(23,29,31)
CHECKS={}
EVALUATIONS=0

def require(name, condition):
    global EVALUATIONS
    EVALUATIONS+=1
    if not condition:
        raise ArithmeticError(name)
    CHECKS[name]=True

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return list(map(encode,value))
    return value

def crt(parts):
    modulus=prod(m for m,a in parts)
    residue=sum(a*(modulus//m)*pow(modulus//m,-1,m) for m,a in parts)%modulus
    require('CRT_resolves_each_component',all(residue%m==a for m,a in parts))
    return modulus,residue

def raw_cap(exponents):
    return prod(F(2,3**e) if p==3 else F(1,p-1) if e==1
                else F(1,(p-2)*p**(e-1))
                for p,e in zip(CORE,exponents) if e)

def record(exponents,kind):
    # Every old/admitted central component is zero; every old outside one.
    # Every new R central component is one; every R outside component zero.
    new=(kind=='remaining90')
    parts=[(p**e,int(new) if p in (3,5) else int(not new))
           for p,e in zip(CORE,exponents) if e]
    modulus,residue=crt(parts)
    return dict(modulus=modulus,residue=residue,exponents=exponents,
                support=sum(e>0 for e in exponents),kind=kind)

def inventory():
    old=[];add=[];remaining=[];unresolved=[]
    for exponents in product(range(3),repeat=7):
        support=sum(e>0 for e in exponents)
        if support<=1:continue
        if max(exponents[:2])<=1 or support>=5:
            old.append(record(exponents,'old598'))
        elif support==4 and (exponents[0],exponents[1]) in ((2,0),(0,2)):
            add.append(record(exponents,'added190'))
        elif support==4 and min(exponents[:2])>0 and all(e in (0,2) for e in exponents[2:]):
            add.append(record(exponents,'added190'))
        elif support==4:
            remaining.append(record(exponents,'remaining90'))
        else:
            unresolved.append(exponents)
    require('complete_mixed_depth_two_partition',
            (len(old),len(add),len(remaining),len(unresolved))==(1759,190,90,133))
    require('complete_remaining90_natural_class',all(
        min(r['exponents'][:2])>0 and max(r['exponents'][:2])==2
        and sorted(e for e in r['exponents'][2:] if e) in ([1,1],[1,2])
        for r in remaining))
    independent90={3**a*5**b*q**u*r**v
        for a,b in ((2,1),(1,2),(2,2))
        for q,r in combinations(OUTSIDE,2)
        for u,v in ((1,1),(1,2),(2,1))}
    require('independent_literal90_inventory',
            {r['modulus'] for r in remaining}==independent90 and len(independent90)==90)
    require('new190_two_slices',Counter(sum(e>0 for e in r['exponents'][:2]) for r in add)=={1:160,2:30})
    return old,add,remaining,unresolved

def source():
    pure=[dict(modulus=p,residue=p-1) for p in CORE+TAIL]
    pure.extend((dict(modulus=9,residue=7),dict(modulus=25,residue=2)))
    source3={x:F(1,5) for x in range(9) if x%3!=2 and x!=7}
    source5={x:F(1,4*sum(y%5==x%5 and y!=2 for y in range(25)))
             for x in range(25) if x%5!=4 and x!=2}
    require('actual_source3_and_source5_probability',sum(source3.values())==sum(source5.values())==1)
    require('actual_source3_complete_survivor',set(source3)=={0,1,3,4,6})
    require('actual_source5_root_balance',all(
        sum(m for x,m in source5.items() if x%5==j)==F(1,4) for j in range(4)))
    density3=F(9,5);density5=max(25*x for x in source5.values())
    require('central_density_bounds',density3<2 and density5==F(25,16)<F(5,3))
    root_masses=[sum(m for x,m in source3.items() if x%3==i) for i in range(2)]
    require('ternary_root_caps',root_masses==[F(3,5),F(2,5)] and all(F(1,3)<=x<=F(2,3) for x in root_masses))
    rho_density=density3*density5*prod(F(q,q-1) for q in OUTSIDE)
    uniform_density=2*prod(F(p,p-2) for p in CORE[1:])
    require('same_report598_density_envelope',rho_density<=uniform_density==F(3458,405))
    for q in OUTSIDE:
        # Actual pure survivor at height two: all children in q-1 roots.
        words=[x for x in range(q*q) if x%q!=q-1]
        require('outside_actual_root_counts',len(words)==q*(q-1)
                and all(sum(x%q==j for x in words)==q for j in range(q-1)))
        require('outside_complete_density_caps',F(q,q-1)<=F(q,q-2))
    return pure,source3,source5,dict(density3=density3,density5=density5,
        root_masses3=root_masses,actual_product_density=rho_density,
        inherited_density_bound=uniform_density)

def positive_common_source(core_rows, c):
    """One explicit replacement product law; all roots are fixed beforehand."""
    roots={3:(0,),5:(1,)}
    roots.update({q:tuple(r for r in range(q) if r not in (1,q-1))
                  for q in OUTSIDE})
    require('positive_source_has_allowed_roots',all(roots[p] for p in CORE))
    require('positive_source_exactly_one_old_bad_root',roots[3]==(0,)
            and 0 not in roots[5] and all(1 not in roots[q] for q in OUTSIDE))
    for row in core_rows:
        m,a=row['modulus'],row['residue']
        mass=F(1)
        for p in CORE:
            exponent=0
            while m%p==0:
                m//=p;exponent+=1
            if exponent:
                mass*=F(1,len(roots[p])*p**(exponent-1)) if a%p in roots[p] else F(0)
        require('positive_source_exact_literal_avoidance',m==1 and mass==0)
    factors={}
    for p in CORE:
        root_count=len(roots[p])
        cap=lambda e: F(1) if e==0 else F(1,root_count*p**(e-1))
        nonunit=F(p*(3*p-1),root_count*(p-1)**2)
        for height in (0,1,2,3,10):
            prefix=sum(((2*e+1)*cap(e) for e in range(1,height+1)),F(0))
            ratio=F(1,p)
            tail=F(1,root_count*p**height)*(
                F(2*height+3)/(1-ratio)+2*ratio/(1-ratio)**2)
            require('query_geometric_prefix_tail_exact',prefix+tail==nonunit)
            pairs=sum((cap(max(a,b)) for a,b in product(range(height+1),repeat=2)),F(0))
            require('independent_lcm_pair_count',pairs==1+prefix)
        factors[p]=1+nonunit
    require('central_query_factors',factors[3]==7 and factors[5]==F(43,8))
    query=prod(factors.values())
    require('positive_source_full_query_bound',query==F(75428728493069,424019059200))
    density=prod(F(p,len(roots[p])) for p in CORE)
    require('positive_source_density_exact',density==F(1729,45))
    g=v=F(1);controls=(F(2,5),F(9,20),F(1,2))
    for q,delta in zip(TAIL,controls):
        v-=g/(4*delta*(1-delta)*(q-1)**2)
        g*=1+F(3*q-1,(q-1)**2)/(1-delta)
    multiplier=prod(1/(1-delta) for delta in controls)
    require('independent_continuation_constants',1-v==c and multiplier==F(200,33))
    gate=1-c*query;haar=gate/(density*multiplier)
    require('positive_source_query_below_threshold',query<1/c)
    require('positive_source_gate_exact',gate==F(508267814751123689,12190378344376320000)>0)
    require('positive_source_haar_exact',haar==F(508267814751123689,2838675307397529600000)>F(1,5600))
    return dict(allowed_roots=roots,core_originals_avoided=len(core_rows),
                cylinder_caps='1/(number of retained roots times p^(e-1)), e>=1',
                all_height_query_factors=factors,complete_query_upper=query,
                source_density=density,gate_lower=gate,head_haar_lower=haar,
                strictly_greater_than=F(1,5600),
                continuation_multiplier=multiplier,
                continuation_scope='All originals touching23,29,31, with arbitrary globally fixed phases and arbitrary finite heights')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    old,added,R,excluded=inventory()
    pure,s3,s5,source_data=source()
    all_rows=old+added+R+pure
    require('all2051_original_labels_distinct',len(all_rows)==2051
            and len({r['modulus'] for r in all_rows})==2051)
    require('all_original_moduli_odd_gt_one',all(r['modulus']>1 and r['modulus']%2 for r in all_rows))
    old_by_modulus={row['modulus']:row for row in old}
    root_pair_moduli={p*q for p,q in combinations(CORE,2)}
    require('all21_old_bad_root_pairs_present',root_pair_moduli<=set(old_by_modulus)
            and len(root_pair_moduli)==21)
    for row in old+added:
        support=[p for p,e in zip(CORE,row['exponents']) if e]
        pair_modulus=support[0]*support[1]
        require('every_old_or_added_literal_contained_in_old_pair',
                row['modulus']%pair_modulus==0
                and row['residue']%pair_modulus==old_by_modulus[pair_modulus]['residue'])
    # Central predicates for 45,75,225 and every old central projection.
    central_mass=F(0)
    central_rows=[]
    for x,y in product(s3,s5):
        c45=(x==1 and y%5==1)
        c75=(x%3==1 and y==1)
        c225=(x==1 and y==1)
        active=c45 or c75 or c225
        require('central225_contained_in_both',not c225 or (c45 and c75))
        require('R_requires_both_roots_one',not active or (x%3==y%5==1))
        if active:central_mass+=s3[x]*s5[y]
        central_rows.append(dict(x3=x,x5=y,mass=s3[x]*s5[y],R_central=active))
    require('central_union_exact',central_mass==F(1,5)*F(1,4)+F(2,5)*F(1,20)-F(1,5)*F(1,20)==F(3,50))
    # Each old central-positive literal is disjoint from R. Every old
    # outside-only mixed literal lies in a two-root-one event; all ten such
    # root pair events really occur. This gives equality, not just a bound.
    old_pair_labels={q*r for q,r in combinations(OUTSIDE,2)}
    require('all_old_outside_root_pairs_present',old_pair_labels<={r['modulus'] for r in old})
    for r in old+added:
        powers=r['exponents'];a=r['residue']
        if any(powers[:2]):
            require('every_old_central_literal_disjoint_from_R',all(
                a%p==0 for p,e in zip(CORE[:2],powers[:2]) if e))
        else:
            require('old_outside_literals_imply_two_ones',sum(e>0 for e in powers[2:])>=2
                    and all(a%q==1 for q,e in zip(OUTSIDE,powers[2:]) if e))
    for r in R:
        powers=r['exponents'];a=r['residue']
        require('R_literal_implies_zero_root_pair',all(a%q==0 for q,e in zip(OUTSIDE,powers[2:]) if e))
        require('R_literal_central_predicate',all(a%(p**e)==1 for p,e in zip(CORE[:2],powers[:2])))
        root_pair=prod(q for q,e in zip(OUTSIDE,powers[2:]) if e)
        root_label=3**powers[0]*5**powers[1]*root_pair
        require('matching_R_root_pair_label_present',root_label in {z['modulus'] for z in R})
    # Exact 243 atoms: 0=root zero, 1=root one, 2=any other retained root.
    atom_rows=[];outside_joint=F(0);outside_R=F(0);outside_B=F(0)
    for atoms in product(range(3),repeat=5):
        mass=prod(F(1,q-1) if value<2 else F(q-3,q-1)
                  for q,value in zip(OUTSIDE,atoms))
        r=atoms.count(0)>=2;b=atoms.count(1)>=2
        if r:outside_R+=mass
        if b:outside_B+=mass
        if r and not b:outside_joint+=mass
        atom_rows.append(dict(categories=atoms,mass=mass,R=r,B=b))
    require('243_atom_mass_one',sum(x['mass'] for x in atom_rows)==1)
    require('outside_R_B_symmetry',outside_R==outside_B)
    # Independent bivariate generating polynomial, coefficients [x^i y^j].
    poly={(0,0):F(1)}
    for q in OUTSIDE:
        nxt={}
        for (i,j),a in poly.items():
            for di,dj,c in ((0,0,F(q-3,q-1)),(1,0,F(1,q-1)),(0,1,F(1,q-1))):
                key=(i+di,j+dj);nxt[key]=nxt.get(key,F(0))+a*c
        poly=nxt
    require('independent_two_count_polynomial',outside_joint==sum(
        (a for (i,j),a in poly.items() if i>=2 and j<=1),F(0))==F(7109,103680))
    debit=central_mass*outside_joint
    raw_R=central_mass*outside_R
    cap_R=sum((raw_cap(r['exponents']) for r in R),F())
    require('actual_joint_debit_exact',debit==F(7109,1728000))
    require('genuine_overlap_rebate',0<debit<raw_R<cap_R)
    c=F(1084133,201247200)
    K598=F(26345885990886052732242307711,9055182074115772514304000000000)
    K190=F(23005581948964911238467983,532657769065633677312000000000)
    threshold598=K598/(1-c);threshold190=K190/(1-c)
    require('joint_debit_exceeds_original598_budget',debit>threshold598)
    require('joint_debit_exceeds_190_budget',debit>threshold190)
    require('fixed_gate_debit_negative',K598-(1-c)*debit<0 and K190-(1-c)*debit<0)
    core_pure=[row for row in pure if row['modulus'] not in TAIL]
    core_rows=old+added+R+core_pure
    require('2048_core_originals',len(core_rows)==2048)
    positive=positive_common_source(core_rows,c)
    # A literal full survivor: central words1, outside words2, final words0.
    parts=[(9,1),(25,1)]+[(q*q,2) for q in OUTSIDE]+[(q,0) for q in TAIL]
    period,witness=crt(parts)
    require('every_original_resolved_by_period',all(period%r['modulus']==0 for r in all_rows))
    require('explicit_integer_avoids_all2051_classes',all(witness%r['modulus']!=r['residue'] for r in all_rows))
    result=dict(schema='joint-source-debit-obstruction-v1',scope=dict(
        head_primes=CORE,continuation_primes=TAIL,
        actual_old598_mixed_count=1759,actual_old603_additions=190,
        actual_remaining90_count=90,actual_pure_count=len(pure),total_originals=len(all_rows),
        source='Actual pure-survivor product of Report591; uniform deeper tails; no chosen query.',
        conclusion='No all-phase bound rho(R90 minus B) < K598/(1-c), hence none with K190, for this fixed inherited-gate/debit bridge.',
        exclusions=['Not a covering counterexample','Not the actual eta deletion mass','Does not rule out a phase-dependent stronger gate or a different common source','No new Lean verification']),
        phase_rule=dict(old_and_added='central coordinates0, outside coordinates1',remaining90='central coordinates1, outside coordinates0',all_phases='Globally fixed CRT residues; all listed originals present'),
        source=dict(pure_originals=pure,source3=s3,source5=s5,**source_data),
        original_classes=dict(old598=old,added190=added,remaining90=R),
        joint_geometry=dict(central_union_mass=central_mass,outside_R_mass=outside_R,
            outside_B_mass=outside_B,outside_joint_mass=outside_joint,
            raw_R_mass=raw_R,direct_cap_sum=cap_R,exact_joint_debit=debit,
            equality_for_both_B598_and_B190=True,
            old_union_exactly_21_root_pairs=sorted(root_pair_moduli),
            old_union_global_predicate='At least two bad roots among all seven coordinates; bad central root0, bad outside root1',
            added190_redundant_in_this_family=True,
            central_atoms=central_rows,outside_atoms=atom_rows),
        fixed_gate_comparison=dict(c=c,K598=K598,K190=K190,
            raw_budget598=threshold598,raw_budget190=threshold190,
            gate598_minus_debit=K598-(1-c)*debit,
            gate190_minus_debit=K190-(1-c)*debit),
        positive_common_source=positive,
        explicit_survivor=dict(period=period,word=witness,coordinate_words=parts),
        checks=CHECKS,predicate_evaluations=EVALUATIONS,
        producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(CHECKS),evaluations=EVALUATIONS,
        actual_originals=len(all_rows),joint_debit=debit,direct_cap=cap_R,
        budget598=threshold598,budget190=threshold190,
        resulting598_gate=K598-(1-c)*debit,explicit_survivor=witness)),indent=2))

if __name__=='__main__':main()
