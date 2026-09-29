#!/usr/bin/env python3
"""Finite controls for two local support obstructions; not Lean or all-cut72 closure."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json

def need(p,msg):
    if not p: raise RuntimeError(msg)

def column_vectors(weight):
    answer=[]
    for choices in combinations_with_replacement(range(7),weight):
        c=Counter(choices)
        answer.append(tuple(c[i] for i in range(7)))
    return answer

def is_tight(v):
    return sorted(v)==[0,0,0,0,3,3,3]

def enumeration():
    expected_by_k = {
        0:['2222/12222/12222/12223','2222/12222/12222/22222','2223/12222/12222/12222'],
        2:['2222/02222/02222/11111','2222/02222/11111/11222','2222/11111/11222/11222']}

    output=[]
    for k,Z in ((0,36),(2,29)):
        rows={n:[x for x in combinations_with_replacement(range(4),n)
                 if sum(x)<=10 and (k!=0 or min(x)>0)] for n in (4,5)}
        found=[];tested=0
        for g in rows[4]:
            for ff in combinations_with_replacement(rows[5],3):
                if sum(g)+sum(map(sum,ff))!=Z: continue
                tested+=1
                p=[sum(g[:2])]+[sum(f[:3]) for f in ff]
                if min(p[i]+p[j] for i,j in combinations(range(4),2))<9-k: continue
                if k==0:
                    need(g.count(2)>=3,'three gap doubles')
                    need(any(f.count(1)>=1 and f.count(2)>=3 for f in ff),'full singleton and three doubles')
                else:
                    need(g==(2,2,2,2) and (1,1,1,1,1) in ff,'gap and clean full')
                    need(any(f in ((0,2,2,2,2),(1,1,2,2,2)) for f in ff),'exceptional full')
                found.append('/'.join(''.join(map(str,x)) for x in (g,)+ff))
        expected=expected_by_k[k]
        need(found==expected and len(found)==3,'independent shape inventory')
        output.append({'k':k,'Z':Z,'budget_fitting_shape_quadruples':tested,'shapes':found})
    return output

def vector_controls():
    singles=column_vectors(1); doubles=column_vectors(2); quadruples=column_vectors(4)
    exchange_tests=0
    for family in (singles,doubles):
        for a,b in product(family,repeat=2):
            need((all((x-y)%3==0 for x,y in zip(a,b)))==(a==b),'mod3 exchange injectivity')
            exchange_tests+=1
    parity_tests=0
    for v,u,e in product(doubles,doubles,singles):
        need(not is_tight(tuple(2*x+2*y+z for x,y,z in zip(v,u,e))),'parity obstruction')
        parity_tests+=1
    tight_public2=[]
    for p,v,e in product(doubles,doubles,singles):
        if is_tight(tuple(x+2*y+3*z for x,y,z in zip(p,v,e))):
            need(p==v and sorted(v)==[0,0,0,0,0,1,1],'public2 equals two-column gap vector')
            need(sum(x*y for x,y in zip(v,e))==0,'clean column separated')
            tight_public2.append((p,v,e))
    exception_tests=0; exception_survivors=0
    for p,v,e in tight_public2:
        survivors=[]
        for w in quadruples:
            exception_tests+=1
            if is_tight(tuple(x+y+3*z for x,y,z in zip(p,w,e))):
                survivors.append(w)
        need(survivors==[tuple(2*x for x in v)],'exception candidates in same two columns')
        exception_survivors+=len(survivors)
    return {'exchange_vector_pairs':exchange_tests,'k0_final_vectors':parity_tests,
            'k0_survivors':0,'k2_tight_public_gap_vectors':len(tight_public2),
            'k2_exception_vector_tests':exception_tests,'k2_exception_survivors':exception_survivors}

def boundary_control(short_side):
    # These are actual finite labelled leaves satisfying only the stated LOCAL tests.
    # They are not asserted to be complete literal4555 sources.
    long_family=[{(0,i),(1,i)} for i in range(3)]
    short_family=[{(0,3),(2,0)},{(1,3),(2,1)}]
    singleton={(2,2)}
    left,right=(short_family,long_family) if short_side=='gap' else (long_family,short_family)
    tests=0
    for aa in combinations(range(len(left)),2):
        for bb in combinations(range(len(right)),2):
            pieces=[singleton,left[aa[0]],left[aa[1]],right[bb[0]],right[bb[1]]]
            union=set().union(*pieces)
            need(len(union)==9 and len(union)==sum(map(len,pieces)),'boundary actual distinctness')
            need(sorted(Counter(g for g,h in union).values())==[3,3,3],'boundary ternary tree')
            tests+=1
    return {'scope':'Local selected tests only; not a global source counterexample.',
            'side_with_only_two_double_children':short_side,
            'gap_double_sets':[sorted(x) for x in left],
            'full_double_sets':[sorted(x) for x in right],
            'full_singleton':sorted(singleton),'all_required_local_tests':tests}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    out={'scope':'Ordinary finite arithmetic/support controls, not Lean and not all cut72.',
         'independent_profiles':enumeration(),'vector_checks':vector_controls(),
         'sharpness_controls':[boundary_control('gap'),boundary_control('full')]}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'profile_rows':sum(len(x['shapes'])for x in out['independent_profiles']),'vector_checks':out['vector_checks'],'boundary_controls':len(out['sharpness_controls'])}))
