#!/usr/bin/env python3
"""Exact finite tests of globally fixed per-label query recombination."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from math import prod
import json


def need(ok,message):
    if not ok:raise RuntimeError(message)


def cubic_formula(bit_rows, weights):
    ps=tuple(sum((weights[i]*bit_rows[i][d] for i in range(len(weights))),F(0))
             for d in range(len(bit_rows[0])))
    mean=1+sum(ps,F(0))
    correction=sum((p*(1-p)*(3*mean+1-2*p) for p in ps),F(0))
    return mean**3+correction, mean, correction


def direct_hybrid(bit_rows, weights):
    count=len(bit_rows[0])
    return sum((prod((weights[i] for i in choices),start=F(1))
                *(1+sum(bit_rows[choices[d]][d] for d in range(count)))**3
                for choices in product(range(len(weights)),repeat=count)),F(0))


def calculate():
    identity_checks=0
    for rows in product(tuple(product((0,1),repeat=3)),repeat=3):
        weights=(F(1,2),F(1,3),F(1,6))
        actual=direct_hybrid(rows,weights)
        formula,mean,correction=cubic_formula(rows,weights)
        need(actual==formula,'three-parent, three-slot exact cubic identity')
        need(correction>=0,'the variance correction is nonnegative')
        identity_checks+=1

    # Actual CRT dictionary consists of ALL divisors of 15, including the unit.
    MODS=(3,5,15)
    LAYOUTS=tuple(product(*(range(d) for d in MODS)))
    X=tuple(x for x in range(15) if x%3 and x%5)
    WEIGHTS=(F(1,2),F(1,2))
    loads={a:tuple(1+sum(x%d==phase for d,phase in zip(MODS,a)) for x in X)
           for a in LAYOUTS}
    cubes={a:sum((F(v**3,len(X)) for v in vals),F(0)) for a,vals in loads.items()}
    Gamma=max(cubes.values())
    point_cache={}
    for rows in product(tuple(product((0,1),repeat=3)),repeat=2):
        val,mean,corr=cubic_formula(rows,WEIGHTS)
        need(val==direct_hybrid(rows,WEIGHTS),'two-parent identity')
        disagreement=sum(a!=b for a,b in zip(*rows))
        need(corr==F(3,4)*mean*disagreement,'fair-pair exact Hamming correction')
        point_cache[rows]=val

    pair_count=0
    for A,B in product(LAYOUTS,repeat=2):
        formula=F(0)
        for x in X:
            rows=(tuple(int(x%d==a) for d,a in zip(MODS,A)),
                  tuple(int(x%d==b) for d,b in zip(MODS,B)))
            formula+=point_cache[rows]/len(X)
        # Each of the 8 choices fixes one full phase layout BEFORE integrating x.
        direct=sum((cubes[tuple((A,B)[choice[d]][d] for d in range(3))]/8
                    for choice in product((0,1),repeat=3)),F(0))
        need(formula==direct<=Gamma,'every globally fixed actual hybrid lies under the universal maximum')
        pair_count+=1

    # Same total loads, different slot response, on the actual residue x=1.
    small_A=(1,0);small_B=(0,1)
    small_mods=(3,5)
    small_rows=tuple(tuple(int(1%d==a) for d,a in zip(small_mods,layout))
                     for layout in (small_A,small_B))
    small_hybrid=direct_hybrid(small_rows,WEIGHTS)
    need(small_hybrid==11,'actual A/B example has random hybrid cubic 11')
    need(direct_hybrid((small_rows[0],small_rows[0]),WEIGHTS)==8,
         'identical aggregate loads do not determine label disagreement')
    coherent=(small_A[0],small_B[1])
    need((1+sum(1%d==a for d,a in zip(small_mods,coherent)))**3==27,
         'one globally fixed coherent phase recombination has cubic 27')

    # Source-centred recombination uses one independent source point per slot.
    # Marginal cylinder masses are determined by the ACTUAL old source.
    energy=F(0)
    for x in X:
        ps=tuple(F(sum(y%d==x%d for y in X),len(X)) for d in MODS)
        mean=1+sum(ps,F(0))
        energy+=(mean**3+sum((p*(1-p)*(3*mean+1-2*p) for p in ps),F(0)))/len(X)
    centred_direct=F(0)
    for centres in product(X,repeat=len(MODS)):
        layout=tuple(y%d for d,y in zip(MODS,centres))
        centred_direct+=cubes[layout]/len(X)**len(MODS)
    need(energy==centred_direct<=Gamma,'source-centred marginal energy is an actual-query mixture')

    # Boundary: identical selected actual queries do not generate all legal phases.
    L0=315*11*13*17*19*23
    DIVISORS=tuple(3**a*prod((p for p,take in zip((5,7,11,13,17,19,23),bits) if take),start=1)
                   for a in range(3) for bits in product((0,1),repeat=7))
    NONUNIT=tuple(sorted(d for d in DIVISORS if d!=1))
    need(len(DIVISORS)==384,'the complete shallow23 numerical divisor dictionary')
    selected_phases=tuple(0 if j<16 else 1 for j in range(len(NONUNIT)))
    selected_load=1+sum(0%d==a for d,a in zip(NONUNIT,selected_phases))
    full_centred_load=1+len(NONUNIT)
    G3=F(906617738995,159166336)
    need(selected_load==17 and selected_load**3<G3<full_centred_load**3,
         'selected-hybrid closure is strictly weaker than the full phase dictionary')

    out={'identity_pattern_checks':identity_checks,
         'actual_modulus':15,'nonunit_query_dictionary':MODS,'source_points':X,
         'actual_complete_layouts':len(LAYOUTS),'actual_ordered_parent_pairs':pair_count,
         'actual_universal_cubic_maximum':str(Gamma),
         'same_total_load_example':{'parent_loads':[2,2],'identical_parent_hybrid_cube':'8',
                                  'crossed_parent_hybrid_cube':'11','coherent_hybrid_cube':'27'},
         'source_centred_hybrid_cube':str(energy),
         'selected_closure_boundary':{'divisor_count':384,'same_selected_load':17,
                                      'selected_cube':17**3,'full_centred_cube':384**3},
         'scope':'Ordinary finite probability and actual fixed-phase CRT queries, not new Lean. '
                 'Selected hybrid closure is necessary but not equivalent to the full query-source hypothesis.',
         'exact_checks_passed':True}
    return out


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with complete fixed-phase query checks')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
