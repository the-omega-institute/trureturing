#!/usr/bin/env python3
"""Exact all-source query minima for three actual shallow heads; no optimizer."""
import argparse
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json

PURE=((3,0),(9,1),(5,0),(7,0))
FAMILIES=(PURE,
    PURE+((15,11),(45,2),(21,1),(63,58),(35,3),(105,74),(315,187)),
    PURE+((15,1),(45,22),(21,1),(63,16),(35,3),(105,74),(315,47)))
MINIMA=(F(1339,768),F(47663,23808),F(18015,8704))
SIZES=(120,75,85)
OUTSIDE=(11,13,17,19,23,29)


def need(condition,message):
    if not condition:
        raise RuntimeError(message)


def calculate(witnesses=None):
    if witnesses is None:
        witnesses=Path(__file__).resolve().with_name('fibre_credit_depth_two_pair_minimax_witnesses.json')
    payload=json.loads(witnesses.read_text())
    need(len(payload['cases'])==3,'three fixed actual families')
    fees={3**j*5**e*7**f:F(5,4)**e*F(7,6)**f
          for j in range(3) for e in range(2) for f in range(2) if j+e+f}
    need(len(fees)==11,'all eleven nonunit first-cylinder query modes')
    bs=[F(1,q-2) for q in OUTSIDE]
    outside_mass=prod((1+b for b in bs),start=F(1))-1
    target=(1+sum(bs,F(0)))/outside_mass-1
    need(target==F(8038,4235),'exact six-outside scalar threshold')
    results=[]
    for index,(family,expected,size,witness) in enumerate(zip(FAMILIES,MINIMA,SIZES,payload['cases'])):
        need(witness['originals']==[list(row) for row in family],'fixed original numerical labels and phases')
        need(len({m for m,a in family})==len(family),'distinct original numerical moduli')
        need(all(m>1 and m%2 and 315%m==0 and 0<=a<m for m,a in family),'odd normalized original classes')
        live=[x for x in range(315) if all(x%m!=a for m,a in family)]
        need(len(live)==size,'actual modulo315 survivor count')
        p={int(x):F(value) for x,value in witness['primal_atoms'].items()}
        need(set(p)<=set(live),'primal supported on actual survivors')
        need(min(p.values())>=0 and sum(p.values(),F(0))==1,'primal is one probability law')
        primal=F(0)
        for m,fee in fees.items():
            masses=[F(0) for _ in range(m)]
            for x,value in p.items():
                masses[x%m]+=value
            primal+=fee*max(masses)
        declared=F(witness['lower'])
        need(declared==expected,'declared exact minimum')
        budgets={m:F(0) for m in fees}
        cover={x:F(0) for x in live}
        seen=set()
        for term in witness['dual_terms']:
            m,a,value=term['modulus'],term['phase'],F(term['weight'])
            need(m in fees and 0<=a<m and value>=0,'valid nonnegative dual phase term')
            need((m,a) not in seen,'unique dual phase address')
            seen.add((m,a))
            budgets[m]+=value
            for x in live:
                if x%m==a:
                    cover[x]+=value
        need(all(budgets[m]<=fees[m] for m in fees),'dual mode budgets')
        dual=min(cover.values())
        need(dual==primal==declared,'exact dual lower equals feasible primal upper')
        if index:
            need(dual>target,'all-source obstruction to direct scalar continuation')
        else:
            need(dual<target,'pure-only positive control')
        results.append(dict(name=witness['name'],originals=family,
            actual_survivor_count=size,query_minimum=str(dual),
            query_minimum_decimal=float(dual),gap_to_scalar_target=str(dual-target),
            primal_atoms=len(p),dual_terms=len(seen),dual_cell_checks=len(live),
            mode_budget_checks=len(fees),exact_minimax=True))
    return dict(scope='All probability laws supported on the three specified modulo315 survivor sets, with every nonternary query height and ternary query height<=2. Obstruction only to the stated direct scalar continuation.',
                method='First-cylinder pigeonhole lower and simultaneous Haar-tail upper; exact rational primal and dual certificates without an optimizer.',
                query_mode_fees={str(m):str(fee) for m,fee in sorted(fees.items())},
                outside_primes=OUTSIDE,scalar_target=str(target),
                cases=results,evidence='Ordinary proof and exact certificate verification; no new Lean verification or covering counterexample.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
        need(retained==result,'retained result agrees with exact replay')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':
    main()
