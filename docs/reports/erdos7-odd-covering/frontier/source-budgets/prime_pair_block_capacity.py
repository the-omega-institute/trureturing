"""Exact uniform-layout capacity bound for the seven-prime triangle block."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('shared_phase_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/prime_pair_block_capacity.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/66-shared-phase-triangles-and-common-center-obstruction.md', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'frontier/source-budgets/survivor_cylinder_queries.py', 'frontier/source-budgets/uniform_phase_capacity_input.json')



def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    hybrid=ceiling['hybrid'];threshold=ceiling['thresholds']
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    query=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    P=(3,5,7,11,13,17,19);pairs=list(combinations(P,2))
    B={r['modulus']:F(r['survivor_max_upper']) for r in query['records']}
    for r in literal['records']:
        if r['modulus']!=1:B[r['modulus']]=F(r['max_exact'])
    h=F(query['head_survival'])
    require(h==F(literal['head_survival']),'all block prices use the same actual survivor submeasure')
    unaries=set(P)|{p*q for p,q in pairs}
    require(unaries<={m for m,a in data['labels']},'every selected unary belongs to the original154 labels')
    edges=set()
    for p,q in pairs:
        for d,e in ((p,q),(p,p*q),(q,p*q)):
            require(tuple(sorted((d,e))) not in edges,'each selected unordered pair appears once')
            edges.add(tuple(sorted((d,e))))
    require(len(unaries)==28 and len(edges)==63,'complete seven-prime triangle block')
    selected_coefficients={m:3 for m in unaries}
    for d,e in edges:
        m=lcm(d,e)
        selected_coefficients[m]=selected_coefficients.get(m,0)+2
    all_coefficients={r['modulus']:r['coefficient'] for r in query['records']}
    require(all(c<=all_coefficients[m] for m,c in selected_coefficients.items()),
            'selected coefficients fit within the original hybrid selected expansion')
    U=sum((c*B[m] for m,c in selected_coefficients.items()),F(0))
    require(U==3*sum((B[p] for p in P),F(0))+9*sum((B[p*q] for p,q in pairs),F(0)),
            'the block includes each pure unary once and each composite coefficient9')
    mean=h*(3*sum((F(1,m) for m in unaries),F(0))+2*sum((F(1,d*e) for d,e in edges),F(0)))
    capacity=U-mean
    old=F(hybrid['hybrid_Delta_lower']);needed=F(threshold['records'][0]['Delta_strict_threshold_exact'])
    best_possible=old+capacity
    require(capacity>=0 and best_possible<needed,'the fixed-remainder block cannot supply the required credit')
    small={3,5,7,15,21,35}
    small_edges={tuple(sorted(e)) for p,q in combinations((3,5,7),2)
                 for e in ((p,q),(p,p*q),(q,p*q))}
    require(small<=unaries and small_edges<=edges,'the three-triangle correction is already within this block')
    records=[{'modulus':m,'coefficient':selected_coefficients[m],'hybrid_bound':str(B[m]),
              'old_upper_contribution':str(selected_coefficients[m]*B[m])} for m in sorted(unaries)]
    out={'schema':'seven-prime-triangle-replacement-capacity-v1','status':'PASS',
         'selected_unaries':sorted(unaries),'selected_edges':[list(e) for e in sorted(edges)],
         'old_selected_upper':str(U),'uniform_layout_mean':str(mean),
         'additional_credit_capacity_upper':str(capacity),'old_mixed_credit_lower':str(old),
         'maximum_new_certified_credit_upper':str(best_possible),'required_threshold':str(needed),
         'remaining_gap_lower':str(needed-best_possible),'head_survival':str(h),
         'block_bound_records':records,
         'decimals':{'old_selected_upper':float(U),'uniform_layout_mean':float(mean),
                     'additional_credit_capacity_upper':float(capacity),
                     'maximum_new_certified_credit_upper':float(best_possible),
                     'required_threshold':float(needed),'remaining_gap_lower':float(needed-best_possible)},
         'scope':'Replace only these28 unary and63 pair terms and keep every other Chapter65 hybrid bound unchanged. Independent uniform layout averaging lower-bounds the unrestricted block maximum. This limits credit from this replacement, includes the three small triangles once, and does not bound the actual full joint deficit or stronger blocks.'}
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
