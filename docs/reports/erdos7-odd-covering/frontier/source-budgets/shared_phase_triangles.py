"""Exact shared-residue maximization for a finite graph of CRT triangles."""
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

CERTIFICATE='certificates/source_norms/source-budgets/shared_phase_triangles.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/66-shared-phase-triangles-and-common-center-obstruction.md', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md')

def optimize_triangles(mass, prime_pairs):
    """Optimize distinct (p,q,pq) triangles sharing their prime residues."""
    prime_pairs=tuple(tuple(e) for e in prime_pairs)
    require(len(set(prime_pairs))==len(prime_pairs),'distinct triangle edges')
    primes=tuple(sorted({p for e in prime_pairs for p in e}))
    composites=tuple(p*q for p,q in prime_pairs)
    require(len(set(composites))==len(composites) and not set(primes)&set(composites),
            'distinct composite variables disjoint from the shared pure variables')
    require(all(gcd(p,q)==1 for p,q in prime_pairs),'coprime triangle coordinates')
    moduli=tuple(sorted(set(primes)|set(composites)))
    require(set(mass)==set(moduli),'exact selected marginal inventory')
    totals={sum(v,F(0)) for v in mass.values()}
    require(len(totals)==1 and all(len(v)==m and min(v)>=0 for m,v in mass.items()),
            'one nonnegative finite measure represented by complete marginals')
    for p,q in prime_pairs:
        for d in (p,q):
            require(all(sum((mass[p*q][b] for b in range(p*q) if b%d==a),F(0))==mass[d][a]
                        for a in range(d)),'exact common-law marginal projection')
    D=lcm(*(v.denominator for row in mass.values() for v in row))
    w={m:[int(v*D) for v in row] for m,row in mass.items()}
    edges={};edge_records=[]
    for p,q in prime_pairs:
        for a,b in product(range(p),range(q)):
            center=next(c for c in range(p*q) if c%p==a and c%q==b)
            values=[(3+2*(c%p==a)+2*(c%q==b))*v for c,v in enumerate(w[p*q])]
            best=max(values)
            args=[c for c,v in enumerate(values) if v==best]
            value=2*w[p*q][center]+best
            edges[p,q,a,b]=(value,args)
            edge_records.append({'primes':[p,q],'pure_residues':[a,b],
                                 'crt_residue':center,'maximum_exact':str(F(value,D)),
                                 'composite_maximizers':args})
    best=-1;maximizers=[];pure_rows=[]
    for pure_values in product(*(range(p) for p in primes)):
        pure=dict(zip(primes,pure_values))
        chosen=[edges[p,q,pure[p],pure[q]] for p,q in prime_pairs]
        score=3*sum(w[p][pure[p]] for p in primes)+sum(v for v,args in chosen)
        local=list(product(*(args for v,args in chosen)))
        pure_rows.append({'pure_residues':list(pure_values),'maximum_exact':str(F(score,D)),
                          'composite_maximizers':[list(v) for v in local]})
        layouts=[]
        for comp in local:
            layout=dict(pure);layout.update(zip(composites,comp))
            layouts.append([layout[m] for m in moduli])
        if score>best:best=score;maximizers=layouts
        elif score==best:maximizers.extend(layouts)
    independent=3*sum(max(w[p]) for p in primes)+9*sum(max(w[m]) for m in composites)
    require(best<=independent,'independent cylinder maxima upper-bound every selected layout')
    return {'selected_moduli':list(moduli),'prime_pairs':[list(e) for e in prime_pairs],
            'selected_pairs':[[p,q] for p,q in prime_pairs]+
                             [[p,p*q] for p,q in prime_pairs]+[[q,p*q] for p,q in prime_pairs],
            'head_survival':str(next(iter(totals))),'common_denominator':str(D),
            'pure_assignment_count':len(pure_rows),'full_layout_count':prod(moduli),
            'exact_selected_maximum':str(F(best,D)),
            'independent_upper_exact':str(F(independent,D)),
            'kappa_exact':str(F(independent-best,D)),
            'attaining_layouts':maximizers,'fixed_pure_records':pure_rows,
            'conditional_edge_records':edge_records}


def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    hybrid=ceiling['hybrid'];threshold=ceiling['thresholds']
    moduli=(3,5,7,15,21,35)
    mass={r['modulus']:list(map(F,r['all_residue_masses'])) for r in literal['records'] if r['modulus'] in moduli}
    result=optimize_triangles(mass,((3,5),(3,7),(5,7)))
    require(len(result['selected_pairs'])==len(set(tuple(sorted(e)) for e in result['selected_pairs']))==9,
            'each of the nine selected pair terms is replaced once')
    updates={r['modulus']:r for r in hybrid['updates']}
    require(all(F(updates[m]['exact_maximum'])==max(mass[m]) for m in moduli),
            'the previous hybrid uses these exact six maxima in its termwise bound')
    h=F(result['head_survival']);epsilon=1-h
    require(h==F(literal['head_survival']),'unchanged actual survivor submeasure')
    kappa=F(result['kappa_exact']);old_credit=F(hybrid['hybrid_Delta_lower'])
    new=old_credit+kappa
    Jh=F(budget['exact_initial_head_second'])
    old=next(r for r in curve['records'] if r['B']==16384)
    U=F(old['J_upper'])/Jh
    require(Jh==F(threshold['head_moment_exact']) and U==F(threshold['tail_moment_upper_exact']),
            'same original complete-height head moment and directed tail factor')
    T,C,E=map(F,(old['T_lower'],old['C_upper'],old['E7_upper']))
    require(T>1 and U>=1 and Jh-epsilon-new>=h,'positive residual moment before tail multiplication')
    scores=[]
    for extra,tr in zip((F(0),E),threshold['records']):
        require(h-C-extra>0,'same-law survivor mass lower bound is positive')
        needed=Jh-epsilon-((T-1)*(h-C-extra)+h)/U
        require(needed==F(tr['Delta_strict_threshold_exact']),'fresh directed threshold algebra')
        score=epsilon+C+extra+(U*(Jh-epsilon-new)-h)/(T-1)
        require((score<1)==(new>needed),'strict criterion agrees with achieved credit')
        scores.append({'D7':bool(extra),'score_exact':str(score),'score_decimal':float(score),
                       'required_Delta':str(needed),'remaining_Delta_gap':str(needed-new),
                       'passes':score<1})
    result.update(schema='shared-phase-triangles-v1',status='PASS',
                  old_mixed_credit=str(old_credit),enhanced_credit=str(new),
                  enhanced_credit_decimal=float(new),kappa_decimal=float(kappa),scores=scores,
                  selected_maximum_decimal=float(F(result['exact_selected_maximum'])),
                  independent_upper_decimal=float(F(result['independent_upper_exact'])),
                  scope='Six unary and nine pair terms under the unchanged actual64 survivor submeasure. All other full-layout bounds remain unchanged. No common-center restriction or unrestricted covering conclusion.')
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
