"""Independent exhaustive verification by literal CRT intersection tables."""
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

CERTIFICATE='certificates/source_norms/source-budgets/shared_phase_triangles_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/66-shared-phase-triangles-and-common-center-obstruction.md', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'certificates/source_norms/source-budgets/shared_phase_triangles.json', 'frontier/source-budgets/shared_phase_triangles.py')



def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    hybrid=ceiling['hybrid'];threshold=ceiling['thresholds']
    candidate=ctx.fresh('certificates/source_norms/source-budgets/shared_phase_triangles.json','frontier/source-budgets/shared_phase_triangles.py')
    START=time.monotonic()
    MODULI=(3,5,7,15,21,35)
    TRIANGLES=((3,5,15),(3,7,21),(5,7,35))
    mass={r['modulus']:list(map(F,r['all_residue_masses'])) for r in literal['records'] if r['modulus'] in MODULI}
    h=F(literal['head_survival'])
    require(set(mass)==set(MODULI) and all(len(v)==m and sum(v,F(0))==h and min(v)>=0 for m,v in mass.items()),'six nonnegative tables for one complete H submeasure')
    for p,q,m in TRIANGLES:
        for prime in (p,q):
            require(all(sum((mass[m][b] for b in range(m) if b%prime==a),F(0))==mass[prime][a] for a in range(prime)),'exact shared prime marginal projection')
    pairs=[tuple(sorted(pair)) for tri in TRIANGLES for pair in combinations(tri,2)]
    require(len(pairs)==len(set(pairs))==9 and len(MODULI)==6,'six unary and nine distinct pair terms, no double counting')
    D=lcm(*(x.denominator for values in mass.values() for x in values))
    integer={m:[(x*D).numerator for x in values] for m,values in mass.items()}
    require(all(F(a,D)==b for m in MODULI for a,b in zip(integer[m],mass[m])),'one exact common integer denominator')

    # General literal intersection tables, without using the special formula.
    intersection={}
    for d,e in pairs:
        modulus=lcm(d,e)
        table=[]
        for a in range(d):
            row=[]
            for b in range(e):
                shared=[x for x in range(modulus) if x%d==a and x%e==b]
                require(len(shared)<=1,'each compatible fixed intersection is one lcm residue')
                row.append(integer[modulus][shared[0]] if shared else 0)
            table.append(row)
        intersection[d,e]=table

    fixed_pure_records=[]
    global_max=-1
    maximizers=[]
    enumerated=0
    common_center_max=-1
    common_center_layout=None
    for a3,a5,a7 in product(range(3),range(5),range(7)):
        require(time.monotonic()-START<60,'complete six-residue audit within resource guard')
        chosen={3:a3,5:a5,7:a7}
        pure=3*sum(integer[p][chosen[p]] for p in (3,5,7))
        pure_pairs=2*sum(intersection[p,q][chosen[p]][chosen[q]] for p,q,m in TRIANGLES)
        direct_vectors=[]
        formula_edges=[]
        centers=[]
        for p,q,m in TRIANGLES:
            direct_vectors.append([3*integer[m][b]+2*intersection[p,m][chosen[p]][b]+2*intersection[q,m][chosen[q]][b] for b in range(m)])
            center=next(x for x in range(m) if x%p==chosen[p] and x%q==chosen[q])
            centers.append(center)
            formula_edges.append(2*integer[m][center]+max((3+2*(b%p==chosen[p])+2*(b%q==chosen[q]))*integer[m][b] for b in range(m)))
        predicted=pure+sum(formula_edges)
        direct_best=-1
        local_maximizers=[]
        for b15,b21,b35 in product(range(15),range(21),range(35)):
            score=pure+pure_pairs+direct_vectors[0][b15]+direct_vectors[1][b21]+direct_vectors[2][b35]
            enumerated+=1
            if score>direct_best:
                direct_best=score;local_maximizers=[(b15,b21,b35)]
            elif score==direct_best:
                local_maximizers.append((b15,b21,b35))
        require(predicted==direct_best,'proposed elimination formula equals full fixed-pure enumeration')
        if direct_best>global_max:
            global_max=direct_best
            maximizers=[(a3,a5,a7,*b) for b in local_maximizers]
        elif direct_best==global_max:
            maximizers.extend((a3,a5,a7,*b) for b in local_maximizers)
        fixed_pure_records.append({'pure_residues':[a3,a5,a7],'maximum_exact':str(F(direct_best,D)),'composite_maximizers':[list(b) for b in local_maximizers]})
        centered=pure+pure_pairs+sum(v[b] for v,b in zip(direct_vectors,centers))
        if centered>common_center_max:
            common_center_max=centered
            common_center_layout=[a3,a5,a7,*centers]
    require(len(fixed_pure_records)==105 and enumerated==1157625,'complete finite assignment inventory')
    S=F(global_max,D)
    independent=3*sum((max(mass[p]) for p in (3,5,7)),F(0))+9*sum((max(mass[m]) for m in (15,21,35)),F(0))
    kappa=independent-S
    require(kappa>=0,'independent maxima relax every allowed layout')
    mixed=F(hybrid['hybrid_Delta_lower'])
    enhanced=mixed+kappa
    Jh,U=F(threshold['head_moment_exact']),F(threshold['tail_moment_upper_exact'])
    require(Jh==F(budget['exact_initial_head_second']),'unchanged exact full-height head moment')
    epsilon=1-h
    cur=next(r for r in curve['records'] if r['B']==16384)
    T,C,E=map(F,(cur['T_lower'],cur['C_upper'],cur['E7_upper']))
    require(U*Jh==F(cur['J_upper']) and Jh-epsilon-enhanced>=h,'same directed positive-product comparison')
    scores=[]
    for extra,tr in zip((F(0),E),threshold['records']):
        needed=F(tr['Delta_strict_threshold_exact'])
        score=epsilon+C+extra+(U*(Jh-epsilon-enhanced)-h)/(T-1)
        require((score<1)==(enhanced>needed),'new achieved lower credit compared with actual sufficient threshold')
        scores.append({'D7':bool(extra),'score_exact':str(score),'score_decimal':float(score),'required_Delta':str(needed),'remaining_Delta_gap':str(needed-enhanced),'passes':score<1})
    require(candidate['fixed_pure_records']==fixed_pure_records,'all 105 conditional maxima and every attaining composite tuple')
    require(candidate['attaining_layouts']==[list(x) for x in maximizers],'all global maximizing layouts')
    require(F(candidate['exact_selected_maximum'])==S and F(candidate['independent_upper_exact'])==independent,
            'independent literal enumeration agrees with both selected bounds')
    require(F(candidate['kappa_exact'])==kappa and F(candidate['enhanced_credit'])==enhanced and candidate['scores']==scores,
            'exact joint credit and both positive-product scores')
    common_center=next(x for x in range(105) if all(x%m==a for m,a in zip(MODULI,common_center_layout)))
    out={'schema':'shared-phase-triangles-independent-verification-v1','status':'PASS',
         'scope':'Direct literal CRT intersections and exhaustive six-residue layouts under the same actual64 submeasure. The common-center equality is only an observed property of this input.',
         'selected_moduli':list(MODULI),'pairs':[list(x) for x in pairs],
         'pure_assignment_count':105,'full_layout_count':enumerated,
         'exact_selected_maximum':str(S),'selected_maximum_decimal':float(S),
         'independent_upper_exact':str(independent),'independent_upper_decimal':float(independent),
         'kappa_exact':str(kappa),'kappa_decimal':float(kappa),
         'attaining_layouts':[list(x) for x in maximizers],
         'common_center_maximum_exact':str(F(common_center_max,D)),
         'common_center_maximum_decimal':float(F(common_center_max,D)),
         'common_center_layout':common_center_layout,'common_center_mod105':common_center,
         'old_mixed_credit':str(mixed),'enhanced_credit':str(enhanced),
         'enhanced_credit_decimal':float(enhanced),'scores':scores,'fixed_pure_records':fixed_pure_records}
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
