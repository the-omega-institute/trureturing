"""Exact rational endpoint-charge verification; standard-library only."""
from collections import Counter, deque
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
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('shared_root_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/shared_first9_prefix_bound.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'frontier/source-budgets/first9_prefix_edge_charges_input.json', 'certificates/source_norms/source-budgets/shared_first9_prefix_queries.json', 'frontier/source-budgets/shared_first9_prefix_queries.py', 'certificates/source_norms/source-budgets/shared_first3_root_queries.json', 'frontier/source-budgets/shared_first3_root_queries.py', 'certificates/source_norms/source-budgets/shared_first3_root_cut.json', 'frontier/source-budgets/shared_first3_root_cut.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def build_model(data):
    B = {r['modulus']: list(map(F, r['restricted_upper'])) for r in data['root']['records']}
    B.update({r['modulus']: list(map(F, r['restricted_upper'])) for r in data['queries']['records']})
    mods = [m for m, a in data['input']['labels']]
    V = sorted((m for m in mods if m % 3 == 0))
    W = [m for m in mods if m % 3]
    n = len(V)
    state = [(1, 2, 5, 7, 8) if d % 9 == 0 else (1, 2) for d in V]
    depth = [9 if d % 9 == 0 else 3 for d in V]
    require(n == 66 and sum((d == 9 for d in depth)) == 28, 'Exact shared-root certificate: n == 66 and sum((d == 9 for d in depth)) == 28')
    unary = [[3 * B[d][a] + 2 * sum((B[lcm(d, e)][a] for e in W), F(0)) for a in state[i]] for i, d in enumerate(V)]
    nextvar = n
    edges = []
    for i, j in combinations(range(n), 2):
        ia = list(range(nextvar, nextvar + len(state[i])))
        nextvar += len(ia)
        ib = list(range(nextvar, nextvar + len(state[j])))
        nextvar += len(ib)
        payoff = []
        for ai, a in enumerate(state[i]):
            for bj, b in enumerate(state[j]):
                if a % min(depth[i], depth[j]) == b % min(depth[i], depth[j]):
                    residue = a if depth[i] >= depth[j] else b
                    payoff.append((ai, bj, 2 * B[lcm(V[i], V[j])][residue]))
        edges.append((i, j, ia, ib, payoff))
    return V,W,state,depth,unary,edges,nextvar

def evaluate_charges(data, witness):
    V,W,state,depth,unary,edges,nextvar=build_model(data)
    require(witness['labels']==V and witness['states']==[list(s) for s in state],
            'charge witness uses every correct distinct numerical label and state')
    require(len(witness['edge_charges'])==len(edges)==2145,'one charge pair for every selected unordered pair')
    site=[list(row) for row in unary]
    checked=0
    for record,(i,j,ia,ib,payoff) in zip(witness['edge_charges'],edges):
        require((record['i'],record['j'])==(i,j),'canonical unordered edge order')
        left=list(map(F,record['left']));right=list(map(F,record['right']))
        require(len(left)==len(state[i]) and len(right)==len(state[j]) and min(left+right)>=0,
                'complete nonnegative charge arrays for both endpoint state spaces')
        for a,b,w in payoff:
            require(left[a]+right[b]>=w,'exact charge domination of each compatible pair payoff')
            checked+=1
        for a,c in enumerate(left):site[i][a]+=c
        for b,c in enumerate(right):site[j][b]+=c
    prices=list(map(max,site));upper=sum(prices,F(0))
    controls=[]
    for deep in (1,2,5,7,8):
        choices=[list(s).index(deep if depth[i]==9 else deep%3) for i,s in enumerate(state)]
        value=sum((unary[i][choices[i]] for i in range(len(V))),F(0))
        value+=sum((next((w for a,b,w in payoff if a==choices[i] and b==choices[j]),F(0))
                    for i,j,ia,ib,payoff in edges),F(0))
        controls.append({'deep_prefix':deep,'relaxation_score':str(value)})
    require(max(F(r['relaxation_score']) for r in controls)<=upper,'all five feasible relaxed assignments lie below the dual bound')
    states=sum(map(len,state))
    dimensions={'variables':nextvar,'constraints':checked+states,
                'nonzeros':2*checked+states+sum(len(ia)+len(ib) for i,j,ia,ib,payoff in edges)}
    return V,state,prices,upper,controls,dimensions,checked

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    query=ctx.fresh('certificates/source_norms/source-budgets/shared_first9_prefix_queries.json','frontier/source-budgets/shared_first9_prefix_queries.py')
    root_query=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_queries.json','frontier/source-budgets/shared_first3_root_queries.py')
    root_result=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_cut.json','frontier/source-budgets/shared_first3_root_cut.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    witness=ctx.read('frontier/source-budgets/first9_prefix_edge_charges_input.json')
    data={'queries':query,'root':root_query,'root_result':root_result,'input':ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json'),'hybrid':ceiling['hybrid'],'threshold':ceiling['thresholds'],'curve':curve}
    V,state,prices,upper,controls,dimensions,checked=evaluate_charges(data,witness)
    old=F(root_result['old_selected_upper']);gain=old-upper
    rootgain=F(root_result['additional_credit']);increment=gain-rootgain
    new=F(ceiling['hybrid']['hybrid_Delta_lower'])+gain
    h=F(query['head_survival']);eps=1-h
    require(h==F(root_query['head_survival']),'one unchanged full survivor submeasure')
    Jh=F(budget['exact_initial_head_second']);U=F(ceiling['thresholds']['tail_moment_upper_exact'])
    current=next(r for r in curve['records'] if r['B']==16384)
    T,loss,E=map(F,(current['T_lower'],current['C_upper'],current['E7_upper']))
    require(Jh==F(ceiling['thresholds']['head_moment_exact']) and U*Jh==F(current['J_upper']),
            'unchanged complete-height head moment and directed full moment')
    require(T>1 and U>=1 and Jh-eps-new>=h and all(h-loss-extra>0 for extra in (F(0),E)),
            'positive residual moment and same-law final-event lower masses')
    scores=[eps+loss+extra+(U*(Jh-eps-new)-h)/(T-1) for extra in (F(0),E)]
    best=max(controls,key=lambda r:F(r['relaxation_score']));lower=F(best['relaxation_score'])
    root_upper=F(root_result['new_selected_upper'])
    gap=upper-lower;room=root_upper-lower
    require(best['deep_prefix']==7 and 0<=gap<F(1276,10**9) and 0<=increment<=room<F(947127,10**9),
            'exact narrow interval for this relaxation and its possible improvement over root3')
    require(all(score>1 for score in scores),'neither retained sufficient criterion passes')
    out={'schema':'shared-first9-prefix-rational-edge-charge-v1','status':'PASS',
         'labels':V,'states':[list(s) for s in state],'old_selected_upper':str(old),
         'certified_selected_upper':str(upper),'additional_credit':str(gain),
         'improvement_over_first3_cut':str(increment),'new_total_credit_lower':str(new),
         'baseline_score':str(scores[0]),'E7_score':str(scores[1]),
         'decimals':{'old_selected_upper':float(old),'certified_selected_upper':float(upper),
                     'additional_credit':float(gain),'improvement_over_first3_cut':float(increment),
                     'new_total_credit_lower':float(new),'baseline_score':float(scores[0]),'E7_score':float(scores[1])},
         'site_prices':[str(p) for p in prices],'centered_prefix_controls':controls,
         'model_dimensions':dimensions,'compatible_pair_checks':checked,
         'relaxation_lower_control':str(lower),'rational_interval_gap':str(gap),
         'maximum_improvement_over_root3_upper':str(room),
         'scope':'Exact rational feasible charge bound and a feasible assignment lower control for the shared first3/first9-prefix relaxation under the same law. Numerical optimality and actual-layout attainment of the lower control are not claimed.'}
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
