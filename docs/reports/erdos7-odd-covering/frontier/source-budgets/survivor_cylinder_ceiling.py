"""Complete support counts, seven exact replacements, and the fixed independent-marginal method ceiling."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('survivor_cylinder_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/survivor_cylinder_queries.py', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    result=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked complete literal input')
    START=time.monotonic()
    old_curve=next(r for r in curve['records'] if r['B']==16384)
    Jh=F(budget['exact_initial_head_second']);J=F(old_curve['J_upper'])
    U=J/Jh;eps=1-F(result['head_survival']);h=1-eps
    T,C,E=map(F,(old_curve['T_lower'],old_curve['C_upper'],old_curve['E7_upper']))
    threshold={'head_moment_exact':str(Jh),'tail_moment_upper_exact':str(U),'records':[]}
    for extra in (F(0),E):
        s=h-C-extra
        require(T>1 and s>0 and U>=1,'same positive-product directed threshold inputs')
        needed=Jh-eps-((T-1)*s+h)/U
        threshold['records'].append({'B':16384,'D7':bool(extra),'Delta_strict_threshold_exact':str(needed),'Delta_strict_threshold_decimal':float(needed)})
    require(result['status']=='complete' and result['completed_queries']==4660 and F(result['remaining_potential'])==0,'completed one production pass')
    h=F(result['head_survival']);epsilon=1-h;delta=F(result['delta_lower'])
    records=result['records']
    require(sum((F(r['credit']) for r in records),F(0))==delta,'all exact contribution fractions sum to retained deficit')
    Jh,U=F(threshold['head_moment_exact']),F(threshold['tail_moment_upper_exact'])
    bound=Jh-epsilon-delta
    require(bound>=h,'positive full-height uniform head moment bound')
    old=next(r for r in curve['records'] if r['B']==16384)
    T,C,E=map(F,(old['T_lower'],old['C_upper'],old['E7_upper']))
    require(U*Jh==F(old['J_upper']),'same positive-product tail upper bound')
    scores=[]
    for extra,tr in zip((F(0),E),threshold['records']):
        numerator=U*bound-h
        score=epsilon+C+extra+numerator/(T-1)
        gap=F(tr['Delta_strict_threshold_exact'])-delta
        require((score<1)==(gap<0) and numerator>=0 and h-C-extra>0,'positive product transport and exact threshold agree')
        scores.append({'B':16384,'D7':bool(extra),'score':str(score),'score_decimal':float(score),'Delta_threshold':tr['Delta_strict_threshold_exact'],'remaining_Delta_gap':str(gap),'remaining_Delta_gap_decimal':float(gap),'passes':score<1})

    counts=[]
    upper=F(0)
    computed=0
    total_bits=0
    for record in records:
        m=record['modulus'];q=F(record['price']);coefficient=record['coefficient']
        if time.monotonic()-START<30:
            forbidden=0
            for d,a in data['labels']:
                if m%d==0:
                    forbidden|=(((1<<m)-1)//((1<<d)-1))<<a
            require(forbidden.bit_length()<=m and not (forbidden>>(34%m)&1),'literal CRT support count preserves the known uncovered residue')
            z=m-forbidden.bit_count()
            computed+=1
            total_bits+=m
        else:
            z=m
        lower=h/z
        require(0<z<=m and lower<=F(record['survivor_max_upper'])<=q,'finite residue-support lower bound agrees with saved strict upper bound')
        upper+=coefficient*(q-lower)
        counts.append({'modulus':m,'available_residues':z,'max_mass_lower':str(lower)})
    require(upper>=delta,'exact independent-max method lies inside certified lower and upper credit bounds')
    top=sorted(records,key=lambda r:F(r['credit']),reverse=True)[:20]
    out={'status':'PASS','production_recomputations':0,'head_moment_upper':str(bound),'head_moment_upper_decimal':float(bound),'certified_delta_lower':str(delta),'certified_delta_lower_decimal':float(delta),'scores':scores,'independent_marginal_method_delta_upper':str(upper),'independent_marginal_method_delta_upper_decimal':float(upper),'available_residue_counts_completed':computed,'query_count':len(records),'finite_support_count_total_bits':total_bits,'positive_credit_queries':sum(F(r['credit'])>0 for r in records),'zero_credit_queries':sum(F(r['credit'])==0 for r in records),'pure_power_query_credit':str(sum((F(r['credit']) for r in records[:32]),F(0))),'scope':'The residue-count ceiling limits this E154 independent-marginal-max method. It does not limit stronger joint layout constraints or other selected sets/laws.','top_contributors':top,'support_counts':counts}
    require(computed==4660,'complete canonical support counts within resource guard')
    post=out
    query=result
    h=F(query['head_survival']);epsilon=1-h
    require(h==F(literal['head_survival']),'one full survivor submeasure')
    by_m={r['modulus']:r for r in query['records']}
    support={r['modulus']:r for r in post['support_counts']}
    gain=F(0);ceiling_drop=F(0);updates=[]
    for r in literal['records']:
        masses=list(map(F,r['all_residue_masses']))
        require(len(masses)==r['modulus'] and sum(masses,F(0))==h and max(masses)==F(r['max_exact']),'complete literal residue partition and exact maximum')
        m=r['modulus']
        if m==1:continue
        old=by_m[m];actual=F(r['max_exact']);relaxed=F(old['survivor_max_upper']);lower=F(support[m]['max_mass_lower'])
        require(lower<=actual<=relaxed and relaxed==F(r['relaxed_upper']),'literal maximum lies between both previous bounds')
        credit=old['coefficient']*(relaxed-actual)
        drop=old['coefficient']*(actual-lower)
        gain+=credit;ceiling_drop+=drop
        updates.append({'modulus':m,'coefficient':old['coefficient'],'exact_maximum':str(actual),'additional_credit':str(credit),'ceiling_reduction':str(drop)})
    delta=F(query['delta_lower'])+gain
    upper=F(post['independent_marginal_method_delta_upper'])-ceiling_drop
    require(delta<=upper,'hybrid deficit lower bound is below strengthened independent-max ceiling')
    require(upper<F(31400,1000) and F(threshold['records'][0]['Delta_strict_threshold_exact'])>F(31479,1000),'independent-max ceiling is strictly below the existing baseline threshold by more than 0.079')
    Jh,U=F(threshold['head_moment_exact']),F(threshold['tail_moment_upper_exact'])
    old=next(r for r in curve['records'] if r['B']==16384)
    T,C,E=map(F,(old['T_lower'],old['C_upper'],old['E7_upper']))
    scores=[]
    for extra,tr in zip((F(0),E),threshold['records']):
        score=epsilon+C+extra+(U*(Jh-epsilon-delta)-h)/(T-1)
        scores.append({'D7':bool(extra),'score_exact':str(score),'score_decimal':float(score),'remaining_Delta_gap':str(F(tr['Delta_strict_threshold_exact'])-delta),'independent_max_ceiling_minus_threshold':str(upper-F(tr['Delta_strict_threshold_exact'])),'passes':score<1})
    out={'status':'PASS','production_recomputations':0,'literal_query_moduli':[r['modulus'] for r in literal['records']],'additional_credit':str(gain),'additional_credit_decimal':float(gain),'hybrid_Delta_lower':str(delta),'hybrid_Delta_lower_decimal':float(delta),'strengthened_independent_max_Delta_upper':str(upper),'strengthened_independent_max_Delta_upper_decimal':float(upper),'scores':scores,'updates':updates,'scope':'Existing full relaxed-query upper bounds sharpened by seven independent exact small-modulus maxima. The upper ceiling constrains only E154 independent marginal maximization under this same law.'}
    return ctx.finish({'schema':'selected-survivor-independent-max-ceiling-v1','thresholds':threshold,'support_bound':post,'hybrid':out})


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
