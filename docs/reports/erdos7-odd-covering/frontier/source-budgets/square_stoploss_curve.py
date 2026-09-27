"""Exact squared-load stop-loss bounds from complete independently checked product tables."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('square_stoploss_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/square_stoploss_curve.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'certificates/source_norms/source-budgets/expanded_stop_budget_verification.json', 'frontier/source-budgets/expanded_stop_budget.py', 'frontier/source-budgets/verify_expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    verified=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget_verification.json','frontier/source-budgets/verify_expanded_stop_budget.py')
    require(data['scale']==verified['scale'] and data['stages']==verified['stages'],'complete independently checked same-law budget')
    require(all(a['B']==b['B'] and a['final_low_state_digest']==b['final_low_state_digest'] for a,b in zip(data['snapshots'],verified['snapshots'])),'all complete checkpoint tables independently checked')
    scale=data['scale']
    records=[]
    for snapshot in data['snapshots']:
        B=snapshot['B']
        weights=data['low_product_tables'][str(B)]
        require(sha256(json.dumps(weights,separators=(',',':')).encode()).hexdigest()
                ==snapshot['final_low_state_digest'],'bound complete upper table')
        require(len(weights)==snapshot['retained_states']+1 and weights[0]==0,
                'complete positive product table')
        J=F(snapshot['J_upper']);T=F(snapshot['T_lower'])
        C=F(snapshot['C_upper']);epsilon=F(snapshot['epsilon_exact'])
        extra=F(snapshot['E7_upper'])
        prefix_mass=prefix_square=0
        rows=[]
        t=0
        while t*t<T:
            require(t<len(weights),'every queried state represented')
            if t:
                prefix_mass+=weights[t]
                prefix_square+=t*t*weights[t]
            tau=t*t
            K=J-tau+F(tau*prefix_mass-prefix_square,scale)
            require(K>0,'strictly positive certified upper stop loss')
            score=epsilon+C+K/(T-tau)
            rows.append({'t':t,'tau':tau,'K_upper':str(K),
                         'baseline_score_upper':str(score),
                         'D7_score_upper':str(score+extra)})
            t+=1
        require(F(rows[1]['baseline_score_upper'])==F(snapshot['consumer_score_upper']),
                'tau one recovers original attained-head score')
        best=min(rows,key=lambda row:F(row['baseline_score_upper']))
        records.append({'B':B,'T_lower':str(T),'epsilon_exact':str(epsilon),
                        'C_upper':str(C),'J_upper':str(J),'E7_upper':str(extra),
                        'best':best,'baseline_decimal':float(F(best['baseline_score_upper'])),
                        'D7_decimal':float(F(best['D7_score_upper'])),
                        'threshold_count':len(rows),'rows':rows})
    result={'schema':'squared-load-stoploss-upper-curve-v1','scope':'One actual seven-phase head law, all complete divisor layouts without requiring compatible residues, the same auxiliary comparison and D7 extension. Minimum only among the retained square thresholds; no arbitrary-phase head theorem.','scale':scale,'records':records}
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
