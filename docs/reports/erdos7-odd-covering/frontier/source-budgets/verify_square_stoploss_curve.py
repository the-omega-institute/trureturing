"""Independent direct sums for all exact square-threshold continuation scores."""
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

CERTIFICATE='certificates/source_norms/source-budgets/square_stoploss_curve_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'certificates/source_norms/source-budgets/expanded_stop_budget_verification.json', 'certificates/source_norms/source-budgets/expanded_stop_head.json', 'frontier/source-budgets/square_stoploss_curve.py', 'frontier/source-budgets/expanded_stop_head.py', 'frontier/source-budgets/expanded_stop_budget.py', 'frontier/source-budgets/verify_expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    candidate=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    verified=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget_verification.json','frontier/source-budgets/verify_expanded_stop_budget.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    head=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_head.json','frontier/source-budgets/expanded_stop_head.py')
    SCALE = verified['scale']
    require(SCALE == candidate['scale'] == 10**18, 'same integer upper-mass grid')
    snapshots = {r['B']: r for r in verified['snapshots']}
    epsilon = F(head['epsilon_exact'])
    require(all(F(r['epsilon_exact']) == epsilon for r in head['records']),
            'attained head optimum, rather than an all-law lower bound')
    require([r['B'] for r in candidate['records']] == [16384, 32768, 65536], 'complete cutoff inventory')
    records, summands = [], 0
    for record in candidate['records']:
        B = record['B']
        snapshot = snapshots[B]
        weights = budget['low_product_tables'][str(B)]
        require(len(weights) == verified['retained_states'] + 1 and weights[0] == 0 and
                all(type(w) is int and w >= 0 for w in weights), 'complete nonnegative upper mass table')
        require(sha256(json.dumps(weights, separators=(',', ':')).encode()).hexdigest() ==
                snapshot['final_low_state_digest'], 'entire mass table independently checked already')
        T, J, C, extra = [F(snapshot[k]) for k in ['T_lower', 'J_upper', 'C_upper', 'E7_upper']]
        require(all(F(record[k]) == F(snapshot[k]) for k in
                    ['T_lower', 'J_upper', 'C_upper', 'E7_upper', 'epsilon_exact']), 'same law and bounds')
        j_units = J * SCALE
        require(j_units.denominator == 1, 'complete second moment in integer grid units')
        maximum = isqrt(T.numerator // T.denominator)
        if maximum * maximum >= T:
            maximum -= 1
        require(maximum * maximum < T <= (maximum + 1)**2 and maximum < len(weights),
                'all and only nonnegative square thresholds below the lower stop')
        rows = []
        for t in range(maximum + 1):
            tau = t * t
            # Each threshold is summed afresh, independently of the candidate
            # running prefix-mass and prefix-square accumulators.
            correction = sum((tau - d*d) * weights[d] for d in range(1, t + 1))
            summands += t
            K = F(j_units.numerator - tau * SCALE + correction, SCALE)
            require(K > 0 and 0 <= tau < T, 'valid positive stop-loss upper bound and denominator')
            score = epsilon + C + K / (T - tau)
            rows.append(dict(t=t, tau=tau, K_upper=str(K), baseline_score_upper=str(score),
                             D7_score_upper=str(score + extra)))
        require(rows == record['rows'] and len(rows) == record['threshold_count'],
                'every retained threshold and exact score agrees')
        require(F(rows[0]['K_upper']) == J and F(rows[1]['K_upper']) == J - 1 and
                F(rows[1]['baseline_score_upper']) == F(snapshot['consumer_score_upper']),
                'tau zero and tau one recover the original moments and budget')
        best = min(rows, key=lambda row: F(row['baseline_score_upper']))
        require(best == record['best'], 'exact selected minimum among square thresholds')
        old_score = F(snapshot['consumer_score_upper'])
        base_score, d7_score = F(best['baseline_score_upper']), F(best['D7_score_upper'])
        require(base_score < old_score, 'strict improvement over the tau-one certificate')
        lam = 1 - epsilon - C
        lam_d7 = lam - extra
        require(lam > 0 and lam_d7 > 0, 'positive common survivor lower bounds')
        gamma = best['tau'] + F(best['K_upper']) / lam
        gamma_d7 = best['tau'] + F(best['K_upper']) / lam_d7
        require((gamma < T) == (base_score < 1) and (gamma_d7 < T) == (d7_score < 1),
                'exact same-law conditioning/stopping equivalence')
        records.append(dict(B=B, T_lower=str(T), threshold_count=len(rows), best=best,
                            baseline_decimal=float(base_score), D7_decimal=float(d7_score),
                            baseline_margin_lower=str(1 - base_score), D7_margin_lower=str(1 - d7_score),
                            improvement=str(old_score - base_score), Gamma_upper=str(gamma),
                            D7_Gamma_upper=str(gamma_d7), rows=rows))
    require([r['best']['t'] for r in records] == [48, 96, 128] and
            sum(r['threshold_count'] for r in records) == 1362, 'complete independently selected thresholds')
    require(F(records[0]['best']['baseline_score_upper']) > 1 and
            F(records[1]['best']['baseline_score_upper']) < 1 and
            F(records[2]['best']['D7_score_upper']) < 1, 'correct retained pass boundaries')
    result = dict(schema='independent-squared-load-stoploss-direct-sum-v1',
                  scope='One deterministic squared-load threshold for every complete fixed divisor layout under the same actual law. Residues need not share a CRT center. Only minima over the retained square thresholds are claimed; head mass is the attained fixed-numerical-order value.',
                  scale=SCALE, threshold_count=1362, direct_mass_summands=summands, records=records)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
