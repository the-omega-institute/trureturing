"""Independent target-divisor update and complete moment verification for enlarged cutoffs."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd,isqrt,lcm,prod
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('expanded_stop_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require,load_module=_io.require,_io.load_module

CERTIFICATE='certificates/source_norms/source-budgets/expanded_stop_budget_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/62-expanded-stopping-cutoffs-for-the-seven-phase-head.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'problem-details/04b-arbitrary-star-head-residues-with-unrestricted-tails.md', 'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md', 'certificates/source_norms/source-budgets/expanded_stop_head.json', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_head.py', 'frontier/source-budgets/expanded_stop_budget.py', 'certificates/source_norms/source-budgets/balanced_profile_exponent_frontier_verification.json', 'frontier/source-budgets/verify_balanced_profile_exponent_frontier.py', 'verify_finite_continuation.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same locked clean seven-phase input')
    head=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_head.json','frontier/source-budgets/expanded_stop_head.py')
    given=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    frontier=ctx.fresh('certificates/source_norms/source-budgets/balanced_profile_exponent_frontier_verification.json','frontier/source-budgets/verify_balanced_profile_exponent_frontier.py')
    require(all(head[key]==data[key]==given[key] for key in ['prime_order','heights','profiles','labels']),'same literal actual head, heights and caps')
    epsilon=F(head['epsilon_exact'])
    require(all(F(r['epsilon_exact'])==epsilon for r in head['records']),'independent full20/core7 agreement')
    E7=F(next(r for r in frontier['degree_records'] if r['total_degree_max']==7)['outside_weight'])
    require(E7==F(given['E7_upper']),'same independently checked complement-D7 allowance')
    continuation=load_module('expanded_independent_stopping_library',Path(base)/'verify_finite_continuation.py')
    def up(a,b):
        require(a>=0 and b>0,'nonnegative exact upward division')
        quotient,remainder=divmod(a,b)
        return quotient+bool(remainder)
    BMAX, SCALE, CAP = (65536, 10 ** 18, (2 * 65536 + 1) // 5)
    require(given['maximum_B'] == BMAX and given['scale'] == SCALE, 'same finite sweep domain and grid')
    allprimes = [p for p in range(2, BMAX + 2) if all((p % d for d in range(2, isqrt(p) + 1)))]
    require(len(allprimes) == 6543 and allprimes[-2:] == [65521, 65537], 'complete global prime inventory including next prime')
    require(data['prime_order'] == [p for p in allprimes if 3 <= p <= 73], 'all twenty head primes')
    snapshots_given = {r['B']: r for r in given['snapshots']}
    require(sorted(snapshots_given) == [16384, 32768, 65536] and len(given['stages']) == 6521, 'three checkpoints and all required prime stages')
    checkpoints = {max((p for p in allprimes if p <= B)): B for B in snapshots_given}
    divisors = [[] for _ in range(CAP + 1)]
    for n in range(1, CAP + 1):
        pairs = []
        for f in range(1, isqrt(n) + 1):
            if n % f == 0:
                pairs.append((f, n // f))
                if f * f != n:
                    pairs.append((n // f, f))
        divisors[n] = tuple(sorted(pairs))
    terms_per_update = sum(map(len, divisors))
    counts = {'head_updates': 0, 'tail_updates': 0, 'mass_divisor_terms': 0, 'charge_mass_terms': 0, 'stage_comparisons': 0}

    def update(before, atoms):
        require(len(atoms) == CAP + 1 and all((0 <= a <= SCALE for a in atoms)), 'all retained atoms have valid upward bounds')
        after = [0] * (CAP + 1)
        for n in range(1, CAP + 1):
            numerator = sum((before[previous] * atoms[f] for f, previous in divisors[n]))
            after[n] = (numerator + SCALE - 1) // SCALE
        counts['mass_divisor_terms'] += terms_per_update
        return after

    def head_atoms(p, height, row):
        atoms = [0] * (CAP + 1)
        for f in range(1, height + 1):
            mass = row[f - 1] - row[f]
            atoms[f] = up(SCALE * mass.numerator, mass.denominator)
        numerator = SCALE * row[-1].numerator * (p - 1)
        denominator = row[-1].denominator * p
        for f in range(height + 1, CAP + 1):
            if numerator <= denominator:
                atoms[f:] = [1] * (CAP + 1 - f)
                break
            atoms[f] = up(numerator, denominator)
            denominator *= p
        return atoms

    def head_moments(p, height, row):
        eg, eg2 = (F(1, p - 1), F(p + 1, (p - 1) ** 2))
        finite_first = sum(((k + 1) * (row[k] - row[k + 1]) for k in range(height)), F(0))
        finite_second = sum(((k + 1) ** 2 * (row[k] - row[k + 1]) for k in range(height)), F(0))
        return (finite_first + row[-1] * (height + 1 + eg), finite_second + row[-1] * ((height + 1) ** 2 + 2 * (height + 1) * eg + eg2))
    weights = [0] * (CAP + 1)
    weights[1] = SCALE
    mean = second = SCALE
    initial_mean = initial_second = F(1)
    for p, height, encoded in zip(data['prime_order'], data['heights'], data['profiles']):
        row = list(map(F, encoded))
        require(len(row) == height + 1 and row[0] == 1 and all((F(1, p ** e) <= row[e] <= row[e - 1] for e in range(1, height + 1))), 'complete feasible initial depth profile')
        weights = update(weights, head_atoms(p, height, row))
        first_factor, second_factor = head_moments(p, height, row)
        initial_mean *= first_factor
        initial_second *= second_factor
        mean = up(mean * first_factor.numerator, first_factor.denominator)
        second = up(second * second_factor.numerator, second_factor.denominator)
        counts['head_updates'] += 1
    require(initial_mean == F(given['exact_initial_head_mean']) and initial_second == F(given['exact_initial_head_second']), 'all geometric head moments retained')
    charge, steps, snapshots = (0, [], [])
    for k, q in enumerate(allprimes, 1):
        if q <= 73:
            continue
        if q > BMAX:
            break
        cutoff = (2 * q + 1) // 5
        correction = sum(((2 * q + 1 - 5 * d) * weights[d] for d in range(1, cutoff + 1)))
        counts['charge_mass_terms'] += cutoff
        numerator = 5 * mean - (2 * q + 1) * SCALE + correction
        step = up(numerator, 3 * (q - 2))
        charge += step
        stage = [q, step, charge]
        require(stage == given['stages'][len(steps)], 'exact directed stage at prime ' + str(q))
        steps.append(stage)
        counts['stage_comparisons'] += 1
        atoms = [0] * (CAP + 1)
        atoms[1] = up(SCALE * (3 * q * (q - 2) - 5 * (q - 1)), 3 * q * (q - 2))
        an, ad = (SCALE * 5 * (q - 1) ** 2, 3 * (q - 2) * q * q)
        for f in range(2, CAP + 1):
            if an <= ad:
                atoms[f:] = [1] * (CAP + 1 - f)
                break
            atoms[f] = up(an, ad)
            ad *= q
        weights = update(weights, atoms)
        positive = F(5 * (q - 1), 3 * q * (q - 2))
        eg, eg2 = (F(1, q - 1), F(q + 1, (q - 1) ** 2))
        first_factor = 1 - positive + positive * (2 + eg)
        second_factor = 1 - positive + positive * (4 + 4 * eg + eg2)
        mean = up(mean * first_factor.numerator, first_factor.denominator)
        second = up(second * second_factor.numerator, second_factor.denominator)
        counts['tail_updates'] += 1
        if q not in checkpoints:
            continue
        B = checkpoints[q]
        reference = snapshots_given[B]
        C, J, T = (F(charge, SCALE), F(second, SCALE), continuation.stopping_threshold(k))
        require(k >= 10 and T > 1 and (reference['global_prime_index'] == k) and (reference['last_prime'] == q) and (reference['next_prime'] == allprimes[k]), 'correct complete prime index and continuation boundary')
        require(C == F(reference['C_upper']) and J == F(reference['J_upper']) and (T == F(reference['T_lower'])) and (F(mean, SCALE) == F(reference['full_mean_upper'])), 'independent full moments, cumulative charge and rational threshold')
        digest = sha256(json.dumps(weights, separators=(',', ':')).encode()).hexdigest()
        require(digest == reference['final_low_state_digest'], 'entire retained mass table matches')
        score = epsilon + C + (J - 1) / (T - 1)
        survival = 1 - epsilon - C
        score_d7, survival_d7 = (score + E7, survival - E7)
        require(score == F(reference['consumer_score_upper']) and score_d7 == F(reference['D7_score_upper']) and (survival == F(reference['survival_lower'])) and (survival_d7 == F(reference['D7_survival_lower'])), 'same-law baseline and D7 budgets')
        require(survival > 0 and survival_d7 > 0, 'positive common survivor lower mass at checkpoint')
        gamma, gamma_d7 = (1 + (J - 1) / survival, 1 + (J - 1) / survival_d7)
        require(gamma == F(reference['Gamma_upper']) and gamma_d7 == F(reference['D7_Gamma_upper']), 'same-law complete-layout moment after one conditioning')
        snapshots.append(dict(B=B, global_prime_index=k, last_prime=q, next_prime=allprimes[k], tail_stages=len(steps), C_upper=str(C), J_upper=str(J), T_lower=str(T), epsilon_exact=str(epsilon), consumer_score_upper=str(score), consumer_score_decimal=float(score), margin_lower=str(1 - score), survival_lower=str(survival), Gamma_upper=str(gamma), E7_upper=str(E7), D7_score_upper=str(score_d7), D7_score_decimal=float(score_d7), D7_margin_lower=str(1 - score_d7), D7_survival_lower=str(survival_d7), D7_Gamma_upper=str(gamma_d7), final_low_state_digest=digest))
    require(len(steps) == 6521 and len(snapshots) == 3, 'complete bounded independent sweep')
    require(F(snapshots[1]['consumer_score_upper']) < 1 and F(snapshots[1]['Gamma_upper']) < F(snapshots[1]['T_lower']), 'strict baseline pass at B32768')
    require(F(snapshots[2]['D7_score_upper']) < 1 and F(snapshots[2]['D7_Gamma_upper']) < F(snapshots[2]['T_lower']), 'strict outside-D7 pass at B65536')
    require(epsilon<F(381,1000) and E7<F(1,25),'strict simple head and D7 bounds')
    a,b=snapshots[1],snapshots[2]
    require(F(a['C_upper'])<F(527,1000) and F(a['J_upper'])<13906 and F(a['T_lower'])>185000,'strict simple B32768 components')
    require(F(b['C_upper'])<F(53,100) and F(b['J_upper'])<19189 and F(b['T_lower'])>414000,'strict simple B65536 components')
    require(1-F(381,1000)-F(527,1000)==F(23,250) and 1+F(13905)/F(23,250)==F(3476273,23)<185000,'short baseline survivor/Gamma chain')
    require(1-F(381,1000)-F(53,100)-F(1,25)==F(49,1000) and 1+F(19188)/F(49,1000)==F(19188049,49)<414000,'short D7 survivor/Gamma chain')
    simple_bounds={'epsilon_strict_upper':'381/1000','E7_strict_upper':'1/25','B32768':{'C_strict_upper':'527/1000','J_strict_upper':'13906','T_strict_lower':'185000','survival_strict_lower':'23/250','Gamma_strict_upper':'3476273/23'},'B65536_D7':{'C_strict_upper':'53/100','J_strict_upper':'19189','T_strict_lower':'414000','survival_strict_lower':'49/1000','Gamma_strict_upper':'19188049/49'}}
    result=dict(schema='independent-expanded-stop-upward-divisor-audit-v1',scope='Same literal seven-phase head and balanced caps, fixed numerical head order, full uniform high digits, exact same-law tail charges and complete-layout moments. The D7 extension includes only distinct73-smooth added moduli outside D7.',scale=SCALE,retained_states=CAP,snapshots=snapshots,stages=steps,counts=counts,simple_bounds=simple_bounds)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
