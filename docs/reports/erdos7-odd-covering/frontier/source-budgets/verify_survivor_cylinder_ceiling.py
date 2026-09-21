"""Independent full residue-array support counts and exact directed method-ceiling audit."""
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

CERTIFICATE='certificates/source_norms/source-budgets/survivor_cylinder_ceiling_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'problem-details/64-adaptive-core-policy-and-continuous-stoploss-optima.md', 'problem-details/63-squared-load-stoploss-continuation.md', 'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md', 'certificates/source_norms/source-budgets/adaptive_core7_policy.json', 'frontier/source-budgets/adaptive_core7.py', 'certificates/source_norms/source-budgets/survivor_cylinder_literals.json', 'frontier/source-budgets/verify_survivor_cylinder_literals.py', 'certificates/source_norms/source-budgets/survivor_cylinder_queries.json', 'frontier/source-budgets/survivor_cylinder_queries.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    input_data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    policy=ctx.fresh('certificates/source_norms/source-budgets/adaptive_core7_policy.json','frontier/source-budgets/adaptive_core7.py')
    literal=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_literals.json','frontier/source-budgets/verify_survivor_cylinder_literals.py')
    query=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_queries.json','frontier/source-budgets/survivor_cylinder_queries.py')
    candidate=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','locked complete literal input')
    data={'input':input_data,'policy':policy,'literal':literal,'query':query,'support':candidate['support_bound'],'threshold':candidate['thresholds'],'curve':curve}
    START=time.monotonic()
    labels = data['input']['labels']
    require(len(labels) == len({m for m,a in labels}) == 154, 'distinct original labels')
    primes = data['input']['prime_order']
    profiles = [list(map(F,row)) for row in data['input']['profiles']]
    h = 1-F(data['policy']['epsilon_exact'])
    literal = {r['modulus']:r for r in data['literal']['records']}
    require(data['literal']['status'] == 'PASS' and len(literal) == 8, 'eight complete literal queries')
    for m, record in literal.items():
        masses = list(map(F, record['all_residue_masses']))
        require(len(masses) == m and sum(masses) == h and max(masses) == F(record['max_exact']),
                'literal residue partition and maximum')

    coeff = Counter()
    for i, (d,a) in enumerate(labels):
        coeff[d] += 3
        for e,b in labels[:i]:
            coeff[lcm(d,e)] += 2
    support = {r['modulus']:r['available_residues'] for r in data['support']['support_counts']}
    query = {r['modulus']:r for r in data['query']['records']}
    require(len(coeff) == len(support) == len(query) == 4660, 'all selected unary and pair moduli')
    upper = F(0)
    raw_upper = F(0)
    lower = F(0)
    counts = []
    cells = 0
    for m in sorted(coeff):
        require(time.monotonic()-START < 60, 'predeclared 60-second audit budget')
        # Literal byte cells and arithmetic-progression slices, independent of
        # the candidate's geometric-series integer-bitset representation.
        allowed = bytearray(b'\1') * m
        for d,a in labels:
            if m % d == 0:
                allowed[a::d] = b'\0' * len(range(a,m,d))
        z = allowed.count(1)
        require(z == support[m] and z > 0 and allowed[34 % m], 'exact independent residue support')
        cells += m
        left = m
        factors = []
        for p,row in zip(primes, profiles):
            e = 0
            while left % p == 0:
                left //= p
                e += 1
            factors.append(row[e])
        require(left == 1, 'full original head modulus')
        q = prod(factors)
        require(q == F(query[m]['price']) and coeff[m] == query[m]['coefficient'], 'independent cap price and coefficient')
        mass_lower = h/z
        mass_upper = F(query[m]['survivor_max_upper'])
        raw_upper += coeff[m]*(q-mass_lower)
        if m in literal:
            exact = F(literal[m]['max_exact'])
            require(mass_lower <= exact <= mass_upper, 'actual exact max within bounds')
            mass_lower = exact
            mass_upper = exact
        require(mass_lower <= mass_upper <= q, 'all marginal brackets')
        upper += coeff[m]*(q-mass_lower)
        lower += coeff[m]*(q-mass_upper)
        counts.append([m,z])

    require(raw_upper == F(data['support']['independent_marginal_method_delta_upper']), 'raw ceiling agrees')
    threshold = F(data['threshold']['records'][0]['Delta_strict_threshold_exact'])
    Jh = F(data['threshold']['head_moment_exact'])
    require(Jh==F(budget['exact_initial_head_second']),'independent exact head moment anchored to existing62 certificate')
    tail_upper = F(data['threshold']['tail_moment_upper_exact'])
    curve = next(r for r in data['curve']['records'] if r['B'] == 16384)
    T, C = F(curve['T_lower']), F(curve['C_upper'])
    require(tail_upper*Jh == F(curve['J_upper']), 'same moment bound')
    derived_threshold = Jh-(1-h)-((h-C)*(T-1)+h)/tail_upper
    require(threshold == derived_threshold, 'threshold rederived from complete positive-product score')
    require(lower <= upper < threshold, 'entire E154 independent-max route below required threshold')
    require(Jh-(1-h)-upper>=h,'nonnegative residual moment at the favorable method ceiling')
    score_at_upper = (1-h)+C+(tail_upper*(Jh-(1-h)-upper)-h)/(T-1)
    require(score_at_upper > 1, 'even unattainable favorable ceiling fails this fixed sufficient test')
    scale = 10**12
    ceiling_up = F(-((-upper.numerator*scale)//upper.denominator), scale)
    threshold_down = F((threshold.numerator*scale)//threshold.denominator, scale)
    require(upper <= ceiling_up < threshold_down <= threshold, 'compact directed gap certificate')

    out = dict(schema='independent-marginal-route-ceiling-audit-v1', status='PASS',
               scope='Fixed actual64 law, E154, B16384, fixed tau1 moment comparison constants only; joint layout coupling, different tests/laws/selected sets remain open.',
               support_counts_verified=len(counts), literal_cells_examined=cells,
               selected_coefficient_sum=sum(coeff.values()),
               delta_lower_exact=str(lower), delta_lower_decimal=float(lower),
               independent_max_ceiling_up=str(ceiling_up),
               sufficient_threshold_down=str(threshold_down),
               strict_gap_lower=str(threshold_down-ceiling_up),
               independent_max_ceiling_decimal=float(upper),
               threshold_decimal=float(threshold), score_at_ceiling_decimal=float(score_at_upper),
               count_table_sha256=sha256(json.dumps(counts,separators=(',',':')).encode()).hexdigest(),
               production_query_recomputations=0)
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
