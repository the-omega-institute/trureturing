"""Independent divisor-sum lower bounds and full relative-profile box inequality."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt,prod
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True
_spec=importlib.util.spec_from_file_location('transport_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/profile_auxiliary_transport_verification.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/61-coordinate-retention-and-profile-neighborhood-obstruction.md', 'problem-details/60-positive-cylinder-covers-across-head-profiles.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'certificates/source_norms/source-budgets/profile_auxiliary_transport.json', 'certificates/source_norms/source-budgets/positive_cylinder_polynomial_verification.json', 'frontier/source-budgets/profile_auxiliary_transport.py', 'frontier/source-budgets/verify_positive_cylinder_polynomial.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    data=ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json')
    require(sha256(ctx.raw('frontier/source-budgets/uniform_phase_capacity_input.json')).hexdigest()=='ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b','same locked actual seven-phase input')
    expected=ctx.fresh('certificates/source_norms/source-budgets/profile_auxiliary_transport.json','frontier/source-budgets/profile_auxiliary_transport.py')
    polynomial=ctx.fresh('certificates/source_norms/source-budgets/positive_cylinder_polynomial_verification.json','frontier/source-budgets/verify_positive_cylinder_polynomial.py')
    SCALE, B, T, h = 10**15, 16384, F(326059, 4), F(1, 50000)
    cutoff = (2 * B + 1) // 5
    primes, heights = data['prime_order'], data['heights']
    rows = [[F(x) for x in row] for row in data['profiles']]
    require(len(primes) == len(heights) == len(rows) == 20, 'all twenty head coordinates')
    require(all(34 % m != a for m, a in data['labels']), 'same actual survivor integer')

    # Each output integer n is built only from its actual factor pairs.
    # This is a target-indexed divisor sum, not the candidate factor convolution.
    divisors = [[] for _ in range(cutoff + 1)]
    for n in range(1, cutoff + 1):
        pairs = []
        for f in range(1, isqrt(n) + 1):
            if n % f == 0:
                pairs.append((f, n // f))
                if f * f != n:
                    pairs.append((n // f, f))
        divisors[n] = tuple(sorted(pairs))
    counts = {'divisor_terms': 0, 'head_updates': 0, 'tail_updates': 0,
              'charge_mass_terms': 0, 'stage_comparisons': 0}


    def downward(x):
        return (x.numerator * SCALE) // x.denominator


    def atom_table(tail, boundary):
        """Atom f=1+K from the difference of two survival tails."""
        result = {}
        for f in range(1, cutoff + 1):
            mass = tail(f - 1) - tail(f)
            require(mass >= 0, 'monotone exact auxiliary survival tail')
            lower = downward(mass)
            if lower:
                result[f] = lower
            elif f > boundary:
                break
        require(sum(result.values()) <= SCALE, 'nonnegative lower atom subdistribution')
        return result


    def divisor_update(before, atoms):
        after = [0] * (cutoff + 1)
        largest_factor = max(atoms)
        for n in range(1, cutoff + 1):
            total = 0
            for f, previous in divisors[n]:
                if f > largest_factor:
                    break
                if f in atoms and before[previous]:
                    total += (before[previous] * atoms[f]) // SCALE
                    counts['divisor_terms'] += 1
            after[n] = total
        require(sum(after) <= SCALE, 'lower finite product subdistribution')
        return after


    def moment_update(lower, exact_factor_moment):
        require(lower >= 0 and exact_factor_moment >= 1, 'nonnegative full moment update')
        return lower * exact_factor_moment.numerator // exact_factor_moment.denominator


    weights = [0] * (cutoff + 1)
    weights[1] = SCALE
    first = second = SCALE
    for p, height, row in zip(primes, heights, rows):
        require(len(row) == height + 1 and row[0] == 1 and
                all(F(1, p**e) <= row[e] <= row[e - 1] for e in range(1, height + 1)),
                'complete feasible balanced depth profile')

        def tail(e):
            return row[e] if e <= height else row[height] / p**(e - height)

        atoms = atom_table(tail, height)
        weights = divisor_update(weights, atoms)
        # Conditional on K>=H, K=H+G where Pr(G>=t)=p^(-t).
        geometric_first = F(1, p - 1)
        geometric_second = F(p + 1, (p - 1)**2)
        moments = []
        for order in [1, 2]:
            finite = sum((F((k + 1)**order) * (row[k] - row[k + 1])
                          for k in range(height)), F(0))
            remaining = (height + 1 + geometric_first if order == 1 else
                         (height + 1)**2 + 2 * (height + 1) * geometric_first + geometric_second)
            moments.append(finite + row[height] * remaining)
        first = moment_update(first, moments[0])
        second = moment_update(second, moments[1])
        counts['head_updates'] += 1

    # Sieve is independent of the candidate trial-division prime inventory.
    is_prime = bytearray([1]) * (B + 1)
    is_prime[0:2] = b'\x00\x00'
    for q in range(2, isqrt(B) + 1):
        if is_prime[q]:
            for multiple in range(q*q, B + 1, q):
                is_prime[multiple] = 0
    tail_primes = [q for q in range(74, B + 1) if is_prime[q]]
    require(len(tail_primes) == 1879 and tail_primes[0] == 79 and tail_primes[-1] == 16381,
            'complete fixed prime continuation interval')
    require(len(expected['stages']) == len(tail_primes), 'candidate covers every tail stage')
    stages, total_charge = [], 0
    for q, candidate_stage in zip(tail_primes, expected['stages']):
        a = 2*q + 1
        low_correction = 0
        for d in range(1, a // 5 + 1):
            low_correction += (a - 5*d) * weights[d]
            counts['charge_mass_terms'] += 1
        numerator_lower = 5 * first - a * SCALE + low_correction
        charge_lower = max(0, numerator_lower // (3 * (q - 2)))
        total_charge += charge_lower
        stage = [q, charge_lower, total_charge]
        require(stage == candidate_stage, 'independent exact tail charge at prime ' + str(q))
        counts['stage_comparisons'] += 1
        stages.append(stage)
        c = F(5 * (q - 1), 3 * (q - 2))

        def tail(e):
            return F(1) if e == 0 else c / q**e

        atoms = atom_table(tail, 1)
        weights = divisor_update(weights, atoms)
        # K is zero with probability 1-c/q; otherwise 1+G for geometric G.
        positive = c / q
        geometric_first, geometric_second = F(1, q - 1), F(q + 1, (q - 1)**2)
        exact_first = 1 - positive + positive * (2 + geometric_first)
        exact_second = 1 - positive + positive * (4 + 4 * geometric_first + geometric_second)
        first = moment_update(first, exact_first)
        second = moment_update(second, exact_second)
        counts['tail_updates'] += 1

    C, J = F(total_charge, SCALE), F(second, SCALE)
    require(C == F(expected['C_lower']) and J == F(expected['J_lower']),
            'independent complete exact auxiliary lower bounds')
    degree = max(term['coordinate_mask'].bit_count() for term in polynomial['terms'])
    require(degree == 12 and all(int(term['coefficient']) > 0 for term in polynomial['terms']),
            'positive frozen polynomial has degree at most twelve')
    base_caps = [row[-1] for row in rows]
    U = sum((int(term['coefficient']) * prod(base_caps[i] for i in range(20)
                                           if term['coordinate_mask'] >> i & 1)
             for term in polynomial['terms']), F(0))
    require(U == F(polynomial['balanced_value']) == F(expected['base_survivor_upper']),
            'same independently checked frozen-cover value')
    budget_lower = (1 - h)**20 * (C + (J - 1) / (T - 1))
    survival_upper = (1 + h)**degree * U
    gap = budget_lower - survival_upper
    require(budget_lower == F(expected['new_auxiliary_B_lower']) and
            survival_upper == F(expected['new_survivor_upper']) and
            gap == F(expected['score_excess_lower']) and gap > F(1329, 2000000),
            'strict score excess greater than 0.0006645 over the entire relative box')
    result = dict(schema='independent-relative-profile-neighborhood-obstruction-v1',
                  scope='Same seven-phase head; every finite nonroot depth cap of all20 coordinates varies in its relative box, with geometric high-digit lifts and fixed continuation schedule. Lower bounds concern exact independent auxiliary C and J, not actual losses or actual-law moments.',
                  B=B, T=str(T), delta='2/5', scale=SCALE, h=str(h),
                  C_lower=str(C), J_lower=str(J), polynomial_degree=degree,
                  base_survivor_upper=str(U), new_auxiliary_B_lower=str(budget_lower),
                  new_survivor_upper=str(survival_upper), score_excess_lower=str(gap),
                  score_excess_lower_decimal=float(gap), stages=stages, counts=counts)
    return ctx.finish(result)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
