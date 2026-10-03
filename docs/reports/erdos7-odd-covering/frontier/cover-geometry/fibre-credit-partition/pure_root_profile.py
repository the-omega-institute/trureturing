"""New same-source pure-root comparison and fixed 43/47/53/59 schedule.

Exact rational arithmetic, complete moments, low load atoms through 96.
No repository imports, source changes, height truncation, or filesystem search.
"""
import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import comb, factorial, prod
from pathlib import Path

LIMIT = 96
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
ORDERS = (0, 1, 2, 4)
D0 = F(1816999451688960000, 36518862868606981)
CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(message)


def factor_moments(p, mass, cap):
    haar = (F(1), F(p, p-1), F(p*(p+1), (p-1)**2),
            F(p*(p**3+11*p*p+11*p+1), (p-1)**4))
    return [mass + cap*(x-1) for x in haar]


def append(atoms, moments, p, mass, cap):
    require(mass >= cap/p >= 0, 'nonnegative factor zero atom')
    out = [F(0) for _ in range(LIMIT+1)]
    for z in range(1, LIMIT+1):
        if not atoms[z]:
            continue
        for v in range(1, LIMIT//z+1):
            weight = mass-cap/p if v == 1 else cap*F(p-1, p**v)
            out[z*v] += atoms[z]*weight
    return out, [x*y for x, y in zip(moments, factor_moments(p, mass, cap))]


def snapshot(atoms, moments):
    tails = [total-sum((z**k*atoms[z] for z in range(1, LIMIT+1)), F(0))
             for k, total in zip(ORDERS, moments)]
    require(all(t >= 0 for t in tails), 'complete tails nonnegative')
    require(tails[1] >= (LIMIT+1)*tails[0], 'tail first support')
    require(tails[2] >= (LIMIT+1)*tails[1], 'tail second support')
    require(tails[3] >= (LIMIT+1)**2*tails[2], 'tail fourth support')
    return {
        'moments': {str(k): str(v) for k, v in zip(ORDERS, moments)},
        'tail_moments_above_96': {str(k): str(v) for k, v in zip(ORDERS, tails)},
        'low_atoms': {str(z): str(atoms[z]) for z in range(1, LIMIT+1) if atoms[z]},
        'mean': str(moments[1]/moments[0]),
    }


def trim(atoms, moments, target):
    require(0 < target <= moments[0], 'legal upper-mass target')
    result = atoms[:]
    remaining = moments[0]-target
    removed = [F(0) for _ in ORDERS]
    cutoff = 0
    for z in range(1, LIMIT+1):
        take = min(remaining, result[z])
        result[z] -= take
        remaining -= take
        for i, k in enumerate(ORDERS):
            removed[i] += z**k*take
        if remaining == 0:
            cutoff = z
            break
    require(remaining == 0, 'upper-mass cutoff resolved in low atoms')
    require(all(result[z] == 0 for z in range(1, cutoff)), 'upper support')
    new_moments = [x-y for x, y in zip(moments, removed)]
    require(new_moments[0] == target, 'exact trimmed mass')
    return result, new_moments, {'cutoff': cutoff,
        'removed_moments': {str(k): str(v) for k, v in zip(ORDERS, removed)}}


def stoploss(atoms, moments, threshold):
    require(0 <= threshold <= LIMIT, 'stop-loss threshold in retained atoms')
    return moments[1]-threshold*moments[0]+sum(
        ((threshold-z)*atoms[z] for z in range(1, LIMIT+1) if z < threshold), F(0))


def finite_controls():
    layouts = 0
    # Exhaustive literal one-coordinate layouts; compare all load hinges.
    for p, height in ((3, 3), (5, 2)):
        period = p**height
        # Restricted full Haar (one forbidden first root), not normalized.
        allowed = [x for x in range(period) if x % p != p-1]
        factor = {1: F(p-2, p)}
        for v in range(2, height+1):
            factor[v] = F(p-1, p**v)
        factor[height+1] = F(1, p**height)
        for phases in product(*(range(p**e) for e in range(1, height+1))):
            loads = [1+sum(x % (p**e) == phase
                           for e, phase in enumerate(phases, 1)) for x in allowed]
            for threshold in range(height+2):
                actual = sum(max(z-threshold, 0) for z in loads)/F(period)
                bound = sum((max(z-threshold, 0)*w for z, w in factor.items()), F(0))
                require(actual <= bound, 'literal masked coordinate convex hinge')
            layouts += 1
    # Complete 3*5 divisor layouts retain possibly unrelated phases.
    factors = {1: F(1, 3)*F(3, 5), 2: F(1, 3)*F(1, 5)+F(1, 3)*F(3, 5),
               4: F(1, 3)*F(1, 5)}
    allowed = [x for x in range(15) if x % 3 != 0 and x % 5 != 4]
    for a3, a5, a15 in product(range(3), range(5), range(15)):
        loads = [1+(x % 3 == a3)+(x % 5 == a5)+(x == a15) for x in allowed]
        for threshold in range(5):
            actual = sum(max(z-threshold, 0) for z in loads)/F(15)
            bound = sum((max(z-threshold, 0)*w for z, w in factors.items()), F(0))
            require(actual <= bound, 'literal complete two-coordinate layout hinge')
        layouts += 1
    return {'literal_layouts': layouts,
            'one_axis': [[3, 3], [5, 2]], 'two_axis_divisors': [1, 3, 5, 15]}


def main(output):
    controls = finite_controls()
    atoms = [F(0) for _ in range(LIMIT+1)]
    atoms[1] = F(1)
    moments = [F(1) for _ in ORDERS]
    for p in PRIMES:
        atoms, moments = append(atoms, moments, p, F(p-1, p), F(1))
    require(moments[0] == prod(F(p-1, p) for p in PRIMES), 'mask product mass')
    full = snapshot(atoms, moments)
    atoms, moments, initial_trim = trim(atoms, moments, 1/D0)
    initial = snapshot(atoms, moments)
    stages = []
    for q in (43, 47, 53, 59):
        threshold = F(q-1, 2)
        before = snapshot(atoms, moments)
        loss = stoploss(atoms, moments, threshold)
        require(loss >= 0, 'nonnegative exact stop-loss')
        charge = loss/threshold
        target = moments[0]-charge
        require(target > 0, 'fixed-stage positive same-source mass')
        atoms, moments = append(atoms, moments, q, F(1), F(2))
        appended = snapshot(atoms, moments)
        atoms, moments, trim_certificate = trim(atoms, moments, target)
        stages.append({'prime': q, 'delta': '1/2', 'cap': '2',
            'before': before, 'threshold': str(threshold), 'stop_loss': str(loss),
            'deletion_charge': str(charge), 'appended': appended,
            'trim': trim_certificate, 'after': snapshot(atoms, moments)})
    mean_gate = F(60)*moments[0]-moments[1]
    half_charge = stoploss(atoms, moments, F(30))/30
    diagnostic = {'prime': 61, 'mean_gate': str(mean_gate),
        'some_constant_delta_passes': mean_gate > 0,
        'half_clipping_charge': str(half_charge),
        'half_clipping_remaining_mass': str(moments[0]-half_charge),
        'half_clipping_passes': moments[0] > half_charge}
    require(moments[0] > F(3, 400), 'final mass above 3/400')
    require(moments[2] < F(33, 2), 'final second moment below 33/2')
    require(moments[3] < 2500000, 'final fourth moment below 2500000')
    require(moments[0]/16 > F(3, 6400), 'actual head Haar survival')
    # Existing Report734/779 quartic tail, not a new analytic estimate.
    b, ell = 10000, 8
    require(b >= 286 and ell >= 4 and 3**ell <= b and 4*ell >= 25,
            'inherited quartic tail parameter domain')
    growth = {1: F(25), 2: F(250, 3), 3: F(100), 4: F(40)}
    for k, coefficient in growth.items():
        require(coefficient <= comb(25, k), 'quartic growth polynomial domination')
    tau4 = (F(5625, 6144)*F(2*ell*ell+1, 2*ell*ell-1)**25
            *F(b, (b-1)**4)*sum((F(factorial(25), factorial(25-j)*(3*ell)**j)
                                 for j in range(26)), F(0)))
    coarse_reserve = F(3, 400)-2500000*tau4
    exact_reserve = moments[0]-moments[3]*tau4
    require(coarse_reserve > F(7, 1000), 'quartic tail coarse reserve above 7/1000')
    require(exact_reserve > coarse_reserve, 'exact tail reserve dominates short bounds')
    data = {'scope': 'Same FC159 eta0, first pure-root masks, fixed 43/47/53/59 schedule',
        'evidence': 'ordinary mathematical premises and exact rational arithmetic; no Lean claim',
        'primes': PRIMES, 'D0': str(D0), 'atom_limit': LIMIT, 'orders': ORDERS,
        'finite_controls': controls, 'full_masked_comparison': full,
        'initial_trim': initial_trim, 'initial': initial, 'stages': stages,
        'next_61_diagnostic': diagnostic,
        'final_density_cap': '16', 'actual_head_Haar_lower': str(moments[0]/16),
        'quartic_tail_conditional_on_734_analytic_premise': {
            'B': b, 'ell': ell, 'tau4': str(tau4), 'M4_upper': '2500000',
            'mass_lower': '3/400', 'coarse_reserve': str(coarse_reserve),
            'exact_reserve': str(exact_reserve), 'certified_reserve_lower': '7/1000'},
        'checks': CHECKS}
    output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'checks': CHECKS, 'initial_cutoff': initial_trim['cutoff'],
        'stage_summaries': [{'q': s['prime'], 'cutoff': s['trim']['cutoff'],
            'charge': float(F(s['deletion_charge'])),
            'mass': float(F(s['after']['moments']['0'])),
            'mean': float(F(s['after']['mean'])),
            'M2': float(F(s['after']['moments']['2'])),
            'M4': float(F(s['after']['moments']['4']))} for s in stages],
        '61_mean_gate': float(mean_gate), '61_half_mass': float(moments[0]-half_charge),
        'quartic_tail_tau': float(tau4), 'quartic_tail_reserve': float(exact_reserve),
        'output': str(output)}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    main(args.output)
