"""Actual depth-two pure support, with N>=max(2,N_plus).

Exact rational arithmetic, complete moments, low load atoms through 256.
No repository imports, source changes, height truncation, or filesystem search.
"""
import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import comb, factorial, prod
from pathlib import Path

LIMIT = 256
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
        'tail_moments_above_limit': {str(k): str(v) for k, v in zip(ORDERS, tails)},
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
    # New literal depth-two actual supports, not the prior first-root suite.
    for p, first_root, second_residue in ((5,4,3), (7,6,5), (11,0,6)):
        period = p*p
        require(second_residue % p != first_root, 'actual pure first two cylinders disjoint')
        allowed = [x for x in range(period) if x % p != first_root and x != second_residue]
        mass = 1-F(1,p)-F(1,p*p)
        require(F(len(allowed), period) == mass, 'literal finite pure-survivor mass')
        factor = {1: mass-F(1,p), 2: F(p-1,p*p), 3: F(1,p*p)}
        require(sum(factor.values(),F(0)) == mass, 'depth-two finite comparison mass')
        for a1, a2 in product(range(p), range(p*p)):
            loads = [1+(x % p == a1)+(x == a2) for x in allowed]
            for threshold in range(4):
                actual = sum(max(z-threshold,0) for z in loads)/F(period)
                bound = sum((max(z-threshold,0)*w for z,w in factor.items()),F(0))
                require(actual <= bound, 'literal actual two-pure support convex hinge')
            layouts += 1
    return {'literal_layouts': layouts, 'actual_pure_pairs': [[5,4,3],[7,6,5],[11,0,6]]}


def main(output):
    controls = finite_controls()
    atoms = [F(0) for _ in range(LIMIT+1)]
    atoms[1] = F(1)
    moments = [F(1) for _ in ORDERS]
    factor_masses = {}
    for p in PRIMES:
        mass = F(2,3) if p == 3 else 1-F(1,p)-F(1,p*p)
        factor_masses[str(p)] = str(mass)
        atoms, moments = append(atoms, moments, p, mass, F(1))
    require(moments[0] == prod(F(v) for v in factor_masses.values()), 'actual mask product mass')
    full = snapshot(atoms, moments)
    atoms, moments, initial_trim = trim(atoms, moments, 1/D0)
    initial = snapshot(atoms, moments)
    stages = []
    for q in (43, 47, 53, 59, 61, 67, 71, 73):
        threshold = F(q-1, 2)
        before = snapshot(atoms, moments)
        loss = stoploss(atoms, moments, threshold)
        require(loss >= 0, 'nonnegative exact stop-loss')
        charge = loss/threshold
        target = moments[0]-charge
        entry = {'prime': q, 'delta': '1/2', 'cap': '2', 'positive': target > 0,
            'before': before, 'threshold': str(threshold), 'stop_loss': str(loss),
            'deletion_charge': str(charge), 'candidate_mass': str(target),
            'mean_gate': str((q-1)*moments[0]-moments[1])}
        if target <= 0:
            entry['decision'] = 'stop at first nonpositive fixed half-clipping ledger'
            stages.append(entry)
            break
        atoms, moments = append(atoms, moments, q, F(1), F(2))
        appended = snapshot(atoms, moments)
        atoms, moments, trim_certificate = trim(atoms, moments, target)
        entry.update({'appended': appended, 'trim': trim_certificate,
                      'after': snapshot(atoms, moments)})
        stages.append(entry)
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
    exact_reserve = moments[0]-moments[3]*tau4
    completed = sum(s['positive'] for s in stages)
    density_cap = 2**completed
    require(stages[-1]['prime'] == 73 and not stages[-1]['positive'] and completed == 7,
            'declared schedule stops first at73, positive prefix ends71')
    require(F(stages[-1]['mean_gate']) < 0, 'current comparator rejects every constant73 clipping')
    require(moments[0] > F(3,2500), 'depth-two71 mass above3/2500')
    require(moments[2] < F(71,5), 'depth-two71 second moment below71/5')
    require(moments[3] < 8010000, 'depth-two71 fourth moment below8010000')
    require(density_cap == 128, 'seven physical capped source operations')
    require(moments[0]/density_cap > F(3,320000), 'depth-two71 actual head Haar bound')
    coarse_reserve = F(3,2500)-8010000*tau4
    require(coarse_reserve > F(1,1000), 'depth-two71 coarse quartic reserve above1/1000')
    require(exact_reserve > coarse_reserve, 'exact reserve dominates coarse certificate')
    data = {'scope': 'FC159 N>=max(2,N_plus), same eta0, actual depth-two pure masks',
        'evidence': 'ordinary mathematical premises and exact rational arithmetic; no Lean claim',
        'primes': PRIMES, 'D0': str(D0), 'atom_limit': LIMIT, 'orders': ORDERS,
        'factor_masses': factor_masses,
        'declared_schedule': [43,47,53,59,61,67,71,73], 'first_nonpositive_stops': True,
        'finite_controls': controls, 'full_masked_comparison': full,
        'initial_trim': initial_trim, 'initial': initial, 'stages': stages,
        'final': snapshot(atoms,moments),
        'final_density_cap': str(density_cap), 'actual_head_Haar_lower': str(moments[0]/density_cap),
        'quartic_tail_conditional_on_734_analytic_premise': {
            'B': b, 'ell': ell, 'tau4': str(tau4),
            'exact_reserve': str(exact_reserve), 'positive': exact_reserve > 0,
            'coarse_mass_lower': '3/2500', 'coarse_M4_upper': '8010000',
            'coarse_reserve': str(coarse_reserve), 'certified_reserve_lower': '1/1000'},
        'checks': CHECKS}
    output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'checks': CHECKS, 'initial_cutoff': initial_trim['cutoff'],
        'stage_summaries': [{'q': s['prime'], 'positive': s['positive'],
            'charge': float(F(s['deletion_charge'])),
            'candidate_mass': float(F(s['candidate_mass'])),
            'mean_gate': float(F(s['mean_gate'])),
            **({'cutoff': s['trim']['cutoff'], 'mean': float(F(s['after']['mean'])),
                'M2': float(F(s['after']['moments']['2'])),
                'M4': float(F(s['after']['moments']['4']))} if s['positive'] else {})}
            for s in stages],
        'quartic_tail_tau': float(tau4), 'quartic_tail_reserve': float(exact_reserve),
        'output': str(output)}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    main(args.output)
