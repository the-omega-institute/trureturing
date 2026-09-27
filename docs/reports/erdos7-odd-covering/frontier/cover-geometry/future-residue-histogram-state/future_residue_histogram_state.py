#!/usr/bin/env python3
"""Exact finite-future residue histograms and an actual odd-distinct obstruction.

For a fixed inventory of unused future odd moduli, the profile at
B=gcd(current period, lcm(future moduli)) updates without the original
survivor set. This standard-library verifier checks that CRT update and
recovers the profile from full exact-count continuation behavior.

Exact survivor counts are the observation. No minimality claim for the
weaker empty/nonempty readout, general computational lower bound, or
covering counterexample is asserted. No files are written.
"""
from itertools import combinations, product
from math import gcd, lcm
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def valid_moduli(values):
    values = tuple(values)
    need(all(type(m) is int and m > 1 and m % 2 for m in values),
         'moduli must be odd integers greater than one')
    need(len(set(values)) == len(values), 'moduli must be distinct')
    return frozenset(values)


def joint_modulus(period, future):
    return gcd(period, lcm(*future))


def histogram(points, modulus):
    result = [0] * modulus
    for x in points:
        result[x % modulus] += 1
    return tuple(result)


def raw_history(classes):
    """Construct the actual survivor set of distinct original odd classes."""
    classes = tuple(classes)
    used = valid_moduli(m for m, a in classes)
    need(all(type(a) is int for m, a in classes), 'literal integer phases required')
    period = lcm(*used)
    survivors = {x for x in range(period) if all((x-a) % m for m, a in classes)}
    return period, used, survivors


def initial_state(period, used, future, survivors):
    """Return (L,U,F,K_B); no reachability assumption on arbitrary input H."""
    need(type(period) is int and period > 0 and period % 2, 'positive odd period required')
    used, future = valid_moduli(used), valid_moduli(future)
    need(not used & future, 'future inventory must exclude every used modulus')
    need(all(period % m == 0 for m in used), 'the period must contain all used moduli')
    survivors = set(survivors)
    need(all(type(x) is int and 0 <= x < period for x in survivors), 'invalid original survivor')
    return period, used, future, histogram(survivors, joint_modulus(period, future))


def marginal(profile, modulus, phase):
    need(len(profile) % modulus == 0, 'requested marginal must divide the stored modulus')
    return sum(profile[x] for x in range(phase % modulus, len(profile), modulus))


def crt_phase(m, a, n, b):
    """Compatible two-modulus CRT, using no finite residue search."""
    d = gcd(m, n)
    if (b-a) % d:
        return None
    reduced = n // d
    t = ((b-a)//d * pow(m//d, -1, reduced)) % reduced if reduced > 1 else 0
    return (a + m*t) % lcm(m, n)


def update(state, modulus, phase):
    """Exact profile update from the compressed state alone, retaining legality."""
    period, used, future, profile = state
    need(type(modulus) is int and modulus in future, 'action must use an available modulus')
    need(type(phase) is int, 'action phase must be an integer')
    phase %= modulus
    next_period = lcm(period, modulus)
    remaining = future - {modulus}
    next_base = joint_modulus(next_period, remaining)
    g = gcd(period, next_base)
    h = gcd(period, lcm(modulus, next_base))
    multiplier = next_period // lcm(period, next_base)
    next_profile = []
    for b in range(next_base):
        value = multiplier * marginal(profile, g, b)
        combined = crt_phase(modulus, phase, next_base, b)
        if combined is not None:
            value -= marginal(profile, h, combined)
        need(value >= 0, 'negative actual histogram cell')
        next_profile.append(value)
    return next_period, used | {modulus}, remaining, tuple(next_profile)


def direct_update(period, survivors, modulus, phase):
    next_period = lcm(period, modulus)
    return next_period, {x for x in range(next_period)
                         if x % period in survivors and (x-phase) % modulus}


def subsets(values):
    values = sorted(values)
    return [s for k in range(len(values)+1) for s in combinations(values, k)]


def recover_profile(period, future, continuation_count):
    """Recover K_B from every subset continuation count at each common phase.

    continuation_count(S,b) is measured in lcm(L,lcm(S)) after deleting
    b modulo every distinct modulus in S. The formula first lifts each
    count to the common period, so no different sample spaces are mixed.
    """
    total_period = lcm(period, *future)
    B = joint_modulus(period, future)
    return tuple(sum((-1)**len(S) * (total_period // lcm(period, *S))
                     * continuation_count(S, b) for S in subsets(future))
                 for b in range(B))


def actual_counterexample():
    future = {3, 5}
    histories = [('A', (0, 2, 0, 8)), ('B', (5, 0, 5, 3))]
    results = []
    for name, phases in histories:
        classes = tuple(zip((15, 21, 35, 105), phases))
        period, used, H = raw_history(classes)
        state = initial_state(period, used, future, H)
        h3, h5, h15 = (histogram(H, d) for d in (3, 5, 15))
        measured = [len(H)]
        for m in (3, 5):
            state = update(state, m, 0)
            period, H = direct_update(period, H, m, 0)
            need(state[0] == period and state[3] == histogram(H, joint_modulus(period, state[2])),
                 'compressed and actual histories disagree')
            measured.append(len(H))
        results.append({'name': name, 'original_classes': classes, 'period': period,
                        'K3': h3, 'K5': h5, 'K15_at_zero': h15[0], 'successive_counts': measured})
    need(results[0]['K3'] == results[1]['K3'] == (28, 34, 28), 'same complete K3')
    need(results[0]['K5'] == results[1]['K5'] == (11, 20, 20, 19, 20), 'same complete K5')
    need([x['successive_counts'] for x in results] == [[90, 62, 51], [90, 62, 56]],
         'actual legal two-step separation')
    need([x['K15_at_zero'] for x in results] == [0, 5], 'missing joint intersection')
    return results


def verify():
    cells, recoveries = 0, 0
    for period in (3, 5, 9):
        for future in ({3, 5}, {5, 7}, {3, 9}, {7, 15}):
            for mask in range(1 << period):
                H = {x for x in range(period) if mask >> x & 1}
                state = initial_state(period, (), future, H)
                for modulus in future:
                    for phase in range(modulus):
                        nxt = update(state, modulus, phase)
                        Lp, Hp = direct_update(period, H, modulus, phase)
                        expected = histogram(Hp, joint_modulus(Lp, nxt[2]))
                        need(nxt[3] == expected, 'exact CRT histogram transition')
                        cells += len(expected)
                def counts(selected, common_phase):
                    Lp, Hp = period, H
                    for m in selected:
                        Lp, Hp = direct_update(Lp, Hp, m, common_phase)
                    return len(Hp)
                need(recover_profile(period, future, counts) == state[3],
                     'inclusion-exclusion must recover the whole canonical profile')
                recoveries += 1
    example = actual_counterexample()
    return {'update_cells_checked': cells, 'profile_recoveries_checked': recoveries,
            'actual_odd_distinct_histories': example,
            'scope': 'exact-count state sufficiency for a fixed finite future inventory; no closure-only or E7 noncoverage theorem'}


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
