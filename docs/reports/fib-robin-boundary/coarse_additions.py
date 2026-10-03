#!/usr/bin/env python3
"""Independent exact checks of translations preserving the gcd-state quotient.

This delivered verifier uses only the standard library and writes only --out.
"""
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Run without -O: exact checks require assertions.")

import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


def state_count(H):
    return sum(H % d == 0 for d in range(1, H + 1))


def no_extra_criterion(H, d):
    return d == H or (H % 2 == 0 and d == H // 2)


def direct_addition_quotient(H, c, counts):
    """Inspect actual gcd fibers, with no valuation or state-count formula."""
    next_by_gcd = {}
    rep_by_gcd = {}
    for C in range(1, H + 1):
        q, new_q = gcd(C, H), gcd(C + c, H)
        counts['direct_source_translation_checks'] += 1
        if q in next_by_gcd and next_by_gcd[q] != new_q:
            return False, (rep_by_gcd[q], C)
        next_by_gcd[q] = new_q
        rep_by_gcd[q] = C
    return True, None


def quotient_update(q, H, c):
    c %= H
    if c == 0:
        return q
    assert H % 2 == 0 and c == H // 2
    h, t = 0, H
    while t % 2 == 0:
        t //= 2
        h += 1
    r, t = 0, q
    while t % 2 == 0:
        t //= 2
        r += 1
    return q if r < h - 1 else 2 * q if r == h - 1 else q // 2


def label(keys):
    lookup = {}
    out = []
    for key in keys:
        if key not in lookup:
            lookup[key] = len(lookup)
        out.append(lookup[key])
    return out


def independent_moore(H, additions, counts):
    # Every multiplication residue is represented by a positive m in [1,H].
    transitions = [[x * m % H for x in range(H)] for m in range(1, H + 1)]
    transitions += [[(x + c) % H for x in range(H)] for c in additions]
    colors = label(gcd(x, H) for x in range(H))
    rounds = 0
    while True:
        nxt = label((colors[x],) + tuple(colors[t[x]] for t in transitions)
                    for x in range(H))
        counts['moore_transition_scans'] += H * len(transitions)
        if nxt == colors:
            return max(colors) + 1, rounds
        assert max(nxt) > max(colors)
        colors = nxt
        rounds += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    counts = Counter()
    witness_hash = sha256()
    sample_witnesses = []
    for H in range(2, 257):
        actual_good = []
        for c in range(1, H + 1):
            good, witness = direct_addition_quotient(H, c, counts)
            expected = no_extra_criterion(H, gcd(H, c))
            assert good == expected
            counts['individual_addition_models'] += 1
            if good:
                actual_good.append(c)
                for C in range(1, H + 1):
                    assert quotient_update(gcd(C, H), H, c) == gcd(C + c, H)
                    counts['closed_update_checks'] += 1
                # Positive representatives outside the initial residue window.
                for C in [H + 1, 2 * H, 3 * H - 1]:
                    for extra in [0, H, 3 * H]:
                        assert quotient_update(gcd(C, H), H, c + extra) == gcd(C + c + extra, H)
                        counts['positive_lift_update_checks'] += 1
            else:
                x, y = witness
                assert gcd(x, H) == gcd(y, H)
                assert gcd(x + c, H) != gcd(y + c, H)
                counts['one_addition_counterexamples'] += 1
                item = [H, c, x, y]
                witness_hash.update(json.dumps(item, separators=(',', ':')).encode())
                if len(sample_witnesses) < 12:
                    sample_witnesses.append(item)
        assert actual_good == ([H // 2, H] if H % 2 == 0 else [H])
        counts['complete_translation_windows'] += 1
    rows = []
    for H in range(2, 49):
        libraries = [[], [H], [1], [2], [2, 5], [4, 6], [H, 2 * H]]
        if H % 2 == 0:
            libraries.extend([[H // 2], [H // 2, 3 * H // 2], [H, H // 2]])
        else:
            libraries.append([H // 2])
        for additions in libraries:
            d = H
            for c in additions:
                d = gcd(d, c)
            actual, rounds = independent_moore(H, additions, counts)
            assert (actual == state_count(H)) == no_extra_criterion(H, d)
            assert actual >= state_count(H)
            counts['independent_complete_behavior_models'] += 1
            rows.append({'H': H, 'additions': additions, 'd': d,
                         'states': actual, 'divisor_count': state_count(H),
                         'proper_refinement_rounds': rounds})
    template_examples = []
    for c in [7, 10, 13, 2520, 5040, 7560, 10080]:
        good, witness = direct_addition_quotient(5040, c, counts)
        assert good == no_extra_criterion(5040, gcd(5040, c))
        if good:
            for C in range(1, 5041):
                assert quotient_update(gcd(C, 5040), 5040, c) == gcd(C + c, 5040)
                counts['template_5040_closed_update_checks'] += 1
        template_examples.append({'addition': c, 'preserves_60_states': good,
                                  'same_gcd_distinguished_pair': witness})
    data = {
        'schema': 'fib-gcd-no-extra-states-corollary-v1',
        'scope': 'Independent finite checks of a corollary of the existing classification formula; no new Lean or content claim.',
        'methods': ['All positive translation representatives c=1,...,H, H=2,...,256: directly check whether gcd fibers have well-defined successor outputs.',
                    'Moore refinement for selected addition libraries, H=2,...,48, using every positive scalar representative m=1,...,H; no classification formula in minimization.',
                    'Verify the closed-form quotient update for all successful translation windows and explicit positive lifts.'],
        'counts': dict(sorted(counts.items())),
        'counterexample_digest': witness_hash.hexdigest(),
        'sample_counterexamples_H_c_x_y': sample_witnesses,
        'template_5040_examples': template_examples,
        'behavior_summary': {'minimum_H': 2, 'maximum_H': 48,
                             'no_extra_models': sum(r['states'] == r['divisor_count'] for r in rows),
                             'extra_models': sum(r['states'] > r['divisor_count'] for r in rows),
                             'maximum_proper_refinement_rounds': max(r['proper_refinement_rounds'] for r in rows)},
        'boundary_H2_models': [r for r in rows if r['H'] == 2]
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'pass', 'counts': data['counts']}, sort_keys=True))


if __name__ == '__main__':
    main()
