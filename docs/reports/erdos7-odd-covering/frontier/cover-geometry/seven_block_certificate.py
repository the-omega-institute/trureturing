#!/usr/bin/env python3
"""Exact arithmetic for graph blocks with at most seven prime vertices.

Reuses Chapter 30's independent envelope evaluator and pinned geometry.
No author verifier is imported, no geometry is generated, and no Lean
verification is claimed. Analytic comparison and graph recursion premises
are specified in the accompanying Chapter 31 manuscript.

Python 3.10+; --geometry FILE --output FILE work from any directory.
The Chapter 30 helper defaults to the file beside this script.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
import importlib.util
from itertools import combinations
import json
from math import comb, isqrt, prod
from pathlib import Path
import sys

FSTAR = Q(1493, 3072)
SMALL = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
STANDARD = (2, 4, 4, 8, 8)
IMPROVED = (4, 4, 8, 8, 12)
HELPER_SHA = '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4'


def fee(q):
    return {5: Q(7, 24), 7: Q(1, 8), 11: Q(1, 24), 13: Q(1, 48)}.get(
        q, Q(1, 2 ** ((q - 1) // 2)))


def prime(q):
    return q >= 2 and all(q % d for d in range(2, isqrt(q) + 1))


@lru_cache(None)
def coefficients(t):
    # The subset polynomial is sum_n c_n(t) e_n(b), including n=0.
    c, derivative = [1], [0]
    for n in range(1, 7):
        total = sum(comb(n - 1, r - 1) * c[n - r] for r in range(2, n + 1))
        dtotal = sum(comb(n - 1, r - 1) * derivative[n - r]
                     for r in range(2, n + 1))
        c.append(-t * c[-1] - (t + 1) * total)
        derivative.append(-c[n - 1] - t * derivative[-1] - total - (t + 1) * dtotal)
    return c, derivative


class Kernel:
    def __init__(self, children, expense):
        assert len(children) == 6 and 0 <= expense < Q(1, 2)
        caps = [1 / (3 - Q(6, 5) * expense) if q == 5
                else 1 / (q - 2 - 2 * expense) for q in children]
        self.caps = caps
        self.scaled, self.denominators = [[1]] + [None] * 63, [1] * 64
        self.memo = {}
        for mask in range(1, 64):
            bit = mask & -mask
            i, previous = bit.bit_length() - 1, mask ^ bit
            n, d = caps[i].numerator, caps[i].denominator
            row = [0] * (len(self.scaled[previous]) + 1)
            for k, v in enumerate(self.scaled[previous]):
                row[k] += d * v
                row[k + 1] += n * v
            self.scaled[mask] = row
            self.denominators[mask] = self.denominators[previous] * d

    def evaluate(self, t):
        if t not in self.memo:
            c, dc = coefficients(t)
            z = [Q(sum(a * b for a, b in zip(c, row)), d)
                 for row, d in zip(self.scaled, self.denominators)]
            L = Q(-sum(a * b for a, b in zip(dc, self.scaled[-1])), self.denominators[-1])
            self.memo[t] = (min(z), z[-1], L)
        return self.memo[t]

    def pay(self, charge, parent):
        cp = Q(1) if parent == 3 else Q(3, 10) if parent == 5 else Q(2, parent - 1)
        for t in range(1, 32):
            zmin, Z, L = self.evaluate(t)
            if zmin <= 0:
                return None, t
            assert Z > 0 and L >= 0
            cost = L / (parent ** t * (parent - 1) * Z * cp)
            if cost < charge:
                return {'parent': parent, 'cutoff': t, 'min_residual': str(zmin),
                        'fee_ratio': str(cost / charge)}, None
        raise AssertionError('Search bound exhausted without a certified classification')


def boundary():
    rows, exceptional, counts = [], [], Counter()
    for j in range(1, 7):
        for small in combinations(SMALL, j):
            children = small + tuple(range(57, 57 + 2 * (6 - j), 2))
            charge = sum(map(fee, small), Q(0))
            expense = FSTAR - charge
            kernel = Kernel(children, expense)
            root, failure = kernel.pay(charge, 3)
            pmin = next(p for p in range(7, 57) if prime(p) and p not in small)
            non3, _ = kernel.pay(charge, pmin)
            assert non3 is not None
            orientations = [non3]
            if 5 not in small:
                at5, _ = Kernel(children, expense - fee(5)).pay(charge, 5)
                assert at5 is not None
                orientations.append(at5)
            row = {'small': small, 'root': root, 'non3': orientations}
            counts['ranges'] += 1
            counts['non3_paid'] += len(orientations)
            counts['root_paid' if root else 'root_unpaid'] += 1
            if root is None:
                row['first_nonstrict_root_cutoff'] = failure
                exceptional.append({'small': small, 'children': children,
                                    'charge': charge, 'expense': expense})
            rows.append(row)
        print('Boundary small-coordinate count', j, dict(counts), flush=True)
    assert dict(counts) == {'ranges': 6475, 'non3_paid': 10570, 'root_paid': 5966, 'root_unpaid': 509}
    assert all(len(set(r['small']) & {5, 7, 11}) >= 2 for r in exceptional)
    assert all(set(a['small']) & set(b['small']) for a, b in combinations(exceptional, 2))
    classification = Counter(len(r['small']) for r in exceptional)
    assert dict(classification) == {4: 11, 5: 105, 6: 393}
    return rows, exceptional, {**counts, 'unpaid_small_counts': dict(classification),
                              'selected_positive_coordinate_residuals': 64 * (10570 + 5966)}


def load_helper(path):
    assert sha256(path.read_bytes()).hexdigest() == HELPER_SHA, 'Unexpected Chapter 30 helper'
    spec = importlib.util.spec_from_file_location('independent_chapter30_helper', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Ordinary:
    def __init__(self, helper, cache):
        self.helper = helper
        self.nodes = [(a, b, c, -1, j, 0, 0, 0, -1)
                      for a in (1, 2) for b in (2, 4) for c in (a, 3 - a) for j in range(1, 5)]
        self.envelopes, self.reserves = [], []
        for a, b, c, _, j, *_ in self.nodes:
            gamma = 3 * (a == 1) + (b % 3 == a % 3)
            self.reserves.append(Q(135, 4) + gamma + (9 - gamma) * (Q(c == a, 5) + Q(j == a, 20)))
            self.envelopes.append(helper.envelope(cache, a, b, c, j))
        assert len(self.nodes) == 32 and len(helper.BATCHES) == 72 and helper.QUERIES == 51840
        self.vertex_checks, self.stage_checks = 0, 0

    @lru_cache(None)
    def distribution(self, primes, thresholds):
        if not primes:
            return {1: Q(1)}, Q(1)
        table, mean = self.distribution(primes[:-1], thresholds[:-1])
        p, t = primes[-1], thresholds[-1]
        cap = Q(p - 1, p - 1 - t)
        assert 1 < cap < p
        out = defaultdict(Q)
        # Only multipliers <12 enter a finite hinge lookup; the full first
        # moment is maintained separately and pays the entire omitted tail.
        for m, weight in table.items():
            for new in range(m, 12, m):
                e = new // m - 1
                probability = 1 - cap / p if e == 0 else cap * Q(p - 1, p ** (e + 1))
                assert probability >= 0
                out[new] += weight * probability
        return dict(out), mean * (1 + cap / Q(p - 1))

    @lru_cache(None)
    def stage(self, primes, thresholds):
        p, t = primes[-1], thresholds[-1]
        assert 1 <= t < p - 1 and t <= 12
        table, mean = self.distribution(primes[:-1], thresholds[:-1])
        small = [(m, w) for m, w in table.items() if m < t]
        probability = sum((w for m, w in small), Q(0))
        moment = sum((m * w for m, w in small), Q(0))
        out = []
        for mass, whole, values in self.envelopes:
            numerator = sum((m * w * values[Q(t, m)] for m, w in small), Q(0))
            numerator += (mean - moment) * whole - t * (1 - probability) * mass
            exact = numerator / (p - 1 - t)
            rounded = self.helper.ceil_decimal(exact)
            assert 0 <= exact <= rounded < exact + Q(1, 10 ** 10)
            out.append(rounded)
        return tuple(out)

    def schedule(self, children, thresholds):
        primes = tuple(children[1:])
        caps = (Q(1),) + tuple(Q(p - 1, p - 1 - t) for p, t in zip(primes, thresholds))
        stages = [self.stage(primes[:i], thresholds[:i]) for i in range(1, 6)]
        masses = [(reserve - sum((stage[i] for stage in stages), Q(0))) / 135
                  for i, reserve in enumerate(self.reserves)]
        local = tuple(Q(3, 10) if q == 5 else Q(2, q - 1) for q in children)
        attachments = tuple(a * c for a, c in zip(caps, local))
        assert len(primes) == 5 and len(masses) == 32 and min(masses) > 0
        assert max(attachments) <= Q(1, 2)
        self.vertex_checks += 32
        self.stage_checks += 160
        return min(masses), caps, attachments, self.nodes[masses.index(min(masses))]


def close_core(row, ordinary):
    small, children, E = row['small'], row['children'], row['expense']
    thresholds = IMPROVED if 5 not in children else STANDARD
    m, caps, attachments, worst = ordinary.schedule(children, thresholds)
    placement = None
    if 5 not in children:
        assert 5 not in children and children[0] == 7
        rho = max(attachments)
        assert rho <= Q(1, 3)
        forbidden = set(small)
        outside = tuple(p for p in range(5, 100) if prime(p) and p not in forbidden)[:6]
        assert outside[0] == 5 and max(outside) < 57
        # The actual 5 is absent from this block's descendant prime sets.
        outside_expense = E - fee(5)
        kernel = Kernel(outside, outside_expense)
        candidates = []
        for t in range(1, 32):
            zmin, Z, L = kernel.evaluate(t)
            if zmin <= 0:
                break
            candidates.append((L / (2 * 3 ** t * Z), t, zmin))
        else:
            raise AssertionError('Outside-kernel strict region did not terminate')
        K, cutoff, zmin = min(candidates)
        _, selected_Z, selected_L = kernel.evaluate(cutoff)
        assert K < fee(5)
        descendant_cost = E - (1 - rho) * fee(5)
        absent_cost = E - fee(5)
        outside_cost = E - fee(5) + K
        deletion = max(descendant_cost, absent_cost, outside_cost)
        assert m > deletion
        placement = {'five_descendant_cost': str(descendant_cost),
                     'five_absent_cost': str(absent_cost),
                     'five_outside_root_cost': str(outside_cost),
                     'outside_proxy_children': outside, 'outside_expense': str(outside_expense),
                     'outside_coordinate_caps': list(map(str, kernel.caps)),
                     'outside_cutoff': cutoff, 'outside_min_residual': str(zmin),
                     'outside_Z': str(selected_Z), 'outside_L': str(selected_L),
                     'outside_kernel_cost': str(K)}
    else:
        deletion = E
    assert m > deletion
    return {'small': small, 'children_lower_bounds': children,
            'outside_budget': str(E), 'thresholds': thresholds,
            'coordinate_marginal_caps': ['1'] + list(map(str, caps)),
            'child_attachment_coefficients': list(map(str, attachments)),
            'max_attachment_coefficient': str(max(attachments)),
            'mass_lower_bound': str(m), 'worst_basic_vertex': worst,
            'global_density_cap': str(prod(caps)),
            'placement': placement, 'deletion_upper_bound': str(deletion),
            'survival_lower_bound': str(m - deletion),
            'original_haar_survival_lower_bound': str((m - deletion) / prod(caps))}


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--helper', type=Path, default=Path(__file__).with_name('six_prime_prefix_certificate.py'))
    args = parser.parse_args()
    helper = load_helper(args.helper)
    raw = args.geometry.read_bytes()
    assert sha256(raw).hexdigest() == helper.GEOMETRY_SHA256, 'Unexpected geometry digest'
    geometry = json.loads(raw)
    assert geometry['schema'] == 'six-prime-prefix-geometry-input-v1' and len(geometry['batches']) == 72
    rows, exceptional, counts = boundary()
    ordinary = Ordinary(helper, geometry['batches'])
    cores = [close_core(row, ordinary) for row in exceptional]
    special = [r for r in cores if r['placement'] is not None]
    assert len(cores) == 509 and len(special) == 19
    assert ordinary.vertex_checks == 32 * 509
    assert ordinary.stage_checks == 160 * 509
    result = {
        'schema': 'seven-block-certificate-v1',
        'scope': 'Exact finite arithmetic for all nonempty-small-prime six-child boundary ranges and their exceptional-core budgets. The all-large-child analytic bound, actual submeasure construction, full-cylinder transport, and graph recursion are separate mathematical premises; no Lean replay.',
        'source': {k: geometry[k] for k in ('source_doi', 'source_archive_url', 'source_archive_sha256',
                    'source_verifier_sha256', 'source_geometry_cpp_sha256')},
        'helper_sha256': HELPER_SHA, 'geometry_input_sha256': helper.GEOMETRY_SHA256,
        'author_verifier_imported': False, 'geometry_reexecuted': False,
        'boundary_counts': counts, 'boundary_certificates': rows,
        'core_count': len(cores), 'standard_schedule_paid': len(cores) - len(special),
        'improved_ownership_paid': len(special), 'core_results': cores,
        'basic_vertex_checks': ordinary.vertex_checks, 'rounded_stage_cost_checks': ordinary.stage_checks,
        'unique_geometry_batches': len(helper.BATCHES), 'integer_query_reads': helper.QUERIES,
        'least_core_survival': min(cores, key=lambda r: Q(r['survival_lower_bound'])),
        'least_ownership_survival': min(special, key=lambda r: Q(r['survival_lower_bound'])),
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: 10,570 non-3 and 5,966 root fee comparisons; 509 core budgets, including all 19 ownership cases.')
    print('Smallest core survival:', result['least_core_survival']['survival_lower_bound'])
    print('Smallest ownership survival:', result['least_ownership_survival']['survival_lower_bound'])


if __name__ == '__main__':
    main()
