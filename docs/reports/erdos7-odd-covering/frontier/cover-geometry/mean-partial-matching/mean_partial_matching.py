#!/usr/bin/env python3
"""Exact full-tail partial ranks, first-use cylinders, and one original budget.

Standalone standard library. Sharp prefix models cover every local tail but
are not whole integer covers. Actual whole-cover fixtures have even moduli.
Only the period-12 fixture supplies all original parents for the all-private
budget. Checks remain active under -O; no Lean or odd-cover claim is made.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm, prod
import json


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def factors(n):
    answer = {}
    q = 2
    while q * q <= n:
        while n % q == 0:
            answer[q] = answer.get(q, 0) + 1
            n //= q
        q += 1
    if n > 1:
        answer[n] = 1
    return answer


def crt(a, u, b, v):
    return (a + u * ((b - a) * pow(u, -1, v) % v)) % (u * v) if v > 1 else a % u


def maximum_matching(graph):
    owner = {}

    def augment(root, seen):
        for color in sorted(graph[root]):
            if color in seen:
                continue
            seen.add(color)
            if color not in owner or augment(owner[color], seen):
                owner[color] = root
                return True
        return False

    for root in graph:
        augment(root, set())
    return {root: color for color, root in owner.items()}


def analyze(q, H, roots, labels, counters):
    """Labels are (root, color, depth, prefix, original-id); color 0 is pure.

    First-cover ties use the fixed (color, original-id) label order, which
    is independent of future tail digits. This is required for a first-use
    event at depth h to be an entire depth-h cylinder.
    """
    N, tail_count = H - 1, q ** (H - 1)
    check(len(roots) == q - 1 and len(set(roots)) == len(roots), 'wrong root inventory')
    check(len({(color, depth) for _, color, depth, _, _ in labels}) == len(labels),
          'a color repeats at one depth')
    check(all(root in roots and 0 <= depth <= N and 0 <= prefix < q ** depth
              for root, _, depth, prefix, _ in labels), 'invalid literal prefix')
    check(not any(color == 0 and depth == 0 for _, color, depth, _, _ in labels),
          'pure color at depth zero')
    first_events = defaultdict(set)
    color_counts = []
    Ks, ranks, selected_matchings = [], [], []
    pure_total = 0
    for t in range(tail_count):
        active = {root: [label for label in labels
                         if label[0] == root and t % (q ** label[2]) == label[3]]
                  for root in roots}
        check(all(active.values()), 'local model fails full-tail coverage')
        # Choose the shallowest cover, then the pre-fixed label order.
        chosen = {root: min(active[root], key=lambda a: (a[2], a[1], a[4])) for root in roots}
        counts = Counter(label[1] for label in chosen.values())
        color_counts.append(counts)
        pure_total += counts[0]
        first = {}
        for label in chosen.values():
            root, color, depth, prefix, identity = label
            if color and (color not in first or depth < first[color][2]):
                first[color] = label
        for color, label in first.items():
            first_events[(color, label[2], label[3])].add(t)
        K = len(first)
        selected_matchings.append({label[0]: label for label in first.values()})
        check(len({label[0] for label in first.values()}) == K, 'partial matching repeats a root')
        graph = {root: {label[1] for label in active[root] if label[1]} for root in roots}
        matching = maximum_matching(graph)
        check(all(color in graph[root] for root, color in matching.items()), 'matching lost an actual edge')
        deficiency = 0
        for size in range(len(roots) + 1):
            for subset in combinations(roots, size):
                neighbors = set().union(*(graph[root] for root in subset))
                deficiency = max(deficiency, size - len(neighbors))
                counters['hall_subsets'] += 1
        rank = len(matching)
        check(rank == q - 1 - deficiency and rank >= K, 'maximum rank or Hall deficiency mismatch')
        Ks.append(K)
        ranks.append(rank)
        counters['tail_states'] += 1
        counters['first_cover_root_choices'] += q - 1
    for (color, h, prefix), event in first_events.items():
        expected = {t for t in range(tail_count) if t % (q ** h) == prefix}
        check(event == expected, 'first-use event is not the complete claimed prefix cylinder')
        repetitions = sum(color_counts[t][color] - 1 for t in event)
        conditional_cap = Fraction(1 - Fraction(1, q ** (N - h)), q - 1)
        check(Fraction(repetitions, len(event)) <= conditional_cap, 'first-use repeated-depth bound')
        counters['first_use_cylinders'] += 1
    events = list(first_events)
    for i, (color, h, prefix) in enumerate(events):
        for color2, h2, prefix2 in events[i + 1:]:
            if color == color2:
                check(prefix % (q ** min(h, h2)) != prefix2 % (q ** min(h, h2)),
                      'same-color first-use cylinders are not an antichain')
    epsilon = Fraction(1, tail_count)
    mean_K = Fraction(sum(Ks), tail_count)
    mean_rank = Fraction(sum(ranks), tail_count)
    T = len(first_events)
    check(Fraction(pure_total, tail_count) <= (1 - epsilon) / (q - 1), 'pure-column tail bound')
    check(q * mean_K >= q * (q - 2) + epsilon * (1 + T), 'finite first-use accounting')
    check(mean_K > q - 2 and max(Ks) == q - 1 and T >= q - 1, 'integer first-use count step')
    gamma = q - 2 + epsilon
    check(mean_rank >= mean_K >= gamma, 'sharp finite mean-rank lower bound')
    counters['local_models'] += 1
    return dict(mean_first=mean_K, mean_rank=mean_rank, gamma=gamma, T=T,
                minimum_rank=min(ranks), maximum_rank=max(ranks), first_sizes=Ks,
                ranks=ranks, selected=selected_matchings)


def sharp_labels(q, H):
    N, last = H - 1, q - 2
    labels = [(root, root + 1, 0, 0, root + 1) for root in range(q - 2)]
    for depth in range(1, N + 1):
        for branch, color in enumerate(list(range(1, q - 1)) + [0]):
            prefix = q ** (depth - 1) - 1 + branch * q ** (depth - 1)
            labels.append((last, color, depth, prefix, len(labels) + 1))
    labels.append((last, q - 1, N, q ** N - 1, len(labels) + 1))
    return tuple(range(q - 1)), labels


def prepare(name, aps):
    residues = {d: a for a, d in aps}
    check(len(residues) == len(aps), 'repeated original modulus')
    Q = lcm(*residues)
    ps = factors(Q)
    check(all(q in residues for q in ps), 'missing original prime label')
    cover = [frozenset(d for d, a in residues.items() if z % d == a) for z in range(Q)]
    check(all(cover), 'actual fixture is not a whole cover')
    check(all(any(hit == {d} for hit in cover) for d in residues), 'redundant original')
    for m, a in residues.items():
        for d, b in residues.items():
            if d != m and d % m == 0:
                check((b - a) % m != 0, 'comparable original classes intersect')
    return dict(name=name, residues=residues, Q=Q, primes=ps, cover=cover)


def actual_models(M, counters):
    cache, rows, missing = {}, [], set()
    for q, H in M['primes'].items():
        full, B = q ** H, M['Q'] // q ** H
        roots = tuple(r for r in range(q) if r != M['residues'][q] % q)
        base = [x for x in range(B) if all(x % d != a for d, a in M['residues'].items() if d % q)]
        check(bool(base), 'empty actual private cofactor region')
        sums_first, sums_rank = Fraction(), Fraction()
        for x in base:
            labels = []
            for d, a in M['residues'].items():
                if d % q or d == q:
                    continue
                e = factors(d)[q]
                m = d // q ** e
                if x % m != a % m:
                    continue
                label = (a % q, 0 if m == 1 else m, e - 1, a // q % (q ** (e - 1)), d)
                labels.append(label)
                if m > 1 and m not in M['residues']:
                    missing.add(m)
            report = analyze(q, H, roots, labels, counters)
            for t in range(q ** (H - 1)):
                for root in roots:
                    actual = crt(root + q * t, full, x, B)
                    prefix_active = {label[4] for label in labels
                                     if label[0] == root and t % (q ** label[2]) == label[3]}
                    check(prefix_active == set(M['cover'][actual]), 'prefix graph differs from complete actual labels')
                    counters['actual_root_label_checks'] += 1
            cache[q, x] = report
            sums_first += report['mean_first']
            sums_rank += report['mean_rank']
        rows.append(dict(prime=q, height=H, cofactor_states=len(base),
                         mean_first=str(sums_first / len(base)), mean_rank=str(sums_rank / len(base)),
                         lower=str(q - 2 + Fraction(1, q ** (H - 1)))))
    return cache, rows, sorted(missing)


def beta_rho(q, m, primes):
    free = [p for p in primes if p != q and m % p]
    polynomial = [Fraction(1)]
    for p in free:
        new = [Fraction()] * (len(polynomial) + 1)
        for j, v in enumerate(polynomial):
            new[j] += v * Fraction(p - 1, p)
            new[j + 1] += v / p
        polynomial = new
    b = 2 if m in primes else 1
    beta = sum((v / (j + b) for j, v in enumerate(polynomial)), Fraction())
    rho = prod((Fraction(p - 1, p) for p in free), start=Fraction(1))
    check(beta / rho >= Fraction(1, b), 'wrong prime-exclusion factor')
    return beta, rho


def complete_parent_budget(M, cache, counters):
    Q, residues, primes = M['Q'], M['residues'], M['primes']
    source_sets = defaultdict(set)
    weights, source_mass = {}, {}
    coarse_raw = coarse_weighted = Fraction()
    raw_integral = weighted_integral = Fraction()
    for q, H in primes.items():
        B = Q // q ** H
        alpha_q = Fraction(q, q - 1) * (1 - Fraction(1, q ** H))
        gamma = q - 2 + Fraction(1, q ** (H - 1))
        private = [z for z, hit in enumerate(M['cover']) if hit == {q}]
        source_mass[q] = sum((1 + Fraction((z % B) % 3, 4) for z in private), Fraction()) / Q
        for z in private:
            x, t = z % B, (z % (q ** H)) // q
            weights[q, z] = 1 + Fraction(x % 3, 4)
            selected = cache[q, x]['selected'][t]
            raw_integral += Fraction(len(selected), Q) / (2 * alpha_q)
            weighted_integral += Fraction(len(selected), Q) * weights[q, z] / (4 * alpha_q)
            for root, label in selected.items():
                color, d = label[1], label[4]
                check(color in residues, 'invented cofactor parent in all-private budget')
                actual = crt(root + q * t, q ** H, x, B)
                check(d in M['cover'][actual], 'selected partial edge lost original child')
                source_sets[q, color].add(z)
        coarse_raw += gamma * Fraction(len(private), Q) / (2 * alpha_q)
        coarse_weighted += gamma * source_mass[q] / (4 * alpha_q)
    actual_charge = weighted_charge = capacity_sum = Fraction()
    allocation = [Fraction() for _ in range(Q)]
    for (q, m), selected in source_sets.items():
        children = [d for d in residues if d % q == 0 and d // q ** factors(d)[q] == m]
        alpha = sum((Fraction(q, q ** factors(d)[q]) for d in children), Fraction())
        beta, rho = beta_rho(q, m, primes)
        measure = Fraction(len(selected), Q)
        weighted_measure = sum((weights[q, z] for z in selected), Fraction()) / Q
        check(measure <= alpha * rho / (q * m), 'partial source exceeds exact original cylinder capacity')
        check(weighted_measure / 2 <= alpha * rho / (q * m), 'weighted density comparison failed')
        capacity = Fraction()
        for z, hit in enumerate(M['cover']):
            if q in hit and m in hit:
                prime_count = len(hit.intersection(primes))
                allocation[z] += Fraction(1, prime_count)
                capacity += Fraction(1, Q * prime_count)
        check(capacity == beta / (q * m), 'CRT capacity does not equal pointwise allocation')
        actual_charge += beta * measure / (alpha * rho)
        weighted_charge += beta * weighted_measure / (2 * alpha * rho)
        capacity_sum += capacity
        counters['all_private_parent_channels'] += 1
    for z, amount in enumerate(allocation):
        check(amount <= len(M['cover'][z]) - 1, 'shared original surplus charged more than once')
    surplus = sum((Fraction(len(hit) - 1, Q) for hit in M['cover']), Fraction())
    check(coarse_raw <= raw_integral <= actual_charge <= capacity_sum <= surplus, 'all-private raw budget chain')
    check(coarse_weighted <= weighted_integral <= weighted_charge <= capacity_sum, 'tail-uniform weighted budget chain')
    return dict(period=Q, all_original_parents_present=True, raw_coarse=str(coarse_raw),
                raw_partial_integral=str(raw_integral), raw_CA9=str(actual_charge),
                weighted_coarse=str(coarse_weighted), weighted_partial_integral=str(weighted_integral),
                weighted_CA10=str(weighted_charge), allocated_capacity=str(capacity_sum),
                H_cov=str(surplus), weighted_density_bound=2,
                weighted_law='density 1+(x mod3)/4 on Priv_q, uniform in the complete q-tail')


def run():
    counters, sharp = Counter(), []
    for q in (2, 3, 5, 7):
        for H in range(1, 5):
            roots, labels = sharp_labels(q, H)
            r = analyze(q, H, roots, labels, counters)
            check(r['mean_first'] == r['mean_rank'] == r['gamma'], 'sharp construction misses equality')
            sharp.append(dict(q=q, H=H, mean_rank=str(r['mean_rank']), tail_points=q ** (H - 1)))
    # Full-tail local model with one all-pure leaf: a point-mass tail law can
    # have rank zero even for q=3. It is not an odd whole covering system.
    labels = [(0, 0, 1, 0, 1), (1, 0, 2, 0, 2), (0, 1, 1, 1, 3), (0, 2, 1, 2, 4)]
    labels += [(1, 2 + t, 2, t, 4 + t) for t in range(1, 9)]
    nonuniform = analyze(3, 3, (0, 1), labels, counters)
    check(nonuniform['ranks'][0] == 0, 'nonuniform-tail control lost the rank-zero leaf')
    fixtures = [
        ('even period-12 whole cover', [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]),
        ('even period-144 whole cover', [(0, 2), (0, 3), (1, 4), (5, 6), (7, 24),
                                        (7, 36), (19, 48), (67, 72), (91, 144)]),
        ('even period-960 whole cover', [(0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
                                        (13, 16), (17, 20), (13, 40), (69, 160), (149, 320),
                                        (469, 480), (629, 960)]),
    ]
    actual, budget = [], None
    for name, aps in fixtures:
        M = prepare(name, aps)
        cache, rows, missing = actual_models(M, counters)
        actual.append(dict(name=name, period=M['Q'], local_rank=rows, missing_original_parents=missing,
                           all_private_budget_tested=M['Q'] == 12))
        if M['Q'] == 12:
            check(not missing, 'period-12 fixture lacks a required cofactor parent')
            budget = complete_parent_budget(M, cache, counters)
        else:
            check(bool(missing), 'missing-parent boundary was not exercised')
    return dict(scope='Exact finite local full-tail ranks and literal AP graphs. Sharp/local models are not whole integer covers; actual whole-cover fixtures have even moduli. Only period12 tests the all-private budget with all parents. No odd-cover, Lean, or global nonexistence claim.',
                totals=dict(sorted(counters.items())), sharp_local_models=sharp,
                nonuniform_tail_control=dict(q=3, H=3, rank_at_tail_zero=0,
                                             uniform_mean_rank=str(nonuniform['mean_rank'])),
                actual_cover_models=actual, complete_parent_budget=budget)


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
