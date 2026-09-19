#!/usr/bin/env python3
"""Exact actual-parent transports, including full CRT digits and Haar density.

Standalone standard-library checker. Whole-cover fixtures have even moduli;
the odd fixture is explicitly a noncover. No odd-cover or Lean claim is made.
Checks remain active under -O. This file imports no project code or data.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import gcd, lcm
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def factorization(n):
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
    require(gcd(u, v) == 1, 'CRT factors not coprime')
    return (a + u * ((b - a) * pow(u, -1, v) % v)) % (u * v) if v > 1 else a % u


def model(name, aps, whole):
    residues = dict((d, a) for a, d in aps)
    require(len(residues) == len(aps), 'repeated original modulus')
    require(all(d > 1 and 0 <= a < d for a, d in aps), 'invalid original AP')
    Q = lcm(*residues)
    labels = [frozenset(d for a, d in aps if x % d == a) for x in range(Q)]
    private = {m: {x for x, hit in enumerate(labels) if hit == {m}} for m in residues}
    require(all(private.values()), 'nonessential original')
    require(all(labels) == whole, 'whole-cover status mismatch')
    for m, a in residues.items():
        for d, b in residues.items():
            if m != d and d % m == 0:
                require((a - b) % m != 0, 'comparable original APs intersect')
    return dict(name=name, aps=aps, residues=residues, Q=Q, factors=factorization(Q),
                labels=labels, private=private, whole_cover=whole)


def replace_prefix(M, x, m, target_residue):
    """Replace only each q|m low v_q(m) digits, keeping its higher digits."""
    Q = M['Q']
    z = x
    for q, e in factorization(m).items():
        full = q ** M['factors'][q]
        low = q ** e
        coordinate = (z % full) // low * low + target_residue % low
        z = crt(coordinate, full, z % (Q // full), Q // full)
    for q, H in M['factors'].items():
        full = q ** H
        if m % q:
            require(z % full == x % full, 'replacement changed an unrelated CRT coordinate')
        else:
            low = q ** factorization(m)[q]
            require(z % low == target_residue % low, 'replacement missed the parent residue')
            require((z % full) // low == (x % full) // low, 'replacement changed higher digits')
    return z


def first_positive_hit(y0, accepted, bound, L):
    for k in range(1, min(bound, L) + 1):
        y = (y0 + k) % L
        if y in accepted:
            return k, y
    raise ArithmeticError('actual first-hit window has no required private point')


def prefix_transport(M, m, p, e, residue, totals):
    Q, a = M['Q'], M['residues'][m]
    L, D = Q // m, p ** e
    require(m % p != 0 and L % D == 0, 'invalid parent-prefix carrier')
    competitors = [(b, d) for b, d in M['aps'] if d != m and (a - b) % gcd(m, d) == 0]
    kappa, W = len(competitors), 2 ** len(competitors)
    c = ((residue - a) * pow(m, -1, D)) % D
    private_y = {y for y in range(L) if (a + m * y) % Q in M['private'][m]}
    escape_y = {y for y in private_y if y % D != c}
    anchors = list(range(c, L, D))
    require(len(anchors) == L // D, 'wrong number of parent anchors')
    priv, escape = {}, {}
    priv_counts, escape_counts = Counter(), Counter()
    cap_private = min(L // D, (W + D - 1) // D)
    cap_escape = min(L // D, (2 * W + D - 1) // D)
    for y0 in anchors:
        k, y = first_positive_hit(y0, private_y, W, L)
        require(not any((y0 + j) % L in private_y for j in range(1, k)), 'not first private hit')
        z = (a + m * y) % Q
        require(M['labels'][z] == {m}, 'output not actual original-parent private')
        require(z == (a + m * y0 + m * k) % Q, 'wrong literal displacement')
        priv[y0] = y
        priv_counts[y] += 1
        totals['parent_anchor_transports'] += 1
        if D > W:
            require(y % D != c, 'deep transport did not escape')
            recovered = (c + D * (((y - c) % L) // D)) % L
            require(recovered == y0, 'deep rotated-block inverse failed')
            totals['deep_inverse_checks'] += 1
        if escape_y:
            k2, y2 = first_positive_hit(y0, escape_y, 2 * W, L)
            require(k2 < min(2 * W, L), 'escape endpoint bound failed')
            require(not any((y0 + j) % L in escape_y for j in range(1, k2)), 'not first escape')
            escape[y0] = y2
            escape_counts[y2] += 1
            totals['escape_anchor_transports'] += 1
    require(max(priv_counts.values()) <= cap_private, 'private congestion exceeded')
    if D > W:
        require(max(priv_counts.values()) == 1 and cap_private == 1, 'deep map not injective')
    if escape_y:
        require(max(escape_counts.values()) <= cap_escape, 'escape congestion exceeded')
    totals['parent_prefixes'] += 1
    totals['deep_prefixes'] += D > W
    totals['shallow_prefixes'] += D <= W
    totals['empty_escape_prefixes'] += not escape_y
    totals['nonempty_shallow_escape_prefixes'] += bool(escape_y) and D <= W
    totals['escape_window_exceeds_period'] += bool(escape_y) and 2 * W > L
    totals['private_window_exceeds_period'] += W > L
    totals['maximum_private_congestion'] = max(totals['maximum_private_congestion'], max(priv_counts.values()))
    totals['maximum_escape_congestion'] = max(totals['maximum_escape_congestion'], max(escape_counts.values(), default=0))
    return dict(L=L, D=D, c=c, kappa=kappa, W=W, priv=priv, escape=escape,
                cap_private=cap_private, cap_escape=cap_escape)


def reset_and_retail(M, density, q, m, p, D, residue, must_escape, totals):
    """Densities are relative to uniform H_Q, not normalized source probabilities."""
    Q = M['Q']
    full, a_q = q ** M['factors'][q], M['residues'][q] % q
    other, tails = Q // full, full // q
    reset_density = defaultdict(Fraction)
    for x, value in density.items():
        require(M['labels'][x] == {m}, 'reset source lost actual parent provenance')
        coordinate = x % full - x % q + a_q
        z = crt(coordinate, full, x % other, other)
        require(M['labels'][z] == {q}, 'composed reset not prime-private')
        require(z % (p ** M['factors'][p]) == x % (p ** M['factors'][p]), 'reset changed P coordinate')
        if must_escape:
            require(z % D != residue, 'reset lost current P-prefix exclusion')
        reset_density[z] += value
    require(len(reset_density) == len(density), 'reset on a single parent root not injective')
    marginal = defaultdict(Fraction)
    for z, value in reset_density.items():
        marginal[z % other] += value
    output = {}
    for x, total in marginal.items():
        for t in range(tails):
            z = crt(a_q + q * t, full, x, other)
            require(M['labels'][z] == {q}, 'uniform re-tail not prime-private')
            require(not any(max(factorization(d)) < q for d in M['labels'][z]), 'output outside pre-q survivor')
            if must_escape:
                require(z % D != residue, 'uniform re-tail lost P exclusion')
            output[z] = total / tails
    require(sum(output.values()) == sum(density.values()), 'reset/re-tail mass changed')
    require(max(output.values()) <= max(density.values()), 'single-parent reset/re-tail increased density cap')
    totals['reset_retail_compositions'] += 1
    totals['reset_retail_output_atoms'] += len(output)


def actual_children(M, cache, totals):
    Q = M['Q']
    rows = []
    for d, a_d in M['residues'].items():
        for p, e in factorization(d).items():
            D, m = p ** e, d // p ** e
            if m not in M['residues']:
                continue
            a_m = M['residues'][m]
            R = cache[(m, p, e, a_d % D)]
            source = [x for x in range(Q) if x % d == a_d]
            aligned = {replace_prefix(M, x, m, a_m): x for x in source}
            anchors = {(a_m + m * y) % Q for y in R['priv']}
            require(set(aligned) == anchors and len(aligned) == len(source), 'actual CRT source alignment not bijective')
            require(len(source) == Q // d, 'actual child mass denominator')
            for u, x in aligned.items():
                require(replace_prefix(M, u, m, a_d) == x, 'cofactor replacement inverse failed')
            for kind, mapping, cap in [('private', R['priv'], R['cap_private']),
                                        ('escape', R['escape'], R['cap_escape'])]:
                if not mapping:
                    continue
                density = defaultdict(Fraction)
                images = []
                for u, x in aligned.items():
                    y0 = ((u - a_m) // m) % R['L']
                    target = (a_m + m * mapping[y0]) % Q
                    value = Fraction(4 + x % 5, 4)
                    density[target] += value
                    images.append(target)
                    if R['D'] > R['W'] and kind == 'private':
                        y = mapping[y0]
                        recovered_y0 = (R['c'] + D * (((y - R['c']) % R['L']) // D)) % R['L']
                        recovered_u = (a_m + m * recovered_y0) % Q
                        require(replace_prefix(M, recovered_u, m, a_d) == x, 'complete source recovery failed')
                    totals['actual_child_transport_atoms'] += 1
                    totals['repairs_changing_other_prime_coordinates'] += any(
                        q != p and m % q and target % (q ** H) != u % (q ** H)
                        for q, H in M['factors'].items())
                require(sum(density.values()) == sum(Fraction(4 + x % 5, 4) for x in source), 'weighted source mass changed')
                require(max(density.values()) <= 2 * cap, 'weighted Haar density bound failed')
                require(max(Counter(images).values()) <= cap, 'actual-source fibre count failed')
                for q in factorization(m):
                    if q in M['residues']:
                        reset_and_retail(M, density, q, m, p, D, a_d % D, kind == 'escape', totals)
            rows.append(dict(parent=m, child=d, prime=p, exponent=e, kappa=R['kappa'],
                             source_points=len(source), source_mass=str(Fraction(len(source), Q)),
                             private_cap=R['cap_private'], escape_cap=R['cap_escape'],
                             escape_nonempty=bool(R['escape']), deep=D > R['W']))
    return rows


def tuple_mass(M, totals):
    if not M['whole_cover']:
        return None
    p, Q = max(M['factors']), M['Q']
    full, prime_root = p ** M['factors'][p], M['residues'][p] % p
    B, tails = Q // full, full // p
    R = [x for x in range(B) if all(x % d != a for d, a in M['residues'].items() if d % p)]
    roots = [r for r in range(p) if r != prime_root]
    selected, best_key = None, None
    for x, t in product(R, range(tails)):
        options = []
        for r in roots:
            z = crt(r + p * t, full, x, B)
            labels = [d for d in M['labels'][z] if d % p == 0 and d // p ** factorization(d)[p] > 1]
            options.append(sorted(labels))
        for candidate in product(*options):
            cofactors = [d // p ** factorization(d)[p] for d in candidate]
            if len(set(cofactors)) == len(cofactors):
                key = (-max(factorization(d)[p] for d in candidate),
                       -sum(m in M['residues'] for m in cofactors), candidate)
                if best_key is None or key < best_key:
                    selected, best_key = candidate, key
    require(selected is not None, 'whole-cover fixture has no synchronized tuple')
    ms = [d // p ** factorization(d)[p] for d in selected]
    U = [x for x in R if all(x % m == M['residues'][d] % m for d, m in zip(selected, ms))]
    J = [t for t in range(tails) if all((r + p * t - M['residues'][d]) % (d // m) == 0
                                      for r, d, m in zip(roots, selected, ms))]
    theta = Fraction(len(J), tails)
    base = Fraction(len(U), B)
    lam = base * theta
    require(lam > 0, 'selected tuple product event empty')
    totals['nontrivial_tuple_tail_checks'] += theta < 1
    rows = []
    for r, d, m in zip(roots, selected, ms):
        lifted = {crt(r + p * t, full, x, B) for x, t in product(U, J)}
        expanded = {z for z in range(Q) if z % B in U and z % (d // m) == M['residues'][d] % (d // m)}
        require(Fraction(len(lifted), Q) == lam / p, 'fixed-root lift lost 1/p')
        require(Fraction(len(expanded), Q) == base / (d // m), 'expanded child mass wrong')
        require(lifted <= expanded and all(M['residues'][d] == z % d for z in expanded), 'actual source lost child label')
        require(all(all(z % h != a for h, a in M['residues'].items() if h % p) for z in expanded), 'expanded child not in R_p source')
        totals['fixed_root_mass_checks'] += 1
        totals['strict_child_source_expansions'] += len(expanded) > len(lifted)
        rows.append(dict(child=d, parent_present=m in M['residues'], fixed_root_mass=str(lam / p),
                         expanded_child_mass=str(base / (d // m))))
    return dict(prime=p, tuple=list(selected), base_mass=str(base), theta=str(theta),
                cofactor_tail_mass=str(lam), roots=rows)


def run():
    fixtures = [
        ('even period-12 whole cover', [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)], True),
        ('even period-144 whole cover', [(0, 2), (0, 3), (1, 4), (5, 6), (7, 24),
                                         (7, 36), (19, 48), (67, 72), (91, 144)], True),
        ('even period-960 whole cover', [(0, 2), (0, 3), (3, 4), (0, 5), (1, 8), (1, 10),
                                         (13, 16), (17, 20), (13, 40), (69, 160), (149, 320),
                                         (469, 480), (629, 960)], True),
        ('odd NONCOVER: essential-parent transport only', [(0, 3), (0, 5), (1, 75)], False),
    ]
    totals = Counter()
    results = []
    for name, aps, whole in fixtures:
        M = model(name, aps, whole)
        cache = {}
        for m, a in M['residues'].items():
            kappa = sum(d != m and (a - b) % gcd(m, d) == 0 for b, d in aps)
            totals['essential_parents'] += 1
            totals['zero_competitor_parents'] += kappa == 0
            for p, H in M['factors'].items():
                if m % p == 0:
                    continue
                for e in range(1, H + 1):
                    for residue in range(p ** e):
                        cache[m, p, e, residue] = prefix_transport(M, m, p, e, residue, totals)
        results.append(dict(name=name, APs=aps, period=M['Q'], whole_cover=whole,
                            covered_points=sum(bool(x) for x in M['labels']),
                            actual_children=actual_children(M, cache, totals),
                            actual_tuple_source=tuple_mass(M, totals)))
    for key in ('deep_inverse_checks', 'shallow_prefixes', 'nonempty_shallow_escape_prefixes',
                'empty_escape_prefixes', 'escape_window_exceeds_period',
                'private_window_exceeds_period', 'zero_competitor_parents',
                'nontrivial_tuple_tail_checks', 'strict_child_source_expansions',
                'repairs_changing_other_prime_coordinates'):
        require(totals[key] > 0, 'missing intended boundary branch: ' + key)
    require(totals['maximum_private_congestion'] > 1 and totals['maximum_escape_congestion'] > 1,
            'fixtures never exercise noninjective shallow transport')
    return dict(scope='Exact complete-period actual-AP checks. Whole covers have even moduli; the odd list does not cover. No hypothetical odd-cover instance, extremal status, Lean proof, or global closure is asserted.',
                arithmetic='Python standard library, exact integers and rational Haar densities',
                totals=dict(sorted(totals.items())), fixtures=results)


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
