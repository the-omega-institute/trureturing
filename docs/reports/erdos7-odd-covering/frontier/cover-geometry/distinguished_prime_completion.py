"""Exact controls for completion along a declared original prime coordinate.

Existing four-prime certificates supply the universal inputs. Small-prime
fixtures use their measured survival, never the asymptotic cutoff. Import
performs no computation, and all checks remain active under python -O.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import ceil, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parameters(root):
    certificate = json.loads((root / 'certificates/common_density_head_coupled_certificate.json').read_text())
    baseline = json.loads((root / 'frontier/cover-geometry/five_core_cylinder_profiles.json').read_text())
    gamma = F(certificate['head_bound'])
    old_density = F(baseline['baseline_reproduced']['profile']['15'])
    require(certificate['prime_support'] == [3, 5, 7, 11], 'original core support')
    R = F(46, 5)
    require(gamma == F(4939031, 47730) and old_density == F(720, 29), 'existing source constants')
    require((1 + R)**2 > gamma, 'one maximizing layout and Jensen give the strict mean bound')
    expectation = F(13, 12) * R
    threshold = F(1313, 120)
    good_mass = (1 - expectation / threshold) / old_density
    margin = F(143, 12) - threshold
    M1 = prod(F(p, p - 1) for p in certificate['prime_support'])
    M2 = prod(F(p*(p + 1), (p - 1)**2) for p in certificate['prime_support'])
    density = 279
    N = ceil(density*M2)
    require(expectation == F(299, 30) and good_mass == F(29, 8080), 'positive-mass conversion')
    require(margin == F(39, 40) and 1/good_mass < density, 'pointwise margin and density cap')
    require(M1 == F(77, 32) and M2 == F(231, 20) and N == 3223, 'all-height core moment sums')
    require(324*density*M1 == F(1740123, 8), 'unchanged weighted tail coefficient')
    require(324*density*M1 < 3**6 * N**3, 'cutoff makes the weighted tail less than 3^-250')
    return dict(core_primes=certificate['prime_support'], minimum_distinguished_prime=13,
                existing_Gamma_upper=gamma, existing_Haar_density_cap=old_density,
                nonunit_layout_mean_strict_upper=R, Jensen_square_slack=(1 + R)**2 - gamma,
                core_completion_mean_strict_upper=expectation, good_load_threshold=threshold,
                good_Haar_mass_strict_lower=good_mass, minimum_completion_margin=margin,
                Haar_density_cap=density, M1=M1, M2=M2, cutoff_integer=N,
                cutoff='3^256 * 3223^3', weighted_tail_numerator=324*density*M1,
                source_scope='Same uniform complete old survivor law; arbitrary original residues and finite heights.')


def crt(pairs):
    modulus = prod(m for m, _ in pairs)
    value = sum(a*(modulus//m)*pow(modulus//m, -1, m) for m, a in pairs) % modulus
    require(all(value % m == a % m for m, a in pairs), 'literal CRT')
    return modulus, value


def fixture(parent):
    Q, H, outside = 3, 3, (5, 7)
    core = [(3, 0)]
    for e in range(1, H + 1):
        core.append((parent**e, e - 1))
        core.append(crt([(3, 1 if e != 2 else 2), (parent**e, e)]))
    labels = []

    def add(e, a, head, phases, phase):
        pairs = list(phases.items()) + ([(a, head)] if a > 1 else [])
        if e:
            pairs.append((parent**e, phase))
        modulus, residue = crt(pairs)
        require(modulus == parent**e * a * prod(phases), 'original numerical label')
        labels.append(dict(modulus=modulus, residue=residue, e=e, a=a,
                           outside=tuple(sorted(phases))))

    for p, head in ((5, 1), (7, 2)):
        add(0, 1, 0, {p: 0}, 0)
        add(0, 3, head, {p: 1}, 0)
        add(1, 1, 0, {p: 2}, 1)
        add(1, 3, head, {p: 3}, 2)
    add(0, 1, 0, {5: 4, 7: 4}, 0)
    add(1, 1, 0, {5: 1, 7: 6}, 3)
    add(1, 3, 1, {5: 4, 7: 5}, 4)
    for e in (2, 3):
        for a in (1, 3):
            for support in ((5,), (7,), (5, 7)):
                phases = {p: (a + e*(2 if p == 5 else 3)) % p for p in support}
                add(e, a, 1 if e == 2 else 2, phases, a + e)
    all_originals = core + [(v['modulus'], v['residue']) for v in labels]
    require(len(all_originals) == len({m for m, _ in all_originals}) == 30, 'distinct original moduli')
    require(all(m > 1 and m % 2 and 0 <= a < m for m, a in all_originals), 'odd nonunit originals')

    cuts = {}
    for p in outside:
        e = 0
        while 3**(e + 1) <= p:
            e += 1
        cuts[p] = min(H, e)
    require(cuts == {5: 1, 7: 1}, 'base-three auxiliary cuts, independent of the parent')
    early = [v for v in labels if v['e'] <= cuts[max(v['outside'])]]

    def hits(v, x, word):
        return (x % v['a'] == v['residue'] % v['a'] and
                all(word[outside.index(p)] == v['residue'] % p for p in v['outside']))

    sigma = {}
    branches = Counter()
    for x in (1, 2):
        law = {(): F(1, 2)}
        for p in outside:
            next_law = {}
            assigned = [v for v in early if max(v['outside']) == p]
            for prefix, mass in law.items():
                forbidden = {v['residue'] % p for v in assigned
                             if x % v['a'] == v['residue'] % v['a'] and
                             all(prefix[outside.index(q)] == v['residue'] % q
                                 for q in v['outside'] if q != p)}
                alpha = F(len(forbidden), p)
                row = {}
                if mass:
                    branches['low' if alpha <= F(1, 2) else 'high'] += 1
                for leaf in range(p):
                    if alpha <= F(1, 2):
                        density = F(0) if leaf in forbidden else 1/(1 - alpha)
                    else:
                        density = (2*alpha - 1)/alpha if leaf in forbidden else F(2)
                    require(0 <= density <= 2, 'conditional density cap')
                    row[leaf] = density/p
                    next_law[prefix + (leaf,)] = mass*row[leaf]
                require(sum(row.values()) == 1, 'every row is normalized')
            law = next_law
        sigma.update({(x,) + word: mass for word, mass in law.items()})
    require(sum(sigma.values()) == 1 and branches['low'] and branches['high'], 'one full-history law')
    good = {key for key in sigma if not any(hits(v, key[0], key[1:]) for v in early)}
    survival = sum(sigma[key] for key in good)
    require(0 < survival < 1, 'measured global survival')
    nu = {key: mass/survival if key in good else F(0) for key, mass in sigma.items()}
    require(sum(nu.values()) == 1, 'one globally conditioned law')
    marginals = {x: sum(m for key, m in nu.items() if key[0] == x) for x in (1, 2)}
    require(marginals[1] != F(1, 2), 'global conditioning genuinely changes the core marginal')
    query_count = 0
    for a in (1, 3):
        for head in range(a):
            for support in ((), (5,), (7,), (5, 7)):
                for values in product(*(range(p) for p in support)):
                    hit = lambda key: key[0] % a == head and all(key[1 + outside.index(p)] == b for p, b in zip(support, values))
                    before = sum(m for key, m in sigma.items() if hit(key))
                    after = sum(m for key, m in nu.items() if hit(key))
                    cap = F(3, 2)*F(2**len(support), a*prod(support))
                    require(before <= cap and after <= cap/survival, 'same-law joint cylinder bounds')
                    query_count += 1
    tail = F(0)
    three_weight_majorant = F(0)
    for v in labels:
        probability = sum(m for key, m in nu.items() if hits(v, key[0], key[1:]))
        if v in early:
            require(probability == 0, 'all early original cofactor events are avoided')
        if v['e']:
            tail += F(1, parent**(v['e'] - 1))*probability
            three_weight_majorant += F(1, 3**(v['e'] - 1))*probability
    require(0 < tail <= three_weight_majorant, 'parent weights dominated without relabelling originals')
    literal_checks = 0
    actual_escape = F(0)
    for key, mass in nu.items():
        if not mass:
            continue
        x, *word = key
        pure = sum(F(1, parent**e) for e in range(1, H + 1))
        core_cost = sum(F(1, parent**e) for e in range(1, H + 1)
                        if x == (1 if e != 2 else 2))
        tail_cost = sum(F(1, parent**v['e']) for v in labels if v['e'] and hits(v, x, word))
        survivors = 0
        for coordinate in range(parent**H):
            _, integer = crt([(Q, x), (5, word[0]), (7, word[1]), (parent**H, coordinate)])
            covered = any(integer % modulus == residue for modulus, residue in all_originals)
            survivors += not covered
            literal_checks += 1
        escape = F(survivors, parent**H)
        require(escape >= 1 - pure - core_cost - tail_cost, 'literal fibre obeys the original capacity bound')
        actual_escape += mass*escape
    require(actual_escape > 0, 'literal whole-family noncoverage for the fixture')
    return dict(parent_prime=parent, core_period=Q, parent_height=H,
                outside_primes=outside, auxiliary_early_cuts=cuts, actual_originals=all_originals,
                original_count=len(all_originals), kernel_branches=dict(branches),
                measured_global_survival=survival, final_core_marginal=marginals,
                weighted_tail_completion=tail, base_three_weight_majorant=three_weight_majorant,
                joint_cylinder_queries=query_count, literal_full_CRT_checks=literal_checks,
                average_actual_parent_fibre_escape=actual_escape,
                scope='Small outside primes use measured survival only; this is not a large-cutoff instance.')


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    result = dict(parameters=parameters(root), literal_controls=[fixture(p) for p in (13, 17)])
    payload = json.dumps(encode(result), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
        print(json.dumps(encode(dict(parameters=result['parameters'], literal_controls=[
            {k: v for k, v in row.items() if k != 'actual_originals'} for row in result['literal_controls']])), indent=2))
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
