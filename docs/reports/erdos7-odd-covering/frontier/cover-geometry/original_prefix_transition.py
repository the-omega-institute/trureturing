#!/usr/bin/env python3
"""Exact original-prefix cells and same-chain full-Haar clipped transitions.

Research evaluator for the original327/334 same-chain consumers.
Exact finite arithmetic and reproducible checks; not a Lean certificate.
No residue period is enumerated by the transition compiler. The test oracle
enumerates small full periods independently. Original numerical labels and
all future prefix tests are retained. Standard library only.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from math import prod
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


@lru_cache(maxsize=None)
def is_prime(p):
    if type(p) is not int or p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    d = 3
    while d*d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def coordinate_powers(coords, canonical):
    require(isinstance(coords, dict) and bool(coords), 'An original label has a nonempty coordinate dictionary')
    powers = {}
    for p, item in coords.items():
        require(type(p) is int and p > 2 and is_prime(p), 'Original coordinate bases are actual odd primes')
        require(isinstance(item, (tuple, list)) and len(item) == 2, 'Each original coordinate is an exponent/residue pair')
        e, r = item
        require(type(e) is int and e >= 1 and type(r) is int, 'Original exponents are positive integers and residues are integers')
        powers[p] = p**e
        if canonical:
            require(0 <= r < powers[p], 'Stored original coordinate residues are canonical')
    return powers


def validate_label(label):
    require(isinstance(label, dict) and {'modulus', 'residue', 'coords'} <= set(label), 'Every original label retains its modulus, residue and full coordinates')
    powers = coordinate_powers(label['coords'], canonical=True)
    d, a = label['modulus'], label['residue']
    require(type(d) is int and d == prod(powers.values()) and d > 1 and d % 2 == 1, 'Original modulus equals its complete odd prime-power factorization')
    require(type(a) is int and 0 <= a < d, 'Stored original numerical residue is canonical')
    require(all(a % powers[p] == r for p, (_, r) in label['coords'].items()), 'Original numerical residue agrees with every stored prime-power residue')


def original(coords):
    """coords maps prime to (positive exponent, literal prefix residue)."""
    powers = coordinate_powers(coords, canonical=False)
    d = prod(powers.values())
    a = sum((r % powers[p]) * (d//powers[p]) * pow(d//powers[p], -1, powers[p])
            for p, (_, r) in coords.items()) % d
    require(all(a % powers[p] == r % powers[p] for p, (_, r) in coords.items()), 'Literal CRT reconstruction')
    result = dict(modulus=d, residue=a, coords={p: (e, r % powers[p]) for p, (e, r) in coords.items()})
    validate_label(result)
    return result


def inside(child, parent, p):
    e, a = child
    f, b = parent
    return e >= f and a % (p**f) == b


def prefix_cells(p, labels):
    targets = {(0, 0)} | {tuple(c['coords'][p]) for c in labels if p in c['coords']}
    nodes = sorted(targets)
    children = {v: [] for v in nodes}
    for v in nodes[1:]:
        ancestors = [u for u in nodes if u != v and inside(v, u, p)]
        parent = max(ancestors, key=lambda x: x[0])
        children[parent].append(v)
    cells = []
    for v in nodes:
        mass = F(1, p**v[0]) - sum((F(1, p**w[0]) for w in children[v]), F(0))
        require(mass >= 0, 'Laminar children are disjoint inside their parent')
        if mass:
            mask = sum(1 << i for i, c in enumerate(labels)
                       if p not in c['coords'] or inside(v, c['coords'][p], p))
            cells.append(dict(node=v, children=tuple(children[v]), mass=mass, matches=mask))
    require(sum(c['mass'] for c in cells) == 1, 'All omitted digits paid exactly')
    require(len(cells) <= len(targets), 'At most N queried prefixes plus one cell')
    return cells


def atom_cells(p, labels):
    height = max((c['coords'].get(p, (0, 0))[0] for c in labels), default=0)
    period = p**height
    return [dict(mass=F(1, period), matches=sum(1 << i for i, c in enumerate(labels)
                if p not in c['coords'] or x % (p**c['coords'][p][0]) == c['coords'][p][1]))
            for x in range(period)]


def audit_cells(p, labels):
    compressed, atoms = prefix_cells(p, labels), atom_cells(p, labels)
    expected = defaultdict(F)
    for c in atoms:
        expected[c['matches']] += c['mass']
    actual = defaultdict(F)
    for c in compressed:
        actual[c['matches']] += c['mass']
    require(actual == expected, 'Compressed joint original-label tests equal full Haar period')
    period = len(atoms)
    for x in range(period):
        containing = [c for c in compressed if x % (p**c['node'][0]) == c['node'][1]
                      and not any(x % (p**e) == a for e, a in c['children'])]
        require(len(containing) == 1, 'Difference cells partition every full-period atom')
    return dict(prime=p, period=period, queried_prefixes=len({tuple(c['coords'][p]) for c in labels if p in c['coords']}), cells=len(compressed))


def initialize(labels, incoming):
    states = defaultdict(F)
    for coords, mass in incoming:
        require(mass >= 0, 'Positive incoming source')
        if mass == 0:
            continue
        mask = sum(1 << i for i, c in enumerate(labels)
                   if all(p not in coords or coords[p] % (p**e) == a for p, (e, a) in c['coords'].items()))
        require(not any(mask & (1 << i) and set(c['coords']) <= set(coords) for i, c in enumerate(labels)),
                'Incoming source supported on actual old survivors')
        states[(mask, 0)] += mass
    return states


def clipped_row(cells, mask, ending, delta):
    require(0 < delta < 1, 'Legal prescribed full-Haar clipping threshold')
    bad = [bool(mask & c['matches'] & ending) for c in cells]
    alpha = sum((c['mass'] for c, b in zip(cells, bad) if b), F(0))
    theta = min(alpha, delta)
    row = [c['mass'] * (F(0) if alpha <= delta else (alpha-delta)/(alpha*(1-delta)))
           if b else c['mass']/(1-theta) for c, b in zip(cells, bad)]
    beta = max(F(0), alpha-delta)/(1-delta)
    require(sum(row) == 1 and sum(w for w, b in zip(row, bad) if b) == beta, 'Normalized physical row and exact bad mass')
    return bad, row, alpha, beta


def run(labels, incoming, primes, thresholds, enumeration=False):
    """Validate a complete increasing-prime exposure window, then compile it.

    Incoming rows use one common old-coordinate domain, strictly before the
    nonempty stage list. Every original coordinate through the final stage
    must be old or scheduled. Later coordinates remain unexposed. Integer
    old residues are interpreted modulo each full original coordinate height.
    All masses and thresholds are exact integers/Fractions, never floats.
    """
    labels, incoming, primes = tuple(labels), tuple(incoming), tuple(primes)
    for label in labels:
        validate_label(label)
    require(len({c['modulus'] for c in labels}) == len(labels), 'Distinct original moduli')
    require(bool(primes) and all(type(p) is int and p > 2 and is_prime(p) for p in primes), 'Stages are a nonempty sequence of actual odd primes')
    require(all(p < q for p, q in zip(primes, primes[1:])), 'Stages are strictly increasing and contain no repetitions')
    require(bool(incoming), 'Incoming source has an explicit old-coordinate domain')
    require(all(isinstance(row, (tuple, list)) and len(row) == 2 and isinstance(row[0], dict) for row in incoming), 'Incoming source rows are coordinate-dictionary/mass pairs')
    old = set(incoming[0][0])
    require(all(set(coords) == old for coords, _ in incoming), 'All incoming source rows have the same old-coordinate domain')
    require(all(type(p) is int and p > 2 and is_prime(p) for p in old), 'Old coordinates are actual odd primes')
    require(not old.intersection(primes), 'A previously exposed old coordinate cannot be processed again')
    require(all(p < primes[0] for p in old), 'Every old coordinate precedes every scheduled stage')
    required = {p for label in labels for p in label['coords'] if p <= primes[-1]}
    require(required <= old.union(primes), 'Every original coordinate through the final stage is old or explicitly scheduled')
    require(all(type(x) is int for coords, _ in incoming for x in coords.values()), 'Old full-coordinate residues are integers')
    require(all(type(mass) is int or isinstance(mass, F) for _, mass in incoming), 'Incoming masses are exact integers or Fractions')
    require(all(mass >= 0 for _, mass in incoming), 'Incoming source masses are nonnegative')
    require(isinstance(thresholds, dict) and set(thresholds) == set(primes), 'There is exactly one fixed threshold for every scheduled stage')
    require(all((type(delta) is int or isinstance(delta, F)) and 0 < delta < 1 for delta in thresholds.values()), 'Fixed thresholds are exact rationals in (0,1)')
    initial_mass = sum(w for _, w in incoming)
    states = initialize(labels, incoming)
    stages = []
    for step, p in enumerate(primes):
        cells = atom_cells(p, labels) if enumeration else prefix_cells(p, labels)
        ending = sum(1 << i for i, c in enumerate(labels) if max(c['coords']) == p)
        future = sum(1 << i for i, c in enumerate(labels) if max(c['coords']) > p)
        updated = defaultdict(F)
        physical_fee = first_hit = physical_moment = killed_moment = F(0)
        alpha_law = defaultdict(F)
        for (mask, events), mass in states.items():
            delta = thresholds[p]
            bad, row, alpha, beta = clipped_row(cells, mask, ending, delta)
            physical_fee += mass * beta
            physical_moment += mass * alpha**2
            alpha_law[alpha] += mass
            if events == 0:
                first_hit += mass * beta
                killed_moment += mass * alpha**2
            for c, b, w in zip(cells, bad, row):
                if w:
                    updated[(mask & c['matches'], events | ((1 << step) if b else 0))] += mass*w
        states = updated
        require(sum(states.values()) == initial_mass, 'Physical source mass never renormalized')
        survival = sum(w for (_, events), w in states.items() if events == 0)
        matched_future = {i: sum(w for (mask, events), w in states.items() if events == 0 and mask & (1 << i))
                          for i in range(len(labels)) if future & (1 << i)}
        stages.append(dict(prime=p, cells=len(cells), states=len(states), physical_fee=physical_fee,
                           first_hit=first_hit, physical_second_moment=physical_moment,
                           killed_second_moment=killed_moment, alpha_law=dict(alpha_law),
                           survival=survival, matched_future_killed_mass=matched_future))
    joint = defaultdict(F)
    for (_, events), mass in states.items():
        joint[events] += mass
    marginal = {p: sum(w for e, w in joint.items() if e & (1 << i)) for i, p in enumerate(primes)}
    pairs = {(p, q): sum(w for e, w in joint.items() if e & (1 << i) and e & (1 << j))
             for (i, p), (j, q) in combinations(enumerate(primes), 2)}
    survival = sum(w for (_, events), w in states.items() if events == 0)
    require(survival == initial_mass-sum(s['first_hit'] for s in stages), 'Exact same-chain first-hit identity')
    return dict(stages=stages, joint=dict(joint), marginal=marginal, pairs=pairs,
                survival=survival, physical_fee_sum=sum(marginal.values()),
                first_hit_sum=initial_mass-survival)


def compare(a, b):
    require({k: v for k, v in a.items() if k != 'stages'} == {k: v for k, v in b.items() if k != 'stages'},
            'Compressed compiler equals full atom chain, including complete stage-event law')
    for x, y in zip(a['stages'], b['stages']):
        require({k: v for k, v in x.items() if k not in ('states', 'cells')} ==
                {k: v for k, v in y.items() if k not in ('states', 'cells')}, 'All stage moments, first-hit fees and future-label killed masses agree')


def fixture334(kind):
    old = (3, 5, 7, 11, 13, 17, 19)
    labels = [original({p: (1, 1)}) for p in old]
    labels += [original({3: (1, 0), 23: (1, 0)}), original({5: (1, 0), 23: (1, 1)})]
    ys = (0, 1) if kind == 'A' else (2, 2)
    labels += [original({p: (1, 0), 23: (1, y), 29: (1, 0)}) for p, y in zip((7, 11), ys)]
    labels += [original({13: (1, 0), 29: (1, 0), 31: (1, 0)})]
    incoming = [({p: 0 for p in old}, F(1))]
    thresholds = {23: F(1, 23), 29: F(1, 58), 31: F(1, 62)}
    out = run(labels, incoming, (23, 29, 31), thresholds)
    compare(out, run(labels, incoming, (23, 29, 31), thresholds, enumeration=True))
    require(out['survival'] == (F(18564, 19459) if kind == 'A' else F(1057292, 1109163)), 'Existing334 exact final survivor mass reproduced')
    require(out['marginal'] == {23: F(1, 22), 29: F(1, 1254), 31: F(613, 1109163)}, 'Existing334 three physical marginal fees reproduced')
    require(out['pairs'] == {(23, 29): F(1, 1254) if kind == 'A' else F(0),
                             (23, 31): F(1, 76494) if kind == 'A' else F(1, 38918),
                             (29, 31): F(1, 76494)}, 'Existing334 all pair intersections reproduced')
    require(out['stages'][1]['survival'] == (F(21, 22) if kind == 'A' else F(598, 627)), 'Existing327 exact through29 mass reproduced')
    scaled = run(labels, [(incoming[0][0], F(3, 7))], (23, 29, 31), thresholds)
    require(scaled['survival'] == F(3, 7)*out['survival'] and
            scaled['joint'] == {e: F(3, 7)*m for e, m in out['joint'].items()}, 'An incoming killed source of mass3/7 remains unnormalized throughout')
    return dict(original_labels=labels, cell_audits=[audit_cells(p, labels) for p in thresholds], result=out)


def height_fixture(H, K, add_future=True, enumerate_small=False):
    require(H >= 1 and K >= 1, 'Positive original heights')
    R, Q = 5**H, 7**K
    labels = [original({3: (1, 1)}), original({3: (1, 0), 5: (H, 0)}),
              original({5: (H, 0), 7: (K, 0)}),
              original({3: (1, 0), 5: (H, 1), 7: (K, 1)})]
    if add_future:
        labels.append(original({3: (1, 0), 5: (H+1, R+2), 7: (K+1, Q+2), 11: (1, 0)}))
    incoming = [({3: 0}, F(1, 2)), ({3: 2}, F(1, 2))]
    thresholds = {5: F(1, 2*R), 7: F(1, 2*Q)}
    out = run(labels, incoming, (5, 7), thresholds)
    loss = F(1, 2*(2*R-1)) + F(1, (2*R-1)*(2*Q-1)) + F(1, 2*R*(2*Q-1))
    saving = F(1, 2*(2*R-1)*(2*Q-1))
    require(out['first_hit_sum'] == loss and out['physical_fee_sum']-loss == saving, 'Derived all-height formulas on this exact input')
    if add_future:
        require(out['stages'][-1]['matched_future_killed_mass'][4] == F(1, 35*Q*(2*R-1)), 'Unexposed11 label retains both deeper prefix tests without charging its11 condition')
        current = labels[:-1]
        def readout(r):
            return tuple(all(x % (p**e) == a for p, (e, a) in c['coords'].items()
                             for x in [0 if p == 3 else r if p == 5 else Q+2]) for c in current)
        require(readout(2) == readout(R+2), 'Current original-label observations miss the deeper future5 test')
        require(2 != (R+2) % (5*R) and (Q+2) % (7*Q) == Q+2, 'The omitted future label distinguishes these same-current-readout states')
    require([s['cells'] for s in out['stages']] == ([4, 4] if add_future else [3, 3]), 'Cell count independent of original heights in this family')
    audits = []
    if enumerate_small:
        compare(out, run(labels, incoming, (5, 7), thresholds, enumeration=True))
        audits = [audit_cells(p, labels) for p in thresholds]
    return dict(heights=(H, K), with_future_label=add_future, original_labels=labels,
                audits=audits, result=out, same_law_saving=saving)


def boundary_checks():
    # Exhaustive selected laminar targets: nesting, incompatible branches,
    # repeated targets from different original labels, no queried prefix,
    # and a zero-weight parent covered by all children.
    cases = ((), ((1, 0),), ((1, 0), (2, 0), (3, 9), (2, 1)),
             ((1, 0), (1, 1), (1, 2)), ((2, 0), (2, 0), (3, 9)))
    audits = []
    for targets in cases:
        labels = [original({3: target, 5: (i+1, 1)}) for i, target in enumerate(targets)]
        audits.append(audit_cells(3, labels))
    cells = [dict(mass=F(1), matches=1)]
    for mask, ending in ((0, 1), (1, 1)):
        _, row, alpha, beta = clipped_row(cells, mask, ending, F(1, 3))
        require(row == [F(1)] and alpha == beta == (1 if mask else 0), 'alpha=0 and alpha=1 retain exact physical and killed mass')
    return audits


def rejected_input_checks():
    """Regression inputs for ownership/order/source/CRT contract violations."""
    tests = []
    def reject(name, action, fragment):
        try:
            action()
        except ValueError as exc:
            require(fragment in str(exc), 'Input rejected for its stated contract violation: '+name)
            tests.append(dict(case=name, rejection=str(exc)))
        else:
            raise ValueError('Invalid input was silently accepted: '+name)
    label15 = original({3: (1, 0), 5: (1, 0)})
    label5 = original({5: (1, 0)})
    reject('reversed_stages', lambda: run([label15], [({}, F(1))], (5, 3), {3: F(1, 3), 5: F(1, 5)}), 'strictly increasing')
    reject('duplicate_stage', lambda: run([label15], [({3: 1}, F(1))], (5, 5), {5: F(1, 5)}), 'strictly increasing')
    reject('missing_lower_coordinate_of_current_label', lambda: run([label15], [({}, F(1))], (5,), {5: F(1, 5)}), 'through the final stage')
    reject('missing_earlier_ending_label', lambda: run([original({3: (1, 0)}), label5], [({}, F(1))], (5,), {5: F(1, 5)}), 'through the final stage')
    reject('missing_past_coordinate_of_future_label', lambda: run([original({3: (1, 0), 7: (1, 0)})], [({}, F(1))], (5,), {5: F(1, 5)}), 'through the final stage')
    reject('inconsistent_old_domains', lambda: run([label15], [({3: 1}, F(1, 2)), ({}, F(1, 2))], (5,), {5: F(1, 5)}), 'same old-coordinate domain')
    reject('unspecified_old_domain_on_empty_source', lambda: run([label5], [], (5,), {5: F(1, 5)}), 'explicit old-coordinate domain')
    reject('reexposed_old_coordinate', lambda: run([label5], [({5: 1}, F(1))], (5,), {5: F(1, 5)}), 'cannot be processed again')
    reject('later_coordinate_in_old_domain', lambda: run([label5], [({7: 1}, F(1))], (5,), {5: F(1, 5)}), 'precedes every scheduled stage')
    reject('unlisted_stage_threshold', lambda: run([label5], [({}, F(1))], (5,), {5: F(1, 5), 7: F(1, 7)}), 'exactly one fixed threshold')
    reject('floating_mass', lambda: run([label5], [({}, 1.0)], (5,), {5: F(1, 5)}), 'Incoming masses are exact')
    reject('floating_threshold', lambda: run([label5], [({}, F(1))], (5,), {5: 0.2}), 'exact rationals')
    reject('unit_threshold', lambda: run([label5], [({}, F(1))], (5,), {5: F(1)}), 'exact rationals')
    reject('zero_threshold', lambda: run([label5], [({}, F(1))], (5,), {5: F(0)}), 'exact rationals')
    reject('nonprime_stage', lambda: run([label5], [({}, F(1))], (9,), {9: F(1, 5)}), 'actual odd primes')
    reject('nonprime_original_coordinate', lambda: original({9: (1, 0)}), 'actual odd primes')
    reject('zero_original_exponent', lambda: original({3: (0, 0)}), 'positive integers')
    wrong_modulus = dict(label15, modulus=45)
    reject('mutated_original_modulus', lambda: run([wrong_modulus], [({3: 1}, F(1))], (5,), {5: F(1, 5)}), 'complete odd prime-power factorization')
    wrong_residue = dict(label15, residue=1)
    reject('mutated_original_residue', lambda: run([wrong_residue], [({3: 1}, F(1))], (5,), {5: F(1, 5)}), 'agrees with every stored')
    zero = run([original({3: (1, 0)}), label5], [({3: 0}, F(0))], (5,), {5: F(1, 5)})
    require(zero['survival'] == zero['physical_fee_sum'] == zero['first_hit_sum'] == 0 and not zero['joint'], 'Explicit-domain zero measure remains zero even at an old-forbidden zero-weight point')
    list_pair_label = dict(label15, coords={3: [1, 0], 5: [1, 0]})
    require(run([list_pair_label], [({3: 0}, F(1))], (5,), {5: F(1, 5)}) ==
            run([label15], [({3: 0}, F(1))], (5,), {5: F(1, 5)}), 'List-pair and tuple-pair coordinate representations produce identical transitions')
    require(audit_cells(5, [list_pair_label]) == audit_cells(5, [label15]), 'List-pair and tuple-pair coordinate audits agree')
    return tests


def full_threshold_checks():
    """The existing full-Haar formula permits every exact 0<delta<1."""
    thresholds = (F(4, 7), F(12, 23), F(5, 9), F(999, 1000))
    summaries = []
    for delta in thresholds:
        # Enumerate every bad subset on a full seven-point coordinate;
        # compare the compiler cell row with the literal density formula.
        # Near one, also use a1001-point row with alpha=1000/1001>delta.
        cases = [(7, mask) for mask in range(1 << 7)]
        if delta == F(999, 1000):
            cases.append((1001, (1 << 1000)-1))
        for size, bits in cases:
            cells = [dict(mass=F(1, size), matches=(bits >> i) & 1) for i in range(size)]
            bad, row, alpha, beta = clipped_row(cells, 1, 1, delta)
            count = bits.bit_count()
            require(alpha == F(count, size), 'Literal full-Haar bad fraction')
            for i, mass in enumerate(row):
                expected = (F(0) if count <= delta*size else (F(count, size)-delta)/((1-delta)*count)) if bad[i] else F(1, size)/(1-min(F(count, size), delta))
                require(mass == expected, 'Full admissible threshold row agrees pointwise with literal formula')
            require(sum(m for m, b in zip(row, bad) if not b) == 1-beta, 'Killed row and physical bad mass remain complements')
        summaries.append(dict(delta=delta, literal_rows_checked=len(cases)))
    return summaries


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = dict(scope='Exact same prescribed full-Haar physical/killed chains. Existing327/334 reproduced; arbitrary-height fixtures are tests, not new unrestricted noncoverage.',
                boundary_checks=boundary_checks(),
                rejected_inputs=rejected_input_checks(),
                full_threshold_checks=full_threshold_checks(),
                existing334={kind: fixture334(kind) for kind in ('A', 'B')},
                small_heights=[height_fixture(h, k, future, True) for h, k, future in ((1, 1, False), (1, 1, True), (2, 2, True), (3, 1, True))],
                high_heights=height_fixture(257, 263))
    text = json.dumps(encode(data), separators=(',', ':'), sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
