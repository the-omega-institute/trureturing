#!/usr/bin/env python3
"""Exact finite-tail cofactor matching under literal local covering premises.

The general API takes (p, H, prime_root) and labels (e, m, root, tail_residue).
Each label denotes one whole prefix cylinder modulo p**(e-1); (e,m) must
be unique and gcd(p,m)=1. It certifies each non-prime root's entire finite
tail by a disjoint minimal-prefix antichain, without enumerating p**(H-1).
The returned matching keeps original input indices and has a common tail.

The HSW fixtures use the complete source height 22 and its literal normal
and closing families. They are selected private old-coordinate states,
not an exhaustive check of every private old state. The source is an odd
cover with repeated modulus 11, not an Erdős #7 counterexample. Only its
3-bearing labels need distinct numerical moduli for this local lemma.
General unbounded-height conclusions are ordinary proofs in the report;
these exact checks are not Lean verification or a noncoverage theorem.
Only the sibling hsw11_family.py and the Python standard library are used.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt, prod
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
COFACTORS = (5, 7, 13, 17, 19)
HEIGHT = 22


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def integer(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(name + ' must be an integer >= ' + str(minimum))


def prime_integer(p):
    integer(p, 'p', 2)
    if any(p % d == 0 for d in range(2, isqrt(p)+1)):
        raise ValueError('p must be prime')


def validate_local(p, height, prime_root, labels):
    """Return immutable, validated original labels, preserving their order."""
    prime_integer(p)
    integer(height, 'height', 1)
    integer(prime_root, 'prime_root')
    if prime_root >= p:
        raise ValueError('prime_root is outside the p roots')
    out = []
    seen = set()
    for label in labels:
        if not isinstance(label, (tuple, list)) or len(label) != 4:
            raise ValueError('label must be (e,m,root,tail_residue)')
        e, m, root, residue = label
        integer(e, 'exponent', 1)
        integer(m, 'cofactor', 1)
        integer(root, 'root')
        integer(residue, 'tail_residue')
        if e > height:
            raise ValueError('exponent exceeds the complete finite height')
        if gcd(m, p) != 1:
            raise ValueError('cofactor is not p-free')
        if root >= p or root == prime_root:
            raise ValueError('label root is outside the non-prime roots')
        if e == 1 and m == 1:
            raise ValueError('the original prime label cannot be reused')
        if residue >= p**(e-1):
            raise ValueError('tail residue is outside its prefix period')
        if (e, m) in seen:
            raise ValueError('duplicate numerical modulus (e,m)')
        seen.add((e, m))
        out.append(tuple(label))
    return tuple(out)


def minimal_prefix_antichain(p, prefixes):
    """Exact union of p-adic cylinders as disjoint shortest input prefixes."""
    kept = []
    for depth, residue in sorted(set(prefixes)):
        if not any(residue % (p**d) == a for d, a in kept):
            kept.append((depth, residue))
    return tuple(kept)


def prefix_union_mass(p, prefixes):
    return sum((F(1, p**depth) for depth, _ in
                minimal_prefix_antichain(p, prefixes)), F(0))


def trie_union_mass(p, prefixes):
    """Independent finite tree calculation; never expand absent branches."""
    trie = {}
    for depth, residue in prefixes:
        node = trie
        stopped = False
        for level in range(depth):
            if 'terminal' in node:
                stopped = True
                break
            node = node.setdefault((residue // p**level) % p, {})
        if not stopped:
            node.clear()
            node['terminal'] = True

    def mass(node):
        if 'terminal' in node:
            return F(1)
        return sum((mass(child)/p for child in node.values()), F(0))

    return mass(trie)


def augmenting_matching(roots, neighbors):
    """A second matching method, independent of the prefix greedy route."""
    owner = {}

    def augment(root, visited):
        for cofactor in sorted(neighbors[root]):
            if cofactor in visited:
                continue
            visited.add(cofactor)
            if cofactor not in owner or augment(owner[cofactor], visited):
                owner[cofactor] = root
                return True
        return False

    for root in roots:
        if not augment(root, set()):
            raise ArithmeticError('matching failed under local cover premises')
    return {root: m for m, root in owner.items()}


def all_hall_subsets(roots, neighbors):
    """Independent exhaustive Hall check, used only on the small fixtures."""
    count = 0
    for size in range(1, len(roots)+1):
        for subset in combinations(roots, size):
            union = set().union(*(neighbors[r] for r in subset))
            require(len(union) >= size, 'a Hall subset is deficient')
            count += 1
    return count


def greedy_common_tail(p, height, prime_root, labels):
    """Select original labels with distinct nontrivial m on one common tail.

    This helper assumes validate_local and complete root-tail coverage have
    already succeeded. At each depth, used cofactors plus the pure column
    block at most k+1 children while k<p-1 roots have been matched.
    """
    roots = tuple(r for r in range(p) if r != prime_root)
    matched = {}
    used = set()
    by_depth = [[] for _ in range(height)]
    for index, (e, m, root, residue) in enumerate(labels):
        by_depth[e-1].append(index)

    def append_matches(depth, tail):
        for index in by_depth[depth]:
            e, m, root, residue = labels[index]
            if residue != tail or root in matched:
                continue
            require(m > 1 and m not in used,
                    'the selected child contains a used or pure new label')
            matched[root] = index
            used.add(m)

    tail = 0
    depth = 0
    append_matches(0, tail)
    while len(matched) < len(roots) and depth < height-1:
        next_depth = depth+1
        period = p**depth
        blocked = set()
        for index in by_depth[next_depth]:
            _, m, _, residue = labels[index]
            if (m == 1 or m in used) and residue % period == tail:
                blocked.add(residue // period)
        require(len(blocked) <= len(matched)+1 < p,
                'used/pure child budget is not strict')
        child = next(digit for digit in range(p) if digit not in blocked)
        tail += child*period
        depth = next_depth
        append_matches(depth, tail)
    require(len(matched) == p-1, 'a root remained unmatched at the final leaf')
    require(len(used) == p-1 and 1 not in used, 'cofactors are not distinct nonunits')
    for root, index in matched.items():
        e, m, literal_root, residue = labels[index]
        require(root == literal_root and tail % (p**(e-1)) == residue,
                'returned common tail misses an original witness')
    return dict(tail=tail, depth=depth, period=p**depth,
                tail_mass=F(1, p**depth),
                matching_indices={root: matched[root] for root in roots})


def analyze_local(p, height, prime_root, input_labels):
    """Validate full local premises and return literal common-tail witnesses."""
    labels = validate_local(p, height, prime_root, input_labels)
    roots = tuple(r for r in range(p) if r != prime_root)
    antichains = {}
    neighbors = {r: set() for r in roots}
    raw_mass = {r: F(0) for r in roots}
    for r in roots:
        prefixes = [(e-1, a) for e, _, root, a in labels if root == r]
        antichains[r] = minimal_prefix_antichain(p, prefixes)
        if prefix_union_mass(p, prefixes) != 1:
            raise ValueError('a non-prime root does not cover the entire finite tail')
        require(trie_union_mass(p, prefixes) == 1,
                'independent prefix-union algorithms disagree')
    for e, m, root, _ in labels:
        raw_mass[root] += F(1, p**(e-1))
        if m > 1:
            neighbors[root].add(m)
    require(all(mass >= 1 for mass in raw_mass.values()), 'tail union exceeds raw mass')
    hall_matching = augmenting_matching(roots, neighbors)
    greedy = greedy_common_tail(p, height, prime_root, labels)
    require(greedy['tail_mass'] >= F(1, p**(height-1)), 'finite-tail mass bound failed')
    tail_neighbors = {r: set() for r in roots}
    for e, m, r, residue in labels:
        if m > 1 and greedy['tail'] % p**(e-1) == residue:
            tail_neighbors[r].add(m)
    at_tail_matching = augmenting_matching(roots, tail_neighbors)
    return dict(labels=labels, roots=roots, antichains=antichains,
                neighbors=neighbors, hall_matching=hall_matching,
                raw_mass=raw_mass, common_tail=greedy,
                tail_neighbors=tail_neighbors, at_tail_matching=at_tail_matching)


def finite_gap_checks():
    count = 0
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        for height in range(1, 65):
            a = sum((F(1, p**(e-1)) for e in range(2, height+1)), F(0))
            b = sum((F(1, p**(e-1)) for e in range(1, height+1)), F(0))
            require(a == (1-F(1, p**(height-1)))/(p-1), 'pure column sum')
            require(b == (p-F(1, p**(height-1)))/(p-1), 'cofactor column sum')
            for s in range(1, p):
                gap = s-a-(s-1)*b
                require(gap == F(p-1-s, p-1)+F(s, (p-1)*p**(height-1)),
                        'finite-height Hall identity')
                require(gap >= F(1, p**(height-1)) > 0, 'finite-height Hall gap')
                count += 1
    return count


def invalid_input_checks():
    good = [(1, 5, 1, 0), (1, 7, 2, 0)]
    invalid = [
        (3, 1, 0, good+[(1, 5, 2, 0)]),
        (3, 1, 0, good[:1]),
        (3, 1, 0, [(1, 1, 1, 0), good[1]]),
        (3, 1, 0, [(1, 5, 1, 1), good[1]]),
        (3, 1, 0, [(1, 6, 1, 0), good[1]]),
        (3, 1, 0, [(1, 5, 0, 0), good[1]]),
        (3, 1, 0, [(2, 5, 1, 0), good[1]]),
        (4, 1, 0, good),
        (3, 0, 0, good),
        (3, 1, 3, good),
        (3, 1, 0, [(True, 5, 1, 0), good[1]]),
        (3, 1, 0, [(1, 5, 1), good[1]]),
    ]
    for case in invalid:
        try:
            analyze_local(*case)
        except ValueError:
            continue
        raise ArithmeticError('invalid local API input was accepted')
    return len(invalid)


def translated_even_fixture():
    original = ((0, 2), (0, 3), (1, 4), (5, 6), (7, 12))
    count = hall_count = 0
    for shift in range(12):
        cover = [((a+shift) % d, d) for a, d in original]
        require(all(any(z % d == a for a, d in cover) for z in range(12)),
                'translated finite cover lost coverage')
        for p, height, cofactor_period in ((2, 2, 3), (3, 1, 4)):
            prime_root = next(a for a, d in cover if d == p)
            private = [x for x in range(cofactor_period)
                       if all(x % d != a for a, d in cover if d % p)]
            for x in private:
                labels = []
                for a, d in cover:
                    if d % p or d == p:
                        continue
                    e, m = 0, d
                    while m % p == 0:
                        e, m = e+1, m//p
                    if x % m == a % m:
                        r = a % p
                        labels.append((e, m, r, ((a-r)//p) % p**(e-1)))
                result = analyze_local(p, height, prime_root, labels)
                hall_count += all_hall_subsets(result['roots'], result['neighbors'])
                hall_count += all_hall_subsets(result['roots'], result['tail_neighbors'])
                count += 1
    return dict(local_states=count, exact_hall_subset_checks=hall_count,
                scope='even local-premise fixture; not an odd-cover assertion')


def recursive_matching_exists(roots, neighbors, used=frozenset()):
    """Independent tiny-fixture search, separate from augmenting paths."""
    if not roots:
        return True
    root, *remaining = roots
    return any(recursive_matching_exists(remaining, neighbors, used | {m})
               for m in neighbors[root] if m not in used)


def sharp_local_configuration(p, height):
    """Literal numeric cofactor version of the one-good-leaf local family."""
    cofactors = [q for q in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31) if q != p]
    require(len(cofactors) >= p-1, 'insufficient fixture cofactor primes')
    labels = [(1, cofactors[r-1], r, 0) for r in range(1, p-1)]
    for depth in range(1, height):
        for r in range(1, p-1):
            labels.append((depth+1, cofactors[r-1], p-1, r*p**(depth-1)-1))
        labels.append((depth+1, 1, p-1, (p-1)*p**(depth-1)-1))
    labels.append((height, cofactors[p-2], p-1, p**(height-1)-1))
    return labels


def sharp_local_checks():
    examples = []
    tail_checks = comparable_checks = 0
    for p in (2, 3, 5, 7):
        for height in range(1, 5):
            labels = sharp_local_configuration(p, height)
            result = analyze_local(p, height, 0, labels)
            for i, (e, m, r, a) in enumerate(labels):
                for ee, mm, rr, aa in labels[i+1:]:
                    modulus, other = p**e*m, p**ee*mm
                    if modulus % other != 0 and other % modulus != 0:
                        continue
                    require(r != rr or (a-aa) % p**(min(e, ee)-1) != 0,
                            'comparable sharp-fixture original labels overlap')
                    comparable_checks += 1
            good = []
            for tail in range(p**(height-1)):
                neighbors = {r: set() for r in range(1, p)}
                for e, m, r, residue in labels:
                    if m > 1 and tail % p**(e-1) == residue:
                        neighbors[r].add(m)
                if recursive_matching_exists(tuple(range(1, p)), neighbors):
                    good.append(tail)
                tail_checks += 1
            require(good == [p**(height-1)-1], 'sharp fixture has the wrong good-tail set')
            require(result['common_tail']['tail'] == good[0], 'greedy misses the unique good tail')
            require(result['common_tail']['tail_mass'] == F(1, p**(height-1)),
                    'sharp fixture does not attain the finite-height mass bound')
            examples.append(dict(p=p, height=height, label_count=len(labels),
                                 unique_good_tail=good[0], good_mass=F(1, p**(height-1))))
    return dict(scope='sharp for local prefix-cover premises; not a lex-min odd whole cover',
                examples=examples, exact_leaf_checks=tail_checks,
                comparable_label_disjointness_checks=comparable_checks)


def load_constructor():
    path = Path(__file__).resolve().with_name('hsw11_family.py')
    spec = importlib.util.spec_from_file_location('literal_hsw_matching_source', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_hsw_source(family):
    require(family['only_repeated_modulus'] == 11, 'source repetition changed')
    require(family['nonpure_roots'] == [0, 1, 2, 3], 'source root carrier changed')
    supports = set()
    for row in family['normal_families']:
        require(23 not in row['primes'], 'normal source has a closing factor')
        if 3 not in row['primes']:
            continue
        key = tuple(row['primes'])
        require(key not in supports, '3-bearing numerical family is duplicated')
        supports.add(key)
        require(row['digits']['3'] == (1 if key == (3,) else 2),
                'another original 3-bearing label meets the prime root')
        for q in row['primes']:
            require(row['exponent_ranges'][str(q)] ==
                    ([1, 1] if q == 11 else [1, HEIGHT]),
                    'complete original height interval changed')
    require((3,) in supports, 'the original prime class is missing')
    closing = [row for row in family['closing_families'] if row['prime'] == 3]
    require(len(closing) == 1 and closing[0]['exponent_range'] == [1, HEIGHT]
            and closing[0]['modulus'] == '23*p^j' and closing[0]['p_residue'] == 0
            and closing[0]['q_residue'] == 'j', 'literal 3-closing family changed')


def private_mask_witnesses(family):
    patterns = []
    for root in range(4):
        patterns.append([
            tuple((COFACTORS.index(q), row['digits'][str(q)])
                  for q in row['primes'] if q != 11)
            for row in family['normal_families'] if 3 not in row['primes']
            and (11 not in row['primes'] or row['digits']['11'] == root)])
    counts, witnesses = Counter(), {}
    for digits in product(*(range(1, q) for q in COFACTORS)):
        mask = sum((not any(all(digits[k] == digit for k, digit in pattern)
                            for pattern in patterns[root])) << root for root in range(4))
        counts[mask] += 1
        witnesses.setdefault(mask, digits)
    require(sum(counts.values()) == 82944, 'cofactor digit carrier changed')
    return counts, witnesses


def literal_active_three_labels(module, family, coordinates, heights):
    """All source 3-bearing labels active on these fixed cofactor coordinates."""
    labels, originals = [], []
    for row in family['normal_families']:
        if 3 not in row['primes']:
            continue
        compatible = True
        for q in row['primes']:
            if q == 3:
                continue
            period = q if q == 11 else q**heights[q]
            residue = row['digits'][str(q)] * (1 if q == 11 else q**(heights[q]-1))
            if coordinates[q] % period != residue:
                compatible = False
                break
        if not compatible:
            continue
        for e in range(1, HEIGHT+1):
            original = module.instantiate_normal(row, {**heights, 3: e})
            a, d = original['residue'], original['modulus']
            if d == 3:
                require(a == 1, 'the omitted original prime class is not 1 mod3')
                continue
            m = d//3**e
            root = a % 3
            label = (e, m, root, ((a-root)//3) % 3**(e-1))
            require(all(a % (q if q == 11 else q**heights[q]) ==
                        coordinates[q] % (q if q == 11 else q**heights[q])
                        for q in row['primes'] if q != 3), 'literal cofactor membership')
            labels.append(label)
            originals.append(original)
    j = coordinates[23]
    a, d = module.crt_pair(0, 3**j, j, 23)
    labels.append((j, 23, 0, 0))
    originals.append(dict(family='closing-3', height=j, residue=a, modulus=d))
    require(len({item['modulus'] for item in originals}) == len(originals),
            'actual active 3-bearing numerical moduli repeat')
    return labels, originals


def hsw_fixture_checks():
    module = load_constructor()
    family = module.build_family()
    validate_hsw_source(family)
    counts, witnesses = private_mask_witnesses(family)
    cases = label_count = hall_checks = literal_checks = 0
    depth_counts = Counter()
    samples = []
    for mask, digits in sorted(witnesses.items()):
        for root11 in range(4):
            if not mask & (1 << root11):
                continue
            for j in range(1, HEIGHT+1):
                profiles = sorted(set((tuple([1]*5), tuple([j]*5),
                                       tuple(1+k % j for k in range(5)))))
                for profile in profiles:
                    heights = dict(zip(COFACTORS, profile))
                    coordinates = {q: digit*q**(heights[q]-1)
                                   for q, digit in zip(COFACTORS, digits)}
                    coordinates.update({3: 1, 11: root11, 23: j})
                    private_check = module.active_classes(coordinates, family)
                    require(len(private_check) == 1 and private_check[0]['modulus'] == 3
                            and private_check[0]['residue'] == 1,
                            'selected old coordinate is not private for A3')
                    labels, originals = literal_active_three_labels(
                        module, family, coordinates, heights)
                    result = analyze_local(3, HEIGHT, 1, labels)
                    hall_checks += all_hall_subsets(result['roots'], result['neighbors'])
                    hall_checks += all_hall_subsets(result['roots'], result['tail_neighbors'])
                    matched_originals = []
                    for root3, index in result['common_tail']['matching_indices'].items():
                        original = originals[index]
                        a, d = original['residue'], original['modulus']
                        e, m, _, _ = labels[index]
                        require((root3+3*result['common_tail']['tail']-a) % 3**e == 0,
                                'common tail misses the actual original 3-primary residue')
                        old_cofactor, old_period = module.crt_coordinates(
                            {q: coordinates[q] for q in module.ALL_PRIMES if q != 3},
                            {q: q if q in (11, 23) else q**HEIGHT
                             for q in module.ALL_PRIMES if q != 3})
                        require(old_period % m == 0 and (old_cofactor-a) % m == 0,
                                'actual original cofactor misses the common old point')
                        literal_checks += 1
                        matched_originals.append(dict(root=root3, exponent=e, cofactor=m,
                                                       **original))
                    if j == HEIGHT and profile == tuple(1+k % j for k in range(5)):
                        samples.append(dict(mask=mask, root11=root11, closing_digit=j,
                                            cofactor_digits=list(digits), heights=list(profile),
                                            tail=result['common_tail']['tail'],
                                            tail_depth=result['common_tail']['depth'],
                                            original_witnesses=matched_originals))
                    cases += 1
                    label_count += len(labels)
                    depth_counts[result['common_tail']['depth']] += 1
    return dict(scope='selected private old states; complete 3-height and literal local tails',
                source='HSW arXiv:2104.00602v1 Theorem 4.2 and Figures 18--22',
                original_height=HEIGHT, full_tail_period=3**(HEIGHT-1),
                only_repeated_original_modulus=11, mask_counts=dict(sorted(counts.items())),
                cases=cases, literal_active_labels_checked=label_count,
                exact_hall_subset_checks=hall_checks, matched_literal_AP_checks=literal_checks,
                common_tail_depth_counts=dict(sorted(depth_counts.items())),
                endpoint_mixed_height_examples=samples)


def json_default(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    result = dict(exact_gap_identities=finite_gap_checks(),
                  invalid_inputs_rejected=invalid_input_checks(),
                  translated_even_fixture=translated_even_fixture(),
                  sharp_local_fixtures=sharp_local_checks(),
                  hsw=hsw_fixture_checks(),
                  conclusion='local finite-tail certificates; unrestricted Erdős #7 remains unresolved',
                  verification='exact standard-library arithmetic, not Lean verification')
    print(json.dumps(result, sort_keys=True, indent=2, default=json_default))


if __name__ == '__main__':
    main()
