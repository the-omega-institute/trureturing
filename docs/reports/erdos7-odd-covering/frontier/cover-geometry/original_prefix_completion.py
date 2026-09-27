#!/usr/bin/env python3
"""Exact finite checks for original-label prefix completion.

Standard library only; suitable for python3 -I -S -O from any directory.
The default local example has 1243 distinct odd original moduli, current
prime 47, future prime 53 and 24 occupied current roots. It is a local
completion inside an irredundant NONCOVER. Additional finite comb checks
exercise the terminal-sibling height obstruction. A small noncover checks
the signed completion identity, including overlap and uncovered mass.

These are integer/Fraction checks of the specified finite inputs. The
ordinary proof supplies arbitrary-height statements. No Lean verification,
global covering contradiction or solution of Erdos problem 7 is claimed.
No files, certificates or external modules are read or written.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import comb, gcd
import argparse
import sys

sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def current_future_residue(p, q, root, future):
    """One CRT residue; future=None leaves the q coordinate unrestricted."""
    if future is None:
        return p, root
    return p * q, root + p * (((future - root) * pow(p, -1, q)) % q)


def local_completion(p, q, occupied_roots):
    require(is_prime(p) and p >= 7, 'Current prime must be at least 7; old primes are 3 and 5')
    require(is_prime(q) and q > p, 'Future prime must be larger than the current prime')
    require(1 <= occupied_roots <= p - 2, 'Root count must give a clip threshold strictly between zero and one')
    holes = (0,) + tuple(range(occupied_roots + 1, p))
    # Every tuple is an ORIGINAL label, even when its residual modulus repeats.
    labels = [(root, None) for root in range(1, occupied_roots + 1)]
    labels += [(root, future) for root in holes for future in range(q)]
    count = len(labels)
    rank = count - 1
    require(count == occupied_roots + (p - occupied_roots) * q,
            'Complete current and future original-label inventory')
    require(rank > 0, 'Every assigned old cofactor is nonunit')
    originals = []
    for j, (root, future) in enumerate(labels):
        old_cofactor = 3 ** j * 5 ** (rank - j)
        residual_modulus, residual_residue = current_future_residue(p, q, root, future)
        require(gcd(old_cofactor, residual_modulus) == 1, 'Coprime old and residual factors')
        modulus = old_cofactor * residual_modulus
        residue = old_cofactor * ((residual_residue * pow(old_cofactor, -1, residual_modulus)) % residual_modulus)
        require(modulus % 2 == 1 and modulus > 1 and 0 <= residue < modulus,
                'Legal odd original congruence class')
        require(residue % old_cofactor == 0 and residue % p == root,
                'Original CRT residue retains its old and current conditions')
        require(future is None or residue % q == future,
                'Original CRT residue retains its future condition')
        originals.append((modulus, residue))
    require(len({modulus for modulus, _ in originals}) == count,
            'All reconstructed ORIGINAL moduli are distinct')

    pairs = 0
    for j, (root, future) in enumerate(labels):
        for k in range(j):
            other_root, other_future = labels[k]
            # Opposite 3/5 valuation inequalities rule out both divisibilities,
            # including when one original modulus has an extra future prime.
            require(k < j and rank - k > rank - j,
                    'Full original moduli have incomparable old prime valuations')
            require(root != other_root or
                    (future is not None and other_future is not None and future != other_future),
                    'Literal current/future CRT conditions make original classes disjoint')
            pairs += 1

    current_by_root = defaultdict(int)
    future_by_atom = defaultdict(int)
    for root, future in labels:
        if future is None:
            current_by_root[root] += 1
        else:
            future_by_atom[root, future] += 1
    for root in range(p):
        for future in range(q):
            require(current_by_root[root] + future_by_atom[root, future] == 1,
                    'Every residual atom is covered exactly once at old zero')

    # All old conditions hold at zero modulo this ACTUAL common old period.
    # Construct a private CRT integer for every original class. The exact
    # single-coverage check above rules out all other labels at that point.
    old_period = 3 ** rank * 5 ** rank
    inverse_old = pow(old_period, -1, p * q)
    for (root, future), (modulus, residue) in zip(labels, originals):
        chosen_future = 0 if future is None else future
        _, residual = current_future_residue(p, q, root, chosen_future)
        private = old_period * ((residual * inverse_old) % (p * q))
        require(private % old_period == 0 and private % modulus == residue,
                'Actual original private-point CRT witness')
        require(current_by_root[root] + future_by_atom[root, chosen_future] == 1,
                'The private point meets exactly its assigned original class')

    alpha = F(occupied_roots, p)
    delta = F(occupied_roots, p - 1)
    beta = max(alpha - delta, F(0)) / (1 - delta)
    require(0 < alpha < delta < 1 and beta == 0, 'Zero current clipped bad charge')
    rows = []
    for root in range(p):
        occupancy = F(current_by_root[root], p)
        future_load = F(sum(future_by_atom[root, s] for s in range(q)), p * q)
        require(occupancy + future_load == F(1, p), 'Exact original-prefix completion equality')
        rows.append((occupancy, future_load))
    require(min(a for a, _ in rows) == 0 and max(f for _, f in rows) == F(1, p),
            'The min-occupancy lower bound is exactly zero')
    future_total = F((p - occupied_roots) * q, p * q)
    require(alpha + future_total == 1, 'Complete current/future residual partition')
    require(sum(comb(rank, j) ** 2 for j in range(rank + 1)) == comb(2 * rank, rank),
            'Exact middle-rank Vandermonde identity')
    # Every old cofactor exceeds one and has residue zero. Old coordinate one
    # therefore misses every label, proving this original family is a NONCOVER.
    require(all((3 ** j * 5 ** (rank - j)) > 1 for j in range(count)),
            'One old coordinate escapes every original class')
    print(f'PASS local completion: {count} original labels, {pairs} pairs, '
          f'{p*q} residual atoms, alpha={alpha}, delta={delta}, beta=0, '
          f'm1=0, F1_max=1/{p}')


def comb_completion(p, height):
    require(is_prime(p) and p >= 5, 'Comb prime must be odd and different from the old prime 3')
    require(height >= 1, 'Comb height must be positive')
    prefixes = [(e, digit * p ** (e - 1))
                for e in range(1, height) for digit in range(1, p)]
    prefixes += [(height, digit * p ** (height - 1)) for digit in range(p)]
    count = len(prefixes)
    require(count == (p - 1) * height + 1, 'Complete comb original-label inventory')
    originals = []
    for k, (depth, residue) in enumerate(prefixes, start=1):
        old_cofactor = 3 ** k
        current_modulus = p ** depth
        modulus = old_cofactor * current_modulus
        original_residue = old_cofactor * ((residue * pow(old_cofactor, -1, current_modulus)) % current_modulus)
        require(modulus % 2 == 1 and original_residue % old_cofactor == 0
                and original_residue % current_modulus == residue,
                'Comb original CRT class')
        originals.append((modulus, original_residue))
    require(len({modulus for modulus, _ in originals}) == count, 'Comb original moduli are distinct')
    for j, (depth, residue) in enumerate(prefixes):
        for other_depth, other_residue in prefixes[:j]:
            require((residue - other_residue) % (p ** min(depth, other_depth)) != 0,
                    'Current comb cylinders are pairwise disjoint')
    require(sum(F(1, p ** depth) for depth, _ in prefixes) == 1,
            'Disjoint finite current cylinders cover the entire current carrier')

    old_period = 3 ** count
    inverse_old = pow(old_period, -1, p ** height)
    for (depth, residue), (modulus, original_residue) in zip(prefixes, originals):
        private = old_period * ((residue * inverse_old) % (p ** height))
        require(private % modulus == original_residue, 'Original comb class has its private CRT point')
    # Exact old Haar strata: truncated v_3(x)=k. On each stratum the active
    # labels are precisely those with old exponent at most k. Their current
    # cylinders were checked disjoint, so their total mass decides coverage.
    strata_mass = F(0)
    full_fibre_mass = F(0)
    for k in range(count + 1):
        mass = F(2, 3 ** (k + 1)) if k < count else F(1, 3 ** count)
        strata_mass += mass
        covered_mass = sum((F(1, p ** depth) for depth, _ in prefixes[:k]), F(0))
        require((covered_mass == 1) == (k == count), 'Exact full-fibre predicate on every old Haar stratum')
        if covered_mass == 1:
            full_fibre_mass += mass
    require(strata_mass == 1 and full_fibre_mass == F(1, old_period),
            'Same-old-Haar full-fibre mass')

    siblings = defaultdict(dict)
    for k, (depth, residue) in enumerate(prefixes, start=1):
        parent_modulus = p ** (depth - 1)
        parent = residue % parent_modulus
        digit = residue // parent_modulus
        require(digit not in siblings[depth, parent], 'At most one comb original label at a current node')
        siblings[depth, parent][digit] = k
    terminal = [(depth, nodes) for (depth, _), nodes in siblings.items() if len(nodes) == p]
    require(len(terminal) == 1 and terminal[0][0] == height,
            'Exactly one complete direct sibling tuple, at the last depth')
    unweighted = sum((F(1, 3 ** max(nodes.values())) for _, nodes in terminal), F(0))
    discounted = sum((F(1, 3 ** max(nodes.values()) * p ** (depth - 1))
                      for depth, nodes in terminal), F(0))
    require(unweighted == full_fibre_mass and discounted / full_fibre_mass == F(1, p ** (height - 1)),
            'Sharp unweighted sibling budget and exact height discount loss')
    print(f'PASS comb: p={p}, H={height}, {count} original labels, '
          f'full_fibre_mass={full_fibre_mass}, discounted_ratio={discounted/full_fibre_mass}')


def signed_identity_noncover():
    """Atom enumeration checks the Haar identity with all slack types present.

    Old point zero activates the displayed original labels. There are no
    earlier-ending classes. This fibre is NOT fully covered; the uncovered
    term must be subtracted from the nonnegative incidence/excess terms.
    The data include e=0, distinct heights, incompatible prefixes, overlap
    inside the current union and future overcoverage outside it.
    """
    p, q, height = 7, 11, 2
    # (old cofactor, current depth, current residue); old residues are zero.
    current = ((1, 1, 1), (3, 2, 0))
    # (old cofactor, current depth, current residue, future residue).
    future = ((1, 0, 0, 0), (3, 1, 0, 0), (5, 1, 0, 1),
              (15, 1, 1, 0), (9, 2, 7, 2))
    moduli = [old * p ** e for old, e, _ in current]
    moduli += [old * p ** e * q for old, e, _, _ in future]
    require(len(set(moduli)) == len(moduli) and all(d > 1 and d % 2 == 1 for d in moduli),
            'Signed-identity example has legal distinct odd original moduli')
    p_height = p ** height
    bad = {y for y in range(p_height) if any(y % (p ** e) == a for _, e, a in current)}
    multiplicity = {(y, z): sum(y % (p ** e) == a and z == b for _, e, a, b in future)
                    for y in range(p_height) for z in range(q)}
    denominator = p_height * q
    failures_of_completion = 0
    positive_terms = [False, False, False]
    cases = 0
    for t in range(height + 1):
        for residue in range(p ** t):
            points = [y for y in range(p_height) if y % (p ** t) == residue]
            occupancy = F(sum(y in bad for y in points), p_height)
            load = sum((F(1, p ** max(e, t) * q) for _, e, a, _ in future
                        if (a - residue) % (p ** min(e, t)) == 0), F(0))
            enumerated_load = F(sum(multiplicity[y, z] for y in points for z in range(q)), denominator)
            require(load == enumerated_load, 'Residual original-label Haar formula matches full atom enumeration')
            incidence = F(sum(multiplicity[y, z] for y in points if y in bad for z in range(q)), denominator)
            excess = F(sum(max(multiplicity[y, z] - 1, 0)
                           for y in points if y not in bad for z in range(q)), denominator)
            uncovered = F(sum(multiplicity[y, z] == 0
                              for y in points if y not in bad for z in range(q)), denominator)
            require(load + occupancy - F(1, p ** t) == incidence + excess - uncovered,
                    'Exact signed completion identity with uncovered mass retained')
            if load + occupancy < F(1, p ** t):
                failures_of_completion += 1
            if t == 0:
                positive_terms = [incidence > 0, excess > 0, uncovered > 0]
            cases += 1
    require(all(positive_terms) and failures_of_completion > 0,
            'The noncover exercises incidence, overcoverage, uncovered mass and a failed cover-only bound')
    print(f'PASS signed identity: {cases} prefixes, e=0 retained; '
          'positive incidence, overcoverage and uncovered mass; cover-only bound fails as required')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--current-prime', type=int, default=47, help='Current prime >=7 (default: 47)')
    parser.add_argument('--future-prime', type=int, default=53, help='Future prime larger than current (default: 53)')
    parser.add_argument('--occupied-roots', type=int,
                        help='Occupied roots 1..r, with 1<=r<=p-2 (default: (p+1)//2)')
    parser.add_argument('--comb-prime', type=int, default=5, help='Comb current prime >=5 (default: 5)')
    parser.add_argument('--comb-heights', type=int, nargs='+', default=[1, 2, 3, 4, 5],
                        help='Positive finite comb heights (default: 1 2 3 4 5)')
    args = parser.parse_args()
    roots = args.occupied_roots if args.occupied_roots is not None else (args.current_prime + 1) // 2
    local_completion(args.current_prime, args.future_prime, roots)
    for height in args.comb_heights:
        comb_completion(args.comb_prime, height)
    signed_identity_noncover()
    print('PASS finite integer/Fraction checks only; all constructed families are noncovers; '
          'no Lean verification or unrestricted covering conclusion')


if __name__ == '__main__':
    main()
