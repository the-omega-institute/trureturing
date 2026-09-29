#!/usr/bin/env python3
"""Exhaustive finite product certificate for the missing-anchor transport.

For a finite product of source p-adic digit boxes and target q-adic digit
boxes (p <= q), this checks the interface needed by one common transported
submeasure.  Every mixed target cylinder is pulled back by each fixed shift
table to one mixed source cylinder or the empty set.  Averaging over all shift
tables is checked atomwise: every target atom has the same number of
(shift, source-atom) preimages.  The latter identity is exactly the linear
step used to transport all marginal-cap inequalities.

This is a finite arithmetic certificate.  It does not assert the source
survival theorem, root orientation, attachment gluing, or unrestricted
Erdos--Selfridge #7.
"""

from fractions import Fraction
from itertools import combinations, product
from math import prod


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def digits(value, prime, height):
    out = []
    for _ in range(height):
        out.append(value % prime)
        value //= prime
    require(value == 0, "value exceeds digit box")
    return tuple(out)


def encode_coord(value, source_prime, target_prime, height, shifts):
    result = 0
    place = 1
    for digit, shift in zip(digits(value, source_prime, height), shifts):
        result += (digit + shift) % target_prime * place
        place *= target_prime
    return result


def encode(point, source_primes, target_primes, heights, shifts):
    return tuple(encode_coord(x, p, q, h, sig)
                 for x, p, q, h, sig in zip(
                     point, source_primes, target_primes, heights, shifts))


def boxes(primes, heights):
    return tuple(range(p ** h) for p, h in zip(primes, heights))


def all_shifts(target_primes, heights):
    rows = [product(range(q), repeat=h)
            for q, h in zip(target_primes, heights)]
    return tuple(product(*rows))


def target_labels(target_primes, heights):
    """All nonempty mixed cylinders, retaining their coordinate labels."""
    labels = []
    for size in range(1, len(target_primes) + 1):
        for coords in combinations(range(len(target_primes)), size):
            depth_choices = product(*(range(1, heights[i] + 1) for i in coords))
            for depths in depth_choices:
                residues = product(*(range(target_primes[i] ** e)
                                     for i, e in zip(coords, depths)))
                for residue_tuple in residues:
                    labels.append(tuple(zip(coords, depths, residue_tuple)))
    return tuple(labels)


def cylinder(point, primes, label):
    return all(point[i] % (primes[i] ** depth) == residue
               for i, depth, residue in label)


def pullback(point, source_primes, target_primes, heights, shifts, label):
    image = encode(point, source_primes, target_primes, heights, shifts)
    return cylinder(image, target_primes, label)


def source_cylinder_for_target(source_primes, target_primes, heights, shifts,
                               label):
    """Return source residue tuple or None for a target mixed cylinder."""
    source_residues = []
    for i, depth, target_residue in label:
        p, q = source_primes[i], target_primes[i]
        source_digits = digits(target_residue, q, depth)
        sig = shifts[i]
        allowed = []
        for digit, shift in zip(source_digits, sig):
            candidates = [d for d in range(p) if (d + shift) % q == digit]
            if len(candidates) > 1:
                raise AssertionError("digit map is not injective")
            if not candidates:
                return None
            allowed.append(candidates[0])
        source_residue = sum(d * p ** j for j, d in enumerate(allowed))
        source_residues.append((i, depth, source_residue))
    return tuple(source_residues)


def label_modulus(primes, label):
    return prod(primes[i] ** depth for i, depth, _ in label)


def check_profile(source_primes, target_primes, heights, family):
    require(len(source_primes) == len(target_primes) == len(heights),
            "profile dimensions")
    require(all(p <= q for p, q in zip(source_primes, target_primes)),
            "coordinatewise p <= q")
    source_boxes = boxes(source_primes, heights)
    target_boxes = boxes(target_primes, heights)
    source_points = tuple(product(*source_boxes))
    target_points = tuple(product(*target_boxes))
    shifts = all_shifts(target_primes, heights)
    labels = target_labels(target_primes, heights)

    # Every target cylinder at every mixed depth has the claimed pullback.
    cylinder_checks = 0
    for sigma in shifts:
        for label in labels:
            expected = source_cylinder_for_target(
                source_primes, target_primes, heights, sigma, label)
            actual = tuple(x for x in source_points
                           if pullback(x, source_primes, target_primes,
                                       heights, sigma, label))
            if expected is None:
                require(not actual, "empty target cylinder has a preimage")
            else:
                expected_points = tuple(
                    x for x in source_points if cylinder(x, source_primes, expected))
                require(actual == expected_points,
                        "mixed target cylinder is not one source cylinder")
            cylinder_checks += 1

        image = tuple(encode(x, source_primes, target_primes, heights, sigma)
                      for x in source_points)
        require(len(set(image)) == len(source_points),
                "fixed product shift map is not injective")

    # A distinct-modulus original family, with mixed labels and both depths.
    require(len({label_modulus(target_primes, x) for x in family}) == len(family),
            "fixture family must retain distinct original moduli")
    family_checks = 0
    for sigma in shifts:
        source_labels = [source_cylinder_for_target(
            source_primes, target_primes, heights, sigma, label)
                         for label in family]
        for x in source_points:
            y = encode(x, source_primes, target_primes, heights, sigma)
            target_vector = tuple(cylinder(y, target_primes, label)
                                  for label in family)
            source_vector = tuple(
                False if label is None else cylinder(x, source_primes, label)
                for label in source_labels)
            require(target_vector == source_vector,
                    "original event vector is not transported exactly")
            family_checks += 1

    # Atomwise finite-Fubini identity.  For every target atom y,
    # E_sigma H_source(F_sigma^{-1}{y}) = H_target({y}).
    counts = {y: 0 for y in target_points}
    for sigma in shifts:
        for x in source_points:
            counts[encode(x, source_primes, target_primes, heights, sigma)] += 1
    expected = len(shifts) * Fraction(len(source_points), len(target_points))
    require(expected.denominator == 1, "finite atom coefficient is integral")
    require(all(count == expected.numerator for count in counts.values()),
            "target atoms do not have uniform averaged pullback")

    # The coefficient identity implies the marginal-cap inequality for any
    # nonnegative source rows with atomwise bound mu_sigma(x) <= alpha/|X|.
    # Check it for several exact symbolic alpha values; the coefficient is
    # independent of alpha, so these are regression witnesses for the same
    # rational identity rather than separately optimized measures.
    cap_checks = []
    for alpha in (Fraction(1), Fraction(3, 2), Fraction(2)):
        atom_cap = alpha / len(source_points)
        target_atom_cap = expected / len(shifts) * atom_cap
        require(target_atom_cap == alpha / len(target_points),
                "averaged atom cap does not equal target Haar cap")
        cap_checks.append(str(target_atom_cap))

    return {
        "source_primes": list(source_primes),
        "target_primes": list(target_primes),
        "heights": list(heights),
        "source_states": len(source_points),
        "target_states": len(target_points),
        "shift_tables": len(shifts),
        "mixed_cylinder_checks": cylinder_checks,
        "event_vector_checks": family_checks,
        "atom_preimage_count": expected.numerator,
        "target_atom_cap_examples": cap_checks,
        "family_moduli": [label_modulus(target_primes, x) for x in family],
    }


def main():
    profiles = []
    # Missing-3 interface; the family has moduli 25, 7, 35, 5.
    profiles.append(check_profile(
        (3, 5), (5, 7), (2, 1),
        (((0, 2, 7),), ((1, 1, 2),),
         ((0, 1, 1), (1, 1, 3)), ((0, 1, 4),))))
    # Missing-5 interface; keep the same source anchor and move only 5 -> 7.
    profiles.append(check_profile(
        (3, 5), (3, 7), (2, 1),
        (((0, 2, 4),), ((1, 1, 2),),
         ((0, 1, 1), (1, 1, 3)), ((0, 1, 2),))))
    # Dual missing-(3,5) anchor interface.
    profiles.append(check_profile(
        (3, 5), (7, 11), (2, 1),
        (((0, 2, 8),), ((1, 1, 2),),
         ((0, 1, 1), (1, 1, 3)), ((0, 1, 4),))))
    print({"status": "PASS", "profiles": profiles,
           "scope": "Finite product pullback, event-vector, and averaged-cap identities; source survival, root orientation, gluing, later-prime monotonicity, and unrestricted Erdos--Selfridge #7 remain open."})


if __name__ == "__main__":
    main()
