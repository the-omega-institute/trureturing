#!/usr/bin/env python3
"""Exact finite-prefix checks for the source-to-target digit transport.

This checker is deliberately finite. It verifies the two facts used by the
ordinary transport interface: every fixed shift table is injective and the
uniform average of the pullback of every target cylinder has the target Haar
mass. It does not prove the source survival theorem or an Erdos--Selfridge
statement.
"""

from itertools import product


def digits(value, prime, height):
    out = []
    for _ in range(height):
        out.append(value % prime)
        value //= prime
    assert value == 0
    return tuple(out)


def encode(value, source_prime, target_prime, height, shifts):
    result = 0
    place = 1
    for digit, shift in zip(digits(value, source_prime, height), shifts):
        result += (digit + shift) % target_prime * place
        place *= target_prime
    return result


def cylinder(value, prime, depth):
    return value % (prime ** depth)


def check_coordinate(source_prime, target_prime, height):
    source_size = source_prime ** height
    target_size = target_prime ** height
    shift_tables = tuple(product(range(target_prime), repeat=height))
    assert len(shift_tables) == target_size

    # Every fixed shift map is injective. The preimage of a target cylinder
    # is empty or one source cylinder at the same depth.
    for shifts in shift_tables:
        images = [encode(x, source_prime, target_prime, height, shifts)
                  for x in range(source_size)]
        assert len(set(images)) == source_size
        for depth in range(height + 1):
            for target_residue in range(target_prime ** depth):
                preimage = [x for x, image in enumerate(images)
                            if cylinder(image, target_prime, depth)
                            == target_residue]
                if not preimage:
                    continue
                assert len(preimage) == source_prime ** (height - depth)
                source_residue = preimage[0] % (source_prime ** depth)
                assert preimage == [x for x in range(source_size)
                                    if cylinder(x, source_prime, depth)
                                    == source_residue]

    # For each fixed source point the random image is uniform in the target
    # residue box. This is equivalent, by finite Fubini, to averaged pullback
    # equality for every target subset and hence every target cylinder.
    counts = [0] * target_size
    for shifts in shift_tables:
        for source in range(source_size):
            counts[encode(source, source_prime, target_prime, height, shifts)] += 1
    expected = len(shift_tables) * source_size // target_size
    assert expected * target_size == len(shift_tables) * source_size
    assert counts == [expected] * target_size
    return {
        'source_prime': source_prime,
        'target_prime': target_prime,
        'height': height,
        'shift_tables': len(shift_tables),
        'source_states': source_size,
        'target_states': target_size,
        'uniform_count_per_target_state': expected,
    }


def check_profile(source_primes, target_primes, heights):
    assert len(source_primes) == len(target_primes) == len(heights)
    assert all(p <= q for p, q in zip(source_primes, target_primes))
    rows = [check_coordinate(p, q, h)
            for p, q, h in zip(source_primes, target_primes, heights)]
    return {
        'source_primes': list(source_primes),
        'target_primes': list(target_primes),
        'heights': list(heights),
        'coordinate_checks': rows,
    }


def main():
    # The first profile is the missing-3 interface (3,5) -> (5,7); the
    # second is the missing-5 interface (3,5) -> (3,7). The third is the
    # existing identity/one-coordinate transport used by Chapters 31 and 70.
    profiles = [
        check_profile((3, 5), (5, 7), (2, 1)),
        check_profile((3, 5), (3, 7), (2, 1)),
        check_profile((3, 5, 7), (3, 5, 11), (1, 1, 1)),
    ]
    assert all(row['coordinate_checks'] for row in profiles)
    print('PASS: %d finite transport profiles; fixed-map prefix injectivity and '
          'uniform target pullback checked exactly.' % len(profiles))


if __name__ == '__main__':
    main()
