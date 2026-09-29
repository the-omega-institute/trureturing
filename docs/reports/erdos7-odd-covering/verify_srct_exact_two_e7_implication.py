"""Check the elementary class-preserving augmentation behind SRCT -> E7.

This is a bounded regression for the quantifier bridge.  It does not verify
SRCT's universal exact-two theorem.  The universal implication is the short
case split recorded in the companion audit note: a distinct odd family has
zero or one modulus-9 class, and adding the missing one or two classes keeps
coverage and produces the exact-two class.
"""

from itertools import combinations, product


def require(condition, message):
    if not condition:
        raise ValueError(message)


def augment_to_exact_two(family):
    count9 = sum(modulus == 9 for _, modulus in family)
    if count9 == 0:
        return tuple(family) + ((0, 9), (1, 9))
    if count9 == 1:
        residue = next(residue for residue, modulus in family if modulus == 9)
        return tuple(family) + (((residue + 1) % 9, 9),)
    raise ValueError("the input family is not distinct in its moduli")


def exact_two_class(family):
    moduli = [modulus for _, modulus in family]
    return (
        all(modulus > 1 and modulus % 2 == 1 for modulus in moduli)
        and moduli.count(9) == 2
        and all(moduli.count(modulus) <= 1 for modulus in set(moduli) if modulus != 9)
        and len(set(family)) == len(family)
    )


def distinct_odd_families(modulus_pool):
    for size in range(len(modulus_pool) + 1):
        for moduli in combinations(modulus_pool, size):
            for residues in product(*(range(modulus) for modulus in moduli)):
                yield tuple(zip(residues, moduli))


def main():
    # The pool is deliberately small: this checks the transformation, not the
    # universal covering theorem.  Every distinct choice of moduli and every
    # residue assignment in the pool is exercised.
    pool = (3, 5, 7, 9, 11)
    checked = 0
    for family in distinct_odd_families(pool):
        require(sum(modulus == 9 for _, modulus in family) <= 1,
                "input modulus-9 multiplicity")
        augmented = augment_to_exact_two(family)
        require(exact_two_class(augmented), "augmented class membership")
        require(set(family).issubset(augmented), "every original class retained")
        checked += 1
    require(checked == 23040, "exhaustive bounded-family count")
    print(f"PASS: {checked} distinct odd families")
    print("PASS: every bounded family augments to the exact-two-9 class")
    print("PASS: augmentation retains every original congruence class")
    print("Scope: bounded transformation checks; no covering obstruction proved")


if __name__ == "__main__":
    main()
