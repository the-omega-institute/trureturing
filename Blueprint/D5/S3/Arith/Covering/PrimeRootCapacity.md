# Ordinary-Prime Root Capacity

## Abstract

In a distinct odd cover minimal in modulus sum at its class count, a fixed ordinary-prime root contains at most two original labels at any fixed top ternary height and modulo-5 root.

**Theorem 1.1 (Three originals force a cheaper cover).**

Lean statement: `D5/S3/Arith/Covering/PrimeRootCapacity.top_ordinary_prime_root_card_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeRootCapacity.top_ordinary_prime_root_card_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover every natural number with L congruence classes of pairwise distinct odd moduli greater than one. Suppose its modulus sum is minimal among all such covers with L classes. The competing covers have unrestricted prime heights. Fix any natural height h, put D = 3^h, and assume no original modulus is divisible by 3D.

Fix residues u, omega and b, and a prime p different from 3 and 5. At most two original indices have modulus divisible by both 5D and p, residue u modulo D, residue omega modulo 5, and residue b modulo p. The boundary h = 0 is included, where congruence modulo D is congruence modulo one. At h = 2 the selected group is the existing modulo-9 word and modulo-5 root group.

If three such indices existed, coprimality would make each selected modulus a positive multiple of 5Dp. Replace these three originals by moduli 3D, 15D and 3Dp. The three next ternary digits above u select the replacement row: digit zero uses modulus 3D; digit one retains the actual modulo-5 root through CRT; digit two retains the actual modulo-p root through CRT.

Every point of every removed congruence class lies in one replacement class. This uses the coarse residue conditions of that original and requires no common point of the complete removed classes. Retaining the complement and transporting the three new slots back to the original finite index type gives an actual cover with exactly L labels.

Oddness and the prime exclusions give p greater than 5. The three new moduli are distinct odd nonunits. Divisibility by 3D makes them fresh against every original modulus. Each new modulus is strictly smaller than its selected original. The removed sum is at least 15Dp and the replacement sum is 3D(6+p). This contradicts the full same-count minimum.

The conclusion is a literal prime-root capacity bound. It assumes no probability law, minimal class count, divisor closure or occurrence of modulus 3 or 9. It does not supply a weighted selection theorem, a strict global budget contradiction or nonexistence of all odd distinct covering systems.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrimeRootCapacity.top_ordinary_prime_root_card_le_two`
- Dependency: [D5/S3/Arith/Covering/FixedCollisionExceptions](FixedCollisionExceptions.md)
