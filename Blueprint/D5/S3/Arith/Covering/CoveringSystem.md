# Covering systems and the reciprocal bound

## Abstract

A finite family of congruence classes that covers the integers has reciprocal moduli summing to at least one.

A covering system is a finite family of congruence classes whose union is all of the integers. Two further conditions carry the hypotheses under which covering systems are usually studied, distinctness of the moduli and oddness of every modulus; they are recorded here as the vocabulary in which those questions are stated, and the bound below does not assume them.

**Definition 1.1 (Covering systems).**

Lean statement: `D5/S3/Arith/Covering/CoveringSystem.IsCoveringSystem`

*Formalization.* `D5/S3/Arith/Covering/CoveringSystem.IsCoveringSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite set of pairs of naturals is a covering system when every modulus, the second entry, is at least one, and every integer is congruent to the first entry modulo the second for at least one pair. Coverage is stated over the integers, so negative integers are included, and the residue is not required to be reduced modulo the modulus.

**Definition 1.2 (Distinct moduli).**

Lean statement: `D5/S3/Arith/Covering/CoveringSystem.IsDistinct`

*Formalization.* `D5/S3/Arith/Covering/CoveringSystem.IsDistinct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every modulus is at least two and distinct members of the system carry distinct moduli.

**Definition 1.3 (Odd moduli).**

Lean statement: `D5/S3/Arith/Covering/CoveringSystem.AllOdd`

*Formalization.* `D5/S3/Arith/Covering/CoveringSystem.AllOdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every modulus of the system is odd.

**Theorem 1.4 (The reciprocal bound).**

Lean statement: `D5/S3/Arith/Covering/CoveringSystem.sum_reciprocal_moduli_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/CoveringSystem.sum_reciprocal_moduli_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a covering system the sum of the reciprocals of the moduli is at least one. Take a common period, namely a multiple of every modulus, and count the naturals below it. The class of one member meets that range in exactly the period divided by its modulus, because the modulus divides the period. Coverage makes the range the union of those intersections, so the period is at most the sum over the system of the period divided by each modulus. Dividing by the period gives the claim. Overlaps are permitted throughout, which is why the conclusion is an inequality and not an equality.

## References

- Truth anchor: `D5/S3/Arith/Covering/CoveringSystem.AllOdd`
- Truth anchor: `D5/S3/Arith/Covering/CoveringSystem.IsCoveringSystem`
- Truth anchor: `D5/S3/Arith/Covering/CoveringSystem.IsDistinct`
- Truth anchor: `D5/S3/Arith/Covering/CoveringSystem.sum_reciprocal_moduli_ge_one`
