# Cyclic Carry Three-Cocycle

## Abstract

A cyclic sum recovers the parameter of an explicit carry three-cocycle and vanishes on every two-cochain coboundary.

For positive n, write a.val for the least nonnegative representative of a in ZMod n. Set carry(b,c) = floor((b.val + c.val)/n) and w(t,a,b,c) = t * a * carry(b,c) in ZMod n. Raising exp(2πi/n) to the least nonnegative representative of w gives equation (2.13) of David E. Evans and Terry Gannon, Reconstruction and Local Extensions for Twisted Group Doubles, and Permutation Orbifolds, arXiv:1804.11145v1.

**Theorem 1.1 (Normalization at the identity).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The representative vanishes whenever any of its three arguments is zero.

**Theorem 1.2 (The three-cocycle identity).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_cocycle`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the trivial action, the inhomogeneous differential of w vanishes. After expansion, it reduces to the equality of the two total carries obtained by parenthesizing a sum of three residues.

**Theorem 1.3 (Summation recovers the parameter).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.sum_w`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.sum_w` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n greater than one, summing w(t,1,b,1) over b gives t. Only the residue n minus one has carry(b,1) equal to one.

**Theorem 1.4 (Cohomologous carry representatives have equal parameters).**

Lean statement: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.difference_is_coboundary_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.difference_is_coboundary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n greater than one, the difference of the representatives with parameters t and u is the coboundary of a ZMod n-valued two-cochain exactly when t = u. Translation by one cancels the two pairs of terms in the coboundary sum for every two-cochain with trivial action, even with arbitrary abelian coefficients. Equal parameters give the zero coboundary.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.difference_is_coboundary_iff`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.sum_w`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_cocycle`
- Truth anchor: `D5/S3/FiniteGroups/Cyclic/CyclicCarryThreeCocycle.w_normalized`
- Dependency: [D5/S1/Deficit/Cocycles/AdditiveCarryCocycle](../../../S1/Deficit/Cocycles/AdditiveCarryCocycle.md)
