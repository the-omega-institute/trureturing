# Nonnegative vectors in the span of two integer witnesses

## Abstract

Two residue representatives decide feasibility within the span of two integer witnesses.

**Theorem 1.1 (The nearest two residue coefficients decide nonnegative feasibility).**

$$(\exists a, c, ab + c = t \land ap + cu \geq 0) \iff (qp + ru \geq 0) \lor ((q + 1)p + (r - b)u \geq 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NumericalSemigroup/TwoWitnessResidues.nonnegative_at_nearest_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p and u be integer-valued functions on an arbitrary index type. Assume p is nonnegative at each index. Let the degrees assigned to p and u be b and 1, with b a positive integer. Fix a nonnegative degree t and write t = bq + r with 0 ≤ r < b.

There exists a pair of integer coefficients a and c at degree t giving a nonnegative vector if and only if one of the two displayed candidates is nonnegative at every index. Both candidates satisfy the degree equation. Vector inequalities are componentwise.

At a fixed degree the vector is affine in c. At c = 0 its coordinates equal those of p scaled by t/b. Between zero and an admissible coefficient c of either sign, entrywise nonnegativity is preserved. The proof clears denominators in this interpolation. The candidates use the first eligible coefficient on each side of zero.

Nonnegativity of t is used at the interpolation endpoint. For b = 2, t = −5, p = 1 and u = 1 on a single coordinate, the nearest representatives give −2 and −3, while a = −6 and c = 7 gives 1.

## References

- Truth anchor: `D5/S3/Combinatorics/NumericalSemigroup/TwoWitnessResidues.nonnegative_at_nearest_residue`
