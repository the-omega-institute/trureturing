# Integer binary readout in arbitrary abelian groups

## Abstract

Integer binary readout in arbitrary abelian groups.

**Theorem 1.1 (read top difference).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_top_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_top_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite integer word splitting and periodicity control the difference of high readouts. Induction on the changed bit proves the addition-of-a-power identity under the explicit successor-index bound. Geometric upper tails are read with integer coefficients; no division is performed in the group.

**Theorem 1.2 (read add power).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_add_power`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_add_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite integer word splitting and periodicity control the difference of high readouts. Induction on the changed bit proves the addition-of-a-power identity under the explicit successor-index bound. Geometric upper tails are read with integer coefficients; no division is performed in the group.

Finite words and a defined successor endpoint. For a group A and f:N->A, the shared read d f m is the sum of digit(m,i) acting by integer scalar multiplication on f(i), for 0<=i<d. This module works with the sealed additive-helper delta, retaining its original read and digit declarations. The theorem read_add_power explicitly requires j+1<d and 0<=m<m+2^j<2^d; j is a natural, so its nonnegativity is built into the type. No out-of-range successor is hidden in a total function.

Transport instead of division in a group. If f(i)=2^(i-j-1) f(j+1) for j<i<d, then read(m+2^j)-read(m)=(1-2 epsilon) f(j)+epsilon f(j+1), where epsilon=digit(m,j). The source proof inducts on j. At j=0, it splits off the low bit and uses the exact integer geometric word sum for the tail; the two Boolean alternatives are proved by Euclidean division. At j+1, adding the even power preserves parity and shifts the quotient by 2^j. Every quotient belongs to Z, and all actions on A are integer scalar actions, so the statement retains arbitrary torsion.

The actual high-row consumer. The additional word split and periodicity lemmas show that words differing by an integral multiple of 2^n have the same first n digits. Thus their d=n+3 readout difference is exactly the difference of their top three-bit readouts. HighRows applies this to the actual affine digits, while InternalRows and LowRows apply read_add_power to selected upper-to-upper changes. The generic helpers are consumed by these physical all-r proofs, rather than retained as separate certificates.

The binary lemma is uniform in the word length and target abelian group. Integer Euclidean division supplies its coefficients; finite controls from the ordinary mathematical review are not premises.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_add_power`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout.read_top_difference`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Binary](../MersenneExceptional19PermutationStabilizer/Binary.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Family](Family.md)
