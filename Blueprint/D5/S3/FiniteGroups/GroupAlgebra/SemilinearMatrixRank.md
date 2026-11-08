# Semilinear Matrix Rank

## Abstract

Covariant Galois symmetry and rank over the original division ring.

The generic mechanism takes an arbitrary division ring D, an arbitrary unital ring C, a finite index type I with decidable equality, a left D-module U, and a unital homomorphism theta from Matrix I I C to End D U. Their universes are independent. No commutativity, nontriviality or simplicity of C, no injectivity of theta, and no C-module or scalar tower on U are assumed.

**Definition 1.1 (The original-D corner).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.corner`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a chosen i0 in I, the corner is the D-submodule range of theta(E_i0_i0). All operators are D-linear because the action lands in End D U.

**Definition 1.2 (Corner coordinates and reconstruction).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.cornerEquiv`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.cornerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map sends x to the coordinates theta(E_i0_i)x in the chosen corner. The inverse sends s to sum_i theta(E_i_i0)s_i. Products E_i_i0 E_i0_i = E_i_i and sum_i E_i_i = 1 prove reconstruction. The reverse product vanishes for different indices and equals E_i0_i0 on the diagonal; that idempotent fixes its range. Both maps are D-linear, giving U equivalent to I copies of the corner. This adapts Mathlib's Morita matrix coordinate mechanism by Yunzhou Xie and Jujian Zhang (Apache 2.0), retaining the independent scalar ring D.

**Theorem 1.3 (Exact dimension identity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.finrank_eq_card_mul_corner`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.finrank_eq_card_mul_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If U is finite dimensional over D, finrank D U equals card I times the D-rank of the corner. The equivalence and the finite product dimension formula prove this identity. The zero module is included.

**Theorem 1.4 (Divisibility from matrix units).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_dvd_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_dvd_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty I and finite-dimensional U, card I divides finrank D U. The witness is the rank of a chosen corner. This helper is used by the actual covariant Galois client below.

**Theorem 1.5 (Positive original-D multiplicity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_rank`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If U is also nontrivial, there is a natural number r greater than zero with finrank D U = card I times r. Zero multiplicity would contradict positivity of the dimension of a nontrivial finite module over a division ring.

For the live client let F/k be finite Galois and A an arbitrary unital F-algebra with a compatible k-algebra structure, scalar tower, multiplicative action of Gamma = Gal(F/k), and semilinearity over F. The rings A and its fixed algebra C may be noncommutative or trivial. Let U be a left module over another arbitrary division ring D. Supply actual coefficient operators a : A to End D U as a unital ring homomorphism and actual group operators tau : Gamma to End D U as a monoid homomorphism, satisfying tau(g)*a(x) = a(g acting on x)*tau(g). No algebra structure on U is added.

**Definition 1.6 (Actual covariant skew representation).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.skewRepresentation`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.skewRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's liftNCRingHom constructs the skew representation from a, tau and covariance. On the single term with coefficient x at g, it is a(x)*tau(g). Multiplication in End D U is composition, so the right operator acts first.

**Definition 1.7 (Transport to ordinary matrices).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.matrixAction`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.matrixAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The already proved trace-dual skewMatrixEquiv points from the skew algebra to ordinary Matrix I I C for a chosen k-basis of F. Composing the actual skew representation with its inverse produces the unital matrix action on U. Thus the matrix units are actual D-linear operators; no matrix action or descent equivalence is assumed.

**Theorem 1.8 (Galois rank divisibility).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_galois_dvd_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_galois_dvd_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite-dimensional U, Nat.card Gamma divides finrank D U. Apply the generic corner theorem to the constructed matrix action using finBasis k F, then use card Gamma = finrank k F. In particular this conclusion includes U = 0 and uses the original D throughout.

**Theorem 1.9 (Positive Galois multiplicity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_galois_rank`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_galois_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If U is nontrivial and finite dimensional over D, there exists r in the natural numbers with r > 0 and finrank D U = Nat.card Gamma times r. The generic positive corner result is applied to the same actual matrix action. No ordinary-field rank substitution or Schur-index cancellation occurs.

This supplies a rank ingredient for normalized Frobenius representation theory. Constructing the relevant center action and its Galois identification, Hall complement, Skolem implementation and original-D isotypic passage for the full normalized theorem remains outside this unit. The result is a classical structural synthesis and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_dvd_finrank`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.card_galois_dvd_finrank`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.corner`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.cornerEquiv`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_galois_rank`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.exists_pos_rank`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.finrank_eq_card_mul_corner`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.matrixAction`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank.skewRepresentation`
- Dependency: [D5/S3/Factorization/Galois/TraceDualSkewMatrix](../../Factorization/Galois/TraceDualSkewMatrix.md)
