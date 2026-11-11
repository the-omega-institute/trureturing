# SixRowHead

## Abstract

For every nonnegative labelled fifteen-tuple, one nonnegative unit vector in five coordinates and one bijection of the fifteen K6 edges attain at least the Euclidean norm. Labels, rather than numerical values, are sorted, so ties remain distinct. The six final edges are assigned only after the same vector is fixed. This is a head supplier for the APPT threshold programme; it does not settle that threshold.

For every nonnegative labelled fifteen-tuple, one nonnegative unit vector in five coordinates and one bijection of the fifteen K6 edges attain at least the Euclidean norm. Labels, rather than numerical values, are sorted, so ties remain distinct. The six final edges are assigned only after the same vector is fixed. This is a head supplier for the APPT threshold programme; it does not settle that threshold.

The supplied constructive derivation sorts the weights as M, four b entries, four c entries and six d entries. Write X for the sum of the b squares, Y for the sum of the c squares and Z for the sum of the d squares. When Y is positive, use L = sqrt(M² + X + Z), s = M/L and t = sqrt(X + Z)/L. Normalize the four entries b_i + s c_i to a unit vector q, then choose p = (s, t q). The Lean proof uses the equivalent normalized scalar parameters alpha = M/sqrt(X), k = Y/X and h = Z/Y.

The distinguished center edge receives M. The four remaining center edges receive the b entries, and the four edges from the distinguished leaf receive the c entries. The six d labels occupy the remaining edges by a single cyclic permutation selected at the fixed q. The four-coordinate estimate directly consumes FiveRowP2Star.star_product_bound. Monotonicity in the four-coordinate norm and the exact SixRowHeadScalar.recipe_bound supply the full fifteen-entry Euclidean lower bound. When Y vanishes, all c and d entries vanish; normalization of the five center weights gives equality, with the all-zero case handled separately.

**Definition 1.1 (edgeAt).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeAt`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def edgeAt : Fin 15 → Edge 6

**Definition 1.2 (edgeEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def edgeEquiv : Fin 15 ≃ Edge 6

**Definition 1.3 (headValue).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.headValue`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.headValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def headValue (a : Fin 15 → ℝ) (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15) : ℝ

**Theorem 1.4 (head exists).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.head_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.head_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem head_exists (a : Fin 15 → ℝ) (ha : ∀ i,0 ≤ a i) : ∃ (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15), (∀ i,0 ≤ p i) ∧ (∑ i,(p i)^2=1) ∧ Real.sqrt (∑ i,(a i)^2) ≤ headValue a p π

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeAt`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.headValue`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.head_exists`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star](../FiveRowP2Star.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar](SixRowHeadScalar.md)
