# FIB Same-Parity Gap and Deficit Bounds

## Abstract

Four twenty-cycle gaps have an exact parity penalty, and a negative same-family deficit forces a strict cardinality bound.

**Definition 1.1 (A gap contributes its alternating independent-set penalty).**

Lean statement: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.gapPenalty`

*Formalization.* `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.gapPenalty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a gap g, remove its two endpoint centres and count the alternating positions that can remain in the corresponding path. The resulting contribution is floor((g-2)/2), represented by natural-number subtraction and division.

**Theorem 1.2 (The four-gap penalty is fixed by gap parities).**

Lean statement: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For four gaps at least two whose cyclic total is twenty, the sum of the four penalties is 6 minus half the sum of their parity bits. This is the arithmetic core of the twenty-gon carrier calculation and does not assume a choice of triangulation family.

**Theorem 1.3 (The maximal penalty is exactly the all-even case).**

Lean statement: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_eq_six_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_eq_six_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same twenty-cycle hypotheses, the carrier reaches six exactly when all four gaps are even. In the polygon application, this is the all-one-parity four-centre condition; mixed centre parity forces at least one unit of penalty.

**Theorem 1.4 (A negative same-family deficit gives a strict bound).**

Lean statement: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.same_family_strict_bound_of_negative_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.same_family_strict_bound_of_negative_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a same-family estimate gives 2(F-L) at most a negative deficit, then F is strictly below L. The three G terms are deliberately parameters, so the lemma can consume any three carrier bounds proved elsewhere while preserving the common-family quantifier.

Substituting h = 8464690, G₁ = 3784063, G₂ = G₃ = 2773974 and L = 69753940 gives the exact all-one-parity n=20 arithmetic implication. The finite capacity inequality and the stability refinement remain external combinatorial inputs; this declaration does not assert those counts.

The escape-audit registration for these declarations is unfinished and is disclosed in issue https://github.com/the-omega-institute/trureturing/issues/24755; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_eq_six_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.four_gap_penalty_sum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.gapPenalty`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FIBSameParityGapBound.same_family_strict_bound_of_negative_deficit`
