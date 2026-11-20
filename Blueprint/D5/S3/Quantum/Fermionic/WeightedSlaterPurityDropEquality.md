# Equality on the weighted affine fiber

## Abstract

Equality in a positive weighted binary fiber bound.

**Theorem 1.1 (Equality of the weighted product and its lower bound).**

Lean statement: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_product_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_product_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use a strictly positive probability law on the finite set of assignments. The mass of pivot bit one is positive and at most the mass of bit zero. Each row factor uses a positive bias at most one for bit one, and one for bit zero. The bound takes the smaller factor at every position. Strict increase at any one factor gives strict increase in the product at that assignment and then in the weighted sum. Equality requires bit one throughout the assignment space at each untied pivot and at each row whose factor at one is strictly below one.

**Theorem 1.2 (Equality on a parametrized affine fiber).**

Lean statement: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_affine_fiber_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_affine_fiber_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same normalized positive assignment weights and positive lower factors. The selected linear form takes value one on the fiber. The forms in the homogeneous constraint space take value zero there. A pivot or row form takes value one throughout the fiber exactly when its difference from the selected form belongs to the homogeneous constraint space.

**Theorem 1.3 (Equality for any basis of pivot columns).**

Lean statement: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_pivot_fiber_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_pivot_fiber_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same normalized positive assignment weights and positive lower factors. The pivot columns are linearly independent and span the column space. For a feasible right-hand side, each free assignment has exactly one pivot completion. With a one at the selected equation and zero at the other equations, equality holds exactly when every untied pivot unit row and every row with bias factor below one lies in the selected row's coset of the span of the other constraint rows.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_affine_fiber_eq_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_pivot_fiber_eq_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality.weighted_product_eq_iff`
