# Finite Inverse-Poisson RH Criterion

## Abstract

Criticality, positive definiteness, and boundedness are equivalent for a finite inverse-Poisson window with explicit functional-equation reflection.

**Theorem 1.1 (Three equivalent finite-window conditions).**

$$\forall n \in \mathbb{N}, W \in \operatorname{FinitePoissonWindow}\left(n\right),\; \left(\operatorname{OnCriticalLine}\left(W\right) \Leftrightarrow \operatorname{PositiveDefinite}\left(\operatorname{inversePoissonSum}\left(W\right)\right)\right) \land \left(\operatorname{PositiveDefinite}\left(\operatorname{inversePoissonSum}\left(W\right)\right) \Leftrightarrow \operatorname{BoundedOnReal}\left(\operatorname{inversePoissonSum}\left(W\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion.finite_inverse_poisson_rh_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite window stores a displacement and ordinate for each term, together with a permutation that negates displacement while preserving ordinate. This makes the functional-equation pairing used by the reverse implication an explicit premise.

The critical-line implication writes the inverse-Poisson kernel as a finite Gram matrix. Positive semidefiniteness then bounds every value by the value at zero through a two-by-two determinant.

For the converse, a maximal positive growth rate is normalized out. Bolzano-Weierstrass supplies arbitrarily late simultaneous returns of all finite phases to one, so the nonempty maximal-rate block cannot cancel while the original sum remains bounded.

The reflection premise is necessary: without it, a one-term window with displacement one and ordinate zero gives exp(-|t|), which is positive definite and bounded but is not on the critical line. The formal module also checks the empty case and a reflected two-point off-line unbounded witness.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion.finite_inverse_poisson_rh_criterion`
