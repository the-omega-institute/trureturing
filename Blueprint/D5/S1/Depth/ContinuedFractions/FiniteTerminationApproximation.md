# Finite Termination and Infinite Approximation

## Abstract

Rational reals terminate at a finite denominator; irrational errors stay positive at every finite level while their liminf is zero.

**Definition 1.1 (Nearest-integer approximation error).**

$$\forall q \in N, x \in R,\; \operatorname{integerApproximationError}\left(q, x\right) = \left\lVert q \cdot x - \operatorname{round}\left(q \cdot x\right) \right\rVert$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.integerApproximationError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural denominator q and real point x, this is the absolute distance from q times x to its nearest integer.

**Definition 1.2 (Finite approximation error).**

$$\forall Q \in N, x \in R,\; \operatorname{finiteApproximationError}\left(Q, x\right) = \operatorname{if}\left(0 < Q, \operatorname{min}\left(\left\{\operatorname{integerApproximationError}\left(q, x\right) \mid q \in \operatorname{Icc}\left(1, Q\right)\right\}\right), 0\right)$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.finiteApproximationError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a positive level Q this is the finite minimum over denominators from one through Q. The zero branch only totalizes the function at the single level excluded by the source minimum.

**Theorem 1.3 (Finite termination and infinite approximation).**

$$\forall x \in R,\; \left(x \in Q \Leftrightarrow \left(\exists Q \in N,\; 0 < Q \land \operatorname{finiteApproximationError}\left(Q, x\right) = 0\right)\right) \land \left(\left(\operatorname{Irrational}\left(x\right) \Rightarrow \left(\forall Q \in N,\; 0 < Q \Rightarrow 0 < \operatorname{finiteApproximationError}\left(Q, x\right)\right)\right) \land \operatorname{liminfAtTop}\left(\operatorname{finiteApproximationError}\left(Q, x\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.finite_termination_and_infinite_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational denominator makes one finite error exactly zero. Conversely, a zero error writes the real as an integer divided by a positive natural denominator.

For an irrational real, every candidate nearest-integer error is nonzero, so its attained finite minimum is strictly positive.

Dirichlet approximation bounds the level-Q minimum by one over Q plus one. Squeezing against nonnegativity proves convergence to zero for every real, which is stronger than the irrational-only liminf clause.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.finiteApproximationError`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.finite_termination_and_infinite_approximation`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.integerApproximationError`
