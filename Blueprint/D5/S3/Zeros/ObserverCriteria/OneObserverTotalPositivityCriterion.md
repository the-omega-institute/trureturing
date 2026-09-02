# One-Observer Total-Positivity Criterion

## Abstract

A nonvanishing observer and the analytic PF-infinity bridges reduce total positivity to the shifted-square geometry of the zero set.

**Theorem 1.1 (One observer identifies RH, total nonnegativity, and PF infinity).**

$$\begin{aligned}\forall Xi: \mathbb{C} \to \mathbb{C}, t\in\mathbb{R},\\Xi\left(t\right) \neq 0 \land (\operatorname{TN}\left(Pt\right) \Leftrightarrow \operatorname{PFInfinity}\left(at\right)) \land\\(RH \Rightarrow \operatorname{PFInfinity}\left(at\right)) \land (\operatorname{PFInfinity}\left(at\right) \Rightarrow \forall z, Xi\left(z\right) = 0 \Rightarrow \exists x\in\mathbb{R}, 0 \leq x \land {z - t}^2 = x) \land\\(\forall z, Xi\left(z\right) = 0 \Rightarrow \operatorname{Im}\left(z\right) = 0) \Rightarrow RH \Rightarrow\\(RH \Leftrightarrow \operatorname{TN}\left(Pt\right)) \land (\operatorname{TN}\left(Pt\right) \Leftrightarrow \operatorname{PFInfinity}\left(at\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ObserverCriteria/OneObserverTotalPositivityCriterion.one_observer_total_positivity_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a real observer t at which xi is nonzero. Assume the supplied all-finite-minors predicate is equivalent to the supplied PF-infinity predicate, RH implies PF infinity, and PF infinity places every shifted square (z-t)^2 on the nonnegative real axis.

Taking real and imaginary parts of the square gives 2(Re z-t)Im z=0. If the first factor vanishes, nonnegativity of the square forces Im z=0; otherwise the product identity does so. The final supplied real-zero criterion therefore returns RH.

The PF-infinity representation and the minors equivalence are hypotheses because neither the repository nor pinned Mathlib packages those analytic bridges. The theorem proves the exact logical closure once they are available and does not reprove nearby frozen criteria.

## References

- Truth anchor: `D5/S3/Zeros/ObserverCriteria/OneObserverTotalPositivityCriterion.one_observer_total_positivity_criterion`
