# Positivity Transfer from a Form Core

## Abstract

A continuous real form that is nonnegative on a form core is nonnegative on its domain.

**Theorem 1.1 (Nonnegativity on a form core extends to the full domain).**

$$\forall D, C, q, C \subseteq D, q: D \to \mathbb{R}, \operatorname{Continuous}\left(q\right) \land \operatorname{IsFormCore}\left(D, C\right) \land (\forall f \in C, 0 \leq q(f)) \Rightarrow \forall f \in D, 0 \leq q(f).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Forms/FormCorePositivityTransfer.nonnegative_of_formCore` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be a real normed linear domain, let C be a form-norm dense subset of D, and let q from D to the reals be continuous for that norm. If q is nonnegative at every point of C, then it is nonnegative throughout D.

Continuity makes the inverse image of the closed nonnegative real ray a closed subset of D. That subset contains the dense core C, so it must contain every point of D.

## References

- Truth anchor: `D5/S3/Analytic/Forms/FormCorePositivityTransfer.nonnegative_of_formCore`
