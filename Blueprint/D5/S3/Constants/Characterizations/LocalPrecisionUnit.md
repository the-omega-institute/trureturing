# The P-Adic Local Precision Unit

## Abstract

The normalized p-adic precision equation has log p as its unique real unit.

**Theorem 1.1 (Normalized p-adic precision has one logarithmic unit).**

$$\forall p \in \mathbb{N}, p \text{ prime},\\(((e^{-\operatorname{log}\left(p\right)} = \left\lVert (p: \mathbb{Q}_{p}) \right\rVert \land \left\lVert (p: \mathbb{Q}_{p}) \right\rVert = p^{-1}) \land (\forall ell \in \mathbb{R}, (e^{-ell} = \left\lVert (p: \mathbb{Q}_{p}) \right\rVert \land \left\lVert (p: \mathbb{Q}_{p}) \right\rVert = p^{-1}) \Rightarrow ell = \operatorname{log}\left(p\right))) \land\\(\forall s \in \mathbb{C}, p^{-s} = e^{-s \operatorname{log}\left(p\right)})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Characterizations/LocalPrecisionUnit.local_precision_unit_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural parameter p is required to be prime because it indexes the p-adic field. Its embedded p-adic norm is exactly p inverse under Mathlib's checked normalization. The theorem first states that log p satisfies the full two-equality equation, then separately states that every real value satisfying that equation equals log p. These are the existence and uniqueness halves of the source's word unique.

A candidate real number represents only the source evaluation ell_p(p), rather than an otherwise unconstrained whole length function. Injectivity of the real exponential identifies this candidate with log p. Finally, the free exponent is quantified over the complex analytic domain, where the standard complex-power definition gives p to the negative s as exp of negative s times log p.

## References

- Truth anchor: `D5/S3/Constants/Characterizations/LocalPrecisionUnit.local_precision_unit_unique`
