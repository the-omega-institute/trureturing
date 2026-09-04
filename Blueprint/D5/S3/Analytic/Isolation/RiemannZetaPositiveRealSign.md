# Riemann Zeta on the Positive Real Axis

## Abstract

Riemann zeta is real on the positive real axis away from one, negative below one, and positive above one.

**Theorem 1.1 (Riemann zeta has the expected positive-real sign).**

$$\forall x\in \mathbb{R}, (0 < x \land x \neq 1) \Rightarrow \operatorname{Im}(\operatorname{riemannZeta}(x)) = 0 \land ((x < 1 \land \Re(\operatorname{riemannZeta}(x)) < 0) \lor (1 < x \land 0 < \Re(\operatorname{riemannZeta}(x)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem supplies the variable positive-real zeta sign input in the golden Euler germ extraction ladder of OACTC parts 580 and 581. It advances the boundary left open by the point-specific golden auxiliary nonvanishing theorem: every positive real argument other than one is now covered on both sides of one.

Below one, adjacent odd-even Dirichlet terms are paired. Every real pair is strictly positive, a derivative majorant gives local uniform convergence on positive real part, and the analytic identity principle identifies the paired sum with the eta factor times zeta. The eta factor is negative there, forcing zeta to be real and negative.

Above one, the positive Dirichlet series gives a positive real part and zero imaginary part directly. The separate public realness lemma records the common conclusion across both intervals.

The statement is confined to positive real arguments away from the pole at one. It does not establish O-5 or RH, a complex zero-free region, or an all-order extraction claim.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign`
- Narrative reference: [D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign](../EulerGerm/GoldenGermSecondOrderRealAxisSign.md)
- Narrative reference: [D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero](GoldenAuxiliaryZetaNonzero.md)
