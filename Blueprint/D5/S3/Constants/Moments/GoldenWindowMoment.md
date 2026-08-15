# Golden Window Moments

## Abstract

Every natural power moment of the translated golden window has a closed Binet form.

**Theorem 1.1 (The golden window power moments have a Binet form).**

$$\forall j \in \mathbb{N},\ \int_{-\varphi}^{\varphi^{-1}} (1+x)^j dx = \frac{\varphi^{j+1} - {-\varphi^{-1}}^{j+1}}{j+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/GoldenWindowMoment.golden_window_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by one sends the endpoints -phi and phi^-1 to -phi^-1 and phi. The pinned Mathlib theorem integral_pow then evaluates the translated monomial exactly.

The proof directly reuses intervalIntegral.integral_comp_add_right, integral_pow, Real.inv_goldenRatio, Real.one_sub_goldenConj, and Real.one_sub_goldenRatio. Repository search found no equal or stronger golden-window moment declaration.

This theorem formalizes only the window-moment sentence in source remark 27.187. It makes no claim about the surrounding reduction tower, the constants J1 or J2, or their numerical certificates.

## References

- Truth anchor: `D5/S3/Constants/Moments/GoldenWindowMoment.golden_window_moment`
