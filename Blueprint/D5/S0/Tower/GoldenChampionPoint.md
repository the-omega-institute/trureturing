# Golden Champion Point Identity

## Abstract

The proposed golden-tower champion point has equivalent radical and negative-power forms.

**Theorem 1.1 (The champion point forms agree).**

$$\frac{13}{2} - 4\varphi = \frac{(\sqrt{5} - 2)^{2}}{2} \land \frac{(\sqrt{5} - 2)^{2}}{2} = \frac{\varphi^{-6}}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenChampionPoint.golden_champion_point_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-root identity follows from the library definition of the golden ratio and the exact square of sqrt(5). For the negative power, the library's golden quadratic identity gives phi cubed as 2 + sqrt(5), while sqrt(5) - 2 is its reciprocal. Squaring the reciprocal pair gives the exponent-six form.

Pinned Mathlib provides Real.goldenRatio_sq, Real.goldenRatio_ne_zero, Real.sq_sqrt, zpow_neg, and the definitional closed form of Real.goldenRatio. No declaration packaging this three-form equality was found.

This is an honest partial closure of the champion closed-form clause only. The constant-arm realization, the maximizing orbit, the global extremality argument, survivor-set analysis, finite orbit enumerations, golden-gap substitution dynamics, higher-order substitution claims, and the boundary outside the finite-type regime remain unresolved.

## References

- Truth anchor: `D5/S0/Tower/GoldenChampionPoint.golden_champion_point_identity`
