# Alternating Coefficients from a Pole at Minus One

## Abstract

A pole of order d+1 at minus one has alternating binomial coefficients of degree d.

**Theorem 1.1 (Pole order controls the alternating coefficient polynomial).**

$$\forall d,n\in\mathbb{N},\ [v^{n}](1+v)^{-(d+1)} = (-1)^{n}\cdot\operatorname{choose}(d+n,d).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AlternatingPoleCoefficients.alternating_pole_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative degree d, the formal expansion with a pole of order d+1 at minus one has nth coefficient equal to minus one to the nth power times choose(d+n,d). The binomial factor is a polynomial in n of degree d, so each increase in pole order raises the polynomial degree of the alternating coefficient envelope by one. This is the exact universal mechanism asserted by the source atom; its later row calculations are applications and numerical checks of this coefficient law.

Mathlib was searched before proving. The pinned library already provides the coefficients of the inverse power of one minus X as `PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose`, together with `PowerSeries.coeff_rescale`. The Lean theorem is therefore a declared thin honest wrapper: it rescales X by minus one and reads the resulting coefficient. No matching D5 theorem was found, and the wrapper adds the exact pole-at-minus-one formulation needed by the source atom without claiming a new library proof.

## References

- Truth anchor: `D5/S3/Analytic/AlternatingPoleCoefficients.alternating_pole_coefficients`
