# Odd Fiber Pole Certificate

## Abstract

An odd-capacity fiber amplitude has a nonzero normalized value of absolute value one at v equals minus one.

**Theorem 1.1 (Odd capacity gives a normalized simple-pole coefficient).**

$$c\text{ odd},\quad r_{m,c}(v)=\frac{v^{m}(1-v^{c})}{1-v^{2}},\quad \operatorname{reg}_{v=-1}(r)=(-1)^{m},\quad \Vert \operatorname{reg}_{v=-1}(r) \Vert=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/OddFiberPoleCertificate.odd_fiber_pole_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row amplitude is v^m(1-v^c)/(1-v^2). Away from v equals plus or minus one, multiplying by v+1 cancels exactly one denominator factor and leaves v^m times the finite geometric sum.

For odd c, Mathlib's neg_one_geom_sum evaluates the geometric factor to one. The normalized value is therefore (-1)^m and has absolute value one, so the factor at minus one is not removable.

The existing FiberCapacityDivisibility theorem already covers the even capacity criterion and is not duplicated. AlternatingPoleCoefficients concerns a different higher-order power-series coefficient problem.

## References

- Truth anchor: `D5/S1/Recurrence/OddFiberPoleCertificate.odd_fiber_pole_certificate`
