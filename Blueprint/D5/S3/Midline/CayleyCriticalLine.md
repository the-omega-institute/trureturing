# Cayley Ratio and the Critical Line

## Abstract

The scalar Cayley ratio has unit modulus exactly on the critical line.

**Theorem 1.1 (Unit circle corresponds to the critical line).**

$$\forall s\in\mathbb{C},\ \lvert\frac{s - 1}{s}\rvert = 1 \Leftrightarrow \Re(s) = \frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/CayleyCriticalLine.cayley_ratio_norm_one_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof treats the totalized division value at zero separately. For a nonzero parameter, the squared norm defect is (1 - 2 Re(s)) divided by the norm square of s.

Thus unit modulus is equivalent to vanishing horizontal displacement from real part one half.

Two-arm cancellation and imbalance.

Let p > 1 and sigma be real, and let u and v be complex numbers of norm one. Set a = p^(−sigma) and b = p^(−(1−sigma)), with real powers and real scalar multiplication on C. The reverse triangle inequality abs_norm_sub_norm_le, applied to au and −bv, gives |a−b| ≤ ‖au+bv‖. This bound is sharp: choosing v = −u gives equality for every sigma.

Both coefficients are strictly positive. If ‖au+bv‖ = 0, the lower bound forces a = b. Real.rpow_right_inj for the base p then gives −sigma = −(1−sigma), hence sigma = 1/2. The original equation becomes a(u+v) = 0, so v = −u. Conversely these two conditions make the sum zero. If sigma differs from 1/2, the same injectivity shows |a−b| > 0, uniformly over the two unit phases. No primality assumption on p is needed; a prime shell is a specialization.

Reflected Cayley modes and branching depth.

Write c(rho) = cayleyRatio(rho) = (rho−1)/rho. Algebra gives c(1−rho) = c(rho)⁻¹, including the totalized division values. Now assume rho is neither zero nor one and Re(rho) differs from 1/2. Then r = ‖c(rho)‖ is positive, and cayley_ratio_norm_one_iff_critical_line gives r ≠ 1. Since ‖c(1−rho)‖ = r⁻¹, one member of the pair has norm strictly greater than one. Thus q = max(‖c(rho)‖, ‖c(1−rho)‖) > 1. The reflection here is rho ↦ 1−rho, without complex conjugation.

For an integer branching base k ≥ 2 and any real threshold M, set T = max(1, log_q(max(1,M))) and ell = ceil_N(log_k T) + 1, where log_b is Real.logb and ceil_N is the natural ceiling. Nat.le_ceil gives log_k T < ell; Real.logb_lt_iff_lt_rpow gives T < k^ell. Applying the same logarithm equivalence at base q gives M < q^(k^ell) = max(‖c(rho)^(k^ell)‖, ‖c(1−rho)^(k^ell)‖). The equality uses norm_pow and monotonicity of natural powers on nonnegative reals. This explicit depth includes M ≤ 1; k = 2 is repeated squaring.

These are consequences of the scalar norm and power identities under the stated hypotheses. They supply no assertion that a spectral parameter with these properties exists, nor any bound on cancellation in a sum of distinct modes.

## References

- Truth anchor: `D5/S3/Midline/CayleyCriticalLine.cayley_ratio_norm_one_iff_critical_line`
