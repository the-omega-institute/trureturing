# The principal-log zeta tail

## Abstract

Exponential control and oriented height transport of the actual zeta logarithm tail.

Put q = pi squared divided by six minus one and C = q/(1-q). The shifted Dirichlet series and its square majorant give 0 <= q <= 3/4. For real part at least two, each summand gains the factor 2 to the power (2 minus the real part). Thus zeta stays in the open right half-plane, where its actual complex principal logarithm is analytic. Every integral below uses Lebesgue volume. This controls Littlewood's right boundary; the central RH sign E <= 0 remains unproved.

**Theorem 1.1 (The zeta image stays in the right half-plane).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.re_zeta_pos_of_two_le_re`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.re_zeta_pos_of_two_le_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s with real part at least two, Re zeta(s) is positive. The shifted-series bound supplies the strict margin. The principal-log and prime-tail proofs both consume this fact.

**Theorem 1.2 (Uniform exponential decay of the principal logarithm).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.norm_log_riemannZeta_le_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.norm_log_riemannZeta_le_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s with real part at least two, the norm of Log(zeta(s)) is at most C times 2 to the power (2 minus the real part of s). The power-series remainder bound for log(1+w), applied to w = zeta(s)-1, converts the shifted Dirichlet-series estimate into this bound with the stated C.

**Theorem 1.3 (Integrability of the actual complex tail).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_principal_log_riemannZeta_Ioi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_principal_log_riemannZeta_Ioi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every R >= 2 and every real height t, sigma mapped to Log(zeta(sigma+it)) is Bochner integrable over the open half-line sigma > R. Continuity supplies measurability, and the exponential bound supplies an integrable majorant.

**Theorem 1.4 (Integrability of the real logarithm of the zeta norm).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_log_norm_riemannZeta_Ioi`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_log_norm_riemannZeta_Ioi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the real part of the complex logarithm gives the actual real log of the zeta norm. Its tail is integrable for the same endpoints and every real height.

**Theorem 1.5 (An explicit absolute complex tail estimate).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_norm_principal_log_riemannZeta_Ioi_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_norm_principal_log_riemannZeta_Ioi_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of the norm of the principal logarithm over sigma > R is at most C/log(2) times 2 to the power (2-R), uniformly over every real height. Integrating the exponential majorant gives the displayed coefficient exactly.

**Theorem 1.6 (The same absolute estimate for the real lognorm).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_abs_log_norm_riemannZeta_Ioi_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_abs_log_norm_riemannZeta_Ioi_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute real part is bounded by the complex norm, so the integral of the absolute real lognorm satisfies the same uniform estimate.

**Definition 1.7 (The improper horizontal lognorm tail).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail`

*Formalization.* `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_R(t) is the actual integral of log(norm(zeta(sigma+it))) over sigma > R. The definition is total; the analytic statements use R >= 2.

**Theorem 1.8 (A uniform truncation error).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.abs_zetaHorizontalLogTail_sub_intervalIntegral_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.abs_zetaHorizontalLogTail_sub_intervalIntegral_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X >= R >= 2, subtracting the integral from R to X leaves exactly the tail with lower endpoint X. Its absolute value is at most C/log(2) times 2 to the power (2-X), for every real height.

**Theorem 1.9 (Oriented transport between arbitrary real heights).**

Lean statement: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail_sub_eq_intervalIntegral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail_sub_eq_intervalIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every R >= 2 and all real u and v, T_R(v)-T_R(u) equals the oriented integral from u to v of Im Log(zeta(R+it)). Cauchy's rectangle identity gives the top horizontal real integral minus the bottom one as the left vertical imaginary integral minus the right one. The right edge has absolute value at most C times 2 to the power (2-X) times abs(v-u), which tends to zero as X tends to infinity. Integrability identifies the horizontal limits with the actual improper tails. The oriented formula includes coincident and reversed endpoints. This half-plane identity imposes no condition on zeros in the critical strip.

## References

- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.abs_zetaHorizontalLogTail_sub_intervalIntegral_le`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_log_norm_riemannZeta_Ioi`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integrableOn_principal_log_riemannZeta_Ioi`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_abs_log_norm_riemannZeta_Ioi_le`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.integral_norm_principal_log_riemannZeta_Ioi_le`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.norm_log_riemannZeta_le_rpow`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.re_zeta_pos_of_two_le_re`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail`
- Truth anchor: `D5/S3/Weil/ZetaRvm/HorizontalLogTail.zetaHorizontalLogTail_sub_eq_intervalIntegral`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Integral](../Mertens/Cryptids/VonMangoldtCount/Integral.md)
