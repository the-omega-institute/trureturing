# Centered logarithmic derivatives and global zero sums

## Abstract

A scaled disk estimate gives the centered zero expansion, and dyadic counts supply the reciprocal-square summability it requires.

**Theorem 1.1 (Exact zeros and a quadratic radius denominator).**

Lean statement: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_partial_fraction_disk_centered`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_partial_fraction_disk_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be entire with f(0) ≠ 0. Fix R > 0 and B ≥ 2, and assume ‖f(w)‖ ≤ B · ‖f(0)‖ for ‖w‖ ≤ 24R/25. There is a single finite set Z of exactly the zeros of f in the closed disk of radius 22R/25. Write S(u) = ∑_{ρ ∈ Z} m(ρ)/(u − ρ), with m(ρ) the analytic order at ρ. For every ‖s‖ ≤ R/4 with f(s) ≠ 0, the norm of (logDeriv f s − logDeriv f 0) − (S(s) − S(0)) is at most 179180000 · ‖s‖ · log B / R².

Apply logDeriv_partial_fraction_unit_centered to g(w) = f(Rw)/f(0). Multiplication by R carries its exact zero set to Z and preserves analytic orders. The chain rule and the scaled denominators give one factor of 1/R, and the evaluation norm ‖s/R‖ gives the other.

**Theorem 1.2 (An absolutely summable expansion over all actual zeros).**

Lean statement: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_global_zero_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_global_zero_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be entire with f(0) ≠ 0. Suppose that for all sufficiently large R one has B(R) ≥ 2 and ‖f(w)‖ ≤ B(R) · ‖f(0)‖ for ‖w‖ ≤ 24R/25. Assume log B(R) = o(R²) and that m(ρ)/‖ρ‖² is summable over the actual zeros, with m(ρ) the analytic order. For every s with f(s) ≠ 0, the kernels m(ρ) · ((s − ρ)⁻¹ + ρ⁻¹) have summable norms and sum to logDeriv f s − logDeriv f 0.

Outside the finite disk ‖ρ‖ ≤ 2‖s‖, combine the two reciprocals as s/((s − ρ)ρ). This bounds the kernel norm by 2‖s‖ · m(ρ)/‖ρ‖². The exact disk cutoffs eventually contain every finite subset of the zeros, so their sums tend to the sum of the centered kernels. The scaled disk remainder tends to zero by log B(R) = o(R²).

**Theorem 1.3 (Reciprocal-square summability from dyadic zero counts).**

Lean statement: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.summable_zero_multiplicity_div_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.summable_zero_multiplicity_div_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be entire with f(0) ≠ 0 and the eventual normalized disk envelope B(R) above. If the series over natural n with terms log B(2^(n+2)/(22/25)) / (2^(n+1))² is summable, then m(ρ)/‖ρ‖² is summable over the actual zeros of f.

The disk ‖ρ‖ ≤ 2 contributes a finite sum. Each remaining shell has 2^(n+1) < ‖ρ‖ ≤ 2^(n+2) and contains finitely many zeros. For sufficiently large n, the envelope applies at R = 2^(n+2)/(22/25). Landau's logDeriv_partial_fraction_disk then bounds the shell's multiplicities by log B(R) / log((24/25)/(22/25)). Dividing by the squared lower radius gives the summable tail majorant. The finitely many earlier shells contribute finite sums. The unique shell partition follows heightShell_partition in RightStripInverseHeight.lean.

## References

- Truth anchor: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_global_zero_expansion`
- Truth anchor: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.logDeriv_partial_fraction_disk_centered`
- Truth anchor: `D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.summable_zero_multiplicity_div_norm_sq`
- Dependency: [D5/S3/Weil/ZetaExplicit/CenteredDiskLogDeriv](CenteredDiskLogDeriv.md)
