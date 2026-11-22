# The signed two-mode Gibbs calculation

## Abstract

The signed Gibbs map transports the odd kernel and determines its trace quartic.

**Definition 1.1 (Critical-time map).**

Lean statement: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap`

*Formalization.* `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set u = s⁴, w = s³, M = 1 + s¹², L = 1 + w + w², h = (1 + u)/L and r = sh, where s = exp(−β/12) for inverse temperature β. The one-mode map multiplies coherences by √h and has population weights α = (s¹¹ + h)/M, η = w(1 − r)/M, ζ = u²(1 − r)/M and δ = (1 + s¹²r)/M. Apply the conjugation by diag(1, 1, −1, 1), the local map on the second mode, the same conjugation again, and the local map on the first mode.

**Theorem 1.2 (Action on the coherence triangle).**

Lean statement: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s ≥ 0, let x be the 00-to-odd row, z the odd-to-11 column and d the 00-to-11 entry, all with arbitrary complex entries. In coordinate form let j(z) = (z₁, −z₀). The image has coordinates √h(αx + ηj(z)), √h(δz − ζj(x)) and hd, with the conjugate entries set by Hermiticity.

**Theorem 1.3 (Transport of the odd kernel direction).**

Lean statement: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Nₐ(z) for the triangle with x = aj(z) and d = 0. For every s ≥ 0 and every complex z, the signed map sends Nᵤ(z) to √h N_w(z). The identities αu + η = w and ζu + δ = 1 give the two output coordinates.

**Theorem 1.4 (Exact quartic on the odd kernel direction).**

Lean statement: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.kernel_pure_quartic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.kernel_pure_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s ≥ 0 and every complex z, set ν = |z₀|² + |z₁|² and Ω = diag(u², u, u, 1). The input contribution is 2/M² times the square of the real part of the ordinary trace of ΩNᵤ(z)². Subtracting the real part of the ordinary trace of the fourth power of the mapped direction gives 2h²w(2 + 3w + 2w²)ν².

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.kernel_pure_quartic`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_kernel`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuColdSignedGibbs.signedMap_triangle`
- Dependency: [D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor](WuRankOneEndpointFloor.md)
