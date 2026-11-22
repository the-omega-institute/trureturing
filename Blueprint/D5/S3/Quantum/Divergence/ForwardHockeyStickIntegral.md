# Forward hockey-stick integrals

## Abstract

The finite Umegaki pairing and its bounded Loewner difference in forward profiles.

**Definition 1.1 (The forward hockey-stick profile).**

Lean statement: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.forwardProfile`

*Formalization.* `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.forwardProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite Hermitian matrices A and B of the same size, the profile at real s is the real trace of the positive part of A−sB.

**Theorem 1.2 (Two forward integrals for the trace-log pairing).**

Lean statement: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_eq_umegaki`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_eq_umegaki` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Péter E. Frenkel (2023). *Integral formula for quantum relative entropy implies data processing inequality*. DOI: [10.22331/q-2023-09-07-1102](https://doi.org/10.22331/q-2023-09-07-1102). URL: <https://arxiv.org/abs/2208.12194>.

*Acknowledgement.* Christoph Hirche and Marco Tomamichel (2024). *Quantum Rényi and f-divergences from integral representations*. DOI: [10.1007/s00220-024-05087-3](https://doi.org/10.1007/s00220-024-05087-3). URL: <https://arxiv.org/abs/2306.12343>.

*Acknowledgement.* Lukas Schmitt (2026). *Relative entropy representations via tracial joint spectral measures*. URL: <https://arxiv.org/abs/2609.12547>.

*Commentary.*

For finite positive semidefinite A and positive definite B, let E(s) be the forward profile. Integrate (E(s)−Tr(A−sB))/s on (0,1) and E(s)/s on (1,∞). Both real integrands are integrable. The sum of the integrals plus Tr(A−B) is the real trace of A(log A−log B).

The involution s ↦ s/(s−1) maps (0,1) onto (−∞,0) and (1,∞) onto itself. At t=s/(s−1), the pencil is (1−t)(A−sB). The scalar converts the negative-part trace into the forward profile on the right and the forward profile minus Tr(A−sB) on the left. The original weight, the factor |1−t|, and the Jacobian magnitude (s−1)⁻² multiply to 1/s. The pencil is positive semidefinite on [0,1]. Finiteness of the pencil integral gives integrability on both transformed tails.

Frenkel’s Theorem 6 supplies the pencil formula. Hirche and Tomamichel’s Corollary 2.3 uses two orientations on the upper tail for states. Schmitt’s equations (36)–(38) include the unnormalized forward form.

**Theorem 1.3 (The signed profile difference on a bounded interval).**

Lean statement: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_sub_eq_umegaki_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_sub_eq_umegaki_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Jenčová (2024). *Recoverability of quantum channels via hypothesis testing*. DOI: [10.1007/s11005-024-01775-2](https://doi.org/10.1007/s11005-024-01775-2). URL: <https://arxiv.org/abs/2303.11707>.

*Acknowledgement.* Lukas Schmitt (2026). *Relative entropy representations via tracial joint spectral measures*. URL: <https://arxiv.org/abs/2609.12547>.

*Commentary.*

Take two finite pairs (A,B) and (C,D) with positive semidefinite first endpoints and positive definite references. Their dimensions may differ. Suppose Tr A=Tr C, Tr B=Tr D, 0<u≤v, uB≤A≤vB, and uD≤C≤vD. The profiles agree for s≤u, where each equals its affine trace, and for s≥v, where both vanish. Their difference divided by s is integrable on [u,v]. Its real integral is the first trace-log pairing minus the second.

The matching trace masses cancel both the affine term in the lower integrand and the additive trace correction. Jenčová’s Corollary 1 gives the normalized finite-interval formula. The signed identity yields the profile comparison for the Fibonacci optimization.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.forwardProfile`
- Truth anchor: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_eq_umegaki`
- Truth anchor: `D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral.integral_forwardProfile_sub_eq_umegaki_sub`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiPencilIntegral](UmegakiPencilIntegral.md)
