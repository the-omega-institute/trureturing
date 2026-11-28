# Tracial spectator square-root energy

## Abstract

Exact tracial square-root cell and spectator energy bound on the complex CAR frame.

At spectator ratio 1 in the signed-spin setting of Wu’s cubic trace, the spectator jump is J_s = jump 1 = e ⊗ I in occupation order (spectator, cold). Write L_s(A) = A − J_s† A J_s − J_s A J_s†, Q = Tr_s(A)/2 and H = A − I ⊗ Q. All traces are ordinary.

**Theorem 1.1 (Polynomial identity in the square roots).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.scalar_polynomial_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.scalar_polynomial_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For all real a,b, (9/8)(a² − b²)²(a² + b²) − (a³ − b³)² = (a − b)⁴(a² + 4ab + b²)/8.

**Theorem 1.2 (Exact square-root cell identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.sharp_scalar_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.sharp_scalar_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For all u,v ≥ 0, including zero roots, the tracial cubic cell minus the squared square-root difference is (9/8)(u − v)²(u + v) − (u^(3/2) − v^(3/2))² = (√u − √v)⁴(u + 4√u√v + v)/8.

**Theorem 1.3 (Tracial cubic cell bounds the square-root difference).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_cell_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_cell_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For u,v ≥ 0, the factorized difference is nonnegative, so cost(1,u,v) ≥ (u^(3/2) − v^(3/2))².

**Theorem 1.4 (Exact spectator trace excess).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_excess`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every complex Hermitian A, let D = A₀₀ − A₁₁ be the difference of its two diagonal spectator blocks. The two gain terms exchange the diagonal blocks, giving Re Tr(A L_s(A)) − Re Tr(H²) = (1/2) Re Tr(D†D).

**Theorem 1.5 (Remainder bounded by the tracial form).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.remainder_le_tracial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.remainder_le_tracial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every Hermitian A, Re Tr(H²) ≤ Re Tr(A L_s(A)) by nonnegativity of the squared Hilbert–Schmidt norm of D.

**Theorem 1.6 (Quadratic trace on the physical spectator jump).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_trace_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_trace_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a complex unitary frame U and real spectral roots v, put sᵢ = vᵢ^(3/2) and A = U diag(s) U†. Then Re Tr(A L_s(A)) = ∑ᵢₖ (sᵢ − sₖ)² |(U† J_s U)ᵢₖ|². The anticommutator J_s J_s† + J_s† J_s = I gives the two squared terms, and cyclicity of trace identifies the two gain terms.

**Theorem 1.7 (Same-frame spectator energy hypothesis).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.hEs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.hEs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a complex unitary frame U and nonnegative spectral roots v, set A = U diag(vᵢ^(3/2)) U†. Summing the tracial cell inequality with the nonnegative directed weights of J_s gives Re Tr(H²) ≤ energy(1,U,1,v). This supplies the energy hypothesis of rankTwo_joint_lower for the same square-root matrix and normalized cold marginal.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.hEs`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.remainder_le_tracial`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.scalar_polynomial_identity`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.sharp_scalar_identity`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_cell_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_excess`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTracialSpectatorSqrtEnergy.tracial_trace_frame`
- Dependency: [D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression](WuRankTwoSpectatorCompression.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge](WuTwoTemperatureCubicPhysicalBridge.md)
