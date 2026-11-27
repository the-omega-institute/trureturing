# Three-copy discrimination of Wu Gibbs rotations

## Abstract

The exact three-copy Helstrom bias exceeds every first-qubit PPT payoff for mixed Wu Gibbs rotations with positive Bloch coordinates.

Let ρ(x,z) = (I + zZ + xX)/2 on the active qubit. Write D for the difference ρ(x,z)⊗³ − ρ(−x,z)⊗³ and Γ for partial transposition on the first qubit. The equal-prior success probability of a binary effect F is (1 + Re tr(FD))/2.

**Theorem 1.1 (Normalized three-copy hypotheses).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_states`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For real x and z with x² + z² < 1, both tensor powers are positive definite and have trace one.

**Theorem 1.2 (Exact Helstrom bias and unique effect).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_helstrom`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_helstrom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For x > 0 and x² + z² < 1, set b = x(√(1 + z² + z⁴) + (1 − x² − z²)/2). The Dicke block and two alternating-pair blocks give the sign S(z) of D. The effect P = (I + S(z))/2 and its complement are positive semidefinite, Re tr(PD) = b, and the trace norm of D is 2b. Every complex binary effect F satisfies Re tr(FD) ≤ b, with equality exactly when F = P.

**Theorem 1.3 (Invariance of the density difference).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.difference_firstTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.difference_firstTranspose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For all real x and z, Γ(D) = D because the single-qubit factors are symmetric in the computational basis.

**Theorem 1.4 (Exact change of the sign entry).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.sign_firstTranspose_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.sign_firstTranspose_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Partial transposition exchanges the (000,111) and (100,011) entries. For every real z, Re(S[000,111] − S[100,011]) = (2/3)(1 − (1 − z²)/√(1 + z² + z⁴)). This difference is positive for z > 0.

**Theorem 1.5 (Strict PPT payoff bound).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_ppt_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_ppt_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For x > 0, z > 0 and x² + z² < 1, if F, I − F, Γ(F) and I − Γ(F) are positive semidefinite, then Re tr(FD) < b. Invariance of D gives Γ(F) the same payoff as F. Equality would force both effects to equal P by uniqueness, contradicting the change of its off-diagonal entry under Γ.

Figure 5 of Conlon et al., arXiv:2408.06678v2, includes a numerical comparison of the collective Helstrom bound with PPT discrimination across the one-versus-two cut. https://arxiv.org/html/2408.06678v2#S4.F5

## References

- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.difference_firstTranspose`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.sign_firstTranspose_entry`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_helstrom`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_ppt_lt`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination.threeCopy_states`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](../../Entanglement/AbsolutePPT/Bipartite.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound](../../Matrix/AbedNikolaevaNovikovAFDensityBound.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../../QuantumChannels/PositiveFilterTransposeRefutation.md)
