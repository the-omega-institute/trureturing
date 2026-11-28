# Quadratic inverses under parity attenuation

## Abstract

A quadratic inverse has a sharp squared-attenuation upper chord.

**Theorem 1.1 (Upper chord with squared attenuation).**

Lean statement: `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.sSup_trialValue_chord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.sSup_trialValue_chord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miaojiang Chen; Wenjing Xiao; Haiqiang Chen; Jiarong Liang; Anfeng Liu; Zhenrong Zhang; Athanasios V. Vasilakos; Saif Al-Kuwari; Ahmed Farouk; H. Herbert Song (2026). *Noise threshold for learning with quantum memory*. DOI: [10.48550/arXiv.2611.34474](https://doi.org/10.48550/arXiv.2611.34474). URL: <https://arxiv.org/abs/2611.34474v1>.

*Commentary.*

Scale the odd source and the even–odd coupling by the same real factor a in [0,1]. After scaling the odd trial vector by a, the objective is affine in a². Its supremum is bounded by the fully pinched and unattenuated endpoint values with weights 1 − a² and a².

**Theorem 1.2 (The variational optimum at a linear solution).**

Lean statement: `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.variationalValue_eq_inner_of_solve`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.variationalValue_eq_inner_of_solve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miaojiang Chen; Wenjing Xiao; Haiqiang Chen; Jiarong Liang; Anfeng Liu; Zhenrong Zhang; Athanasios V. Vasilakos; Saif Al-Kuwari; Ahmed Farouk; H. Herbert Song (2026). *Noise threshold for learning with quantum memory*. DOI: [10.48550/arXiv.2611.34474](https://doi.org/10.48550/arXiv.2611.34474). URL: <https://arxiv.org/abs/2611.34474v1>.

*Commentary.*

For a symmetric nonnegative quadratic form with operator A, any solution Aw = r attains the supremum of the trial objective. Completing the square identifies the optimum with the inner product of w and r.

## References

- Truth anchor: `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.sSup_trialValue_chord`
- Truth anchor: `D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.variationalValue_eq_inner_of_solve`
