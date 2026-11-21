# Exact finite Fourier phase memory

## Abstract

The exact guessing optimum for finite Fourier character records in dimension N − 1.

The input ensemble comprises uniformly labeled characters of a finite abelian group G of order N ≥ 2, with nonnegative amplitudes of squared sum one. One common CPTP channel sends the input into a finite quantum memory. The decoder measures only that memory.

**Theorem 1.1 (A feasible optimal profile realized by translates gives an attained maximum).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_characterMemory_of_translate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_characterMemory_of_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

If a profile saturates the budget, satisfies the common-slope certificate and is a mixture of translates of the output subset A, the universal upper bound and translate encoder agree. The success set has a greatest element equal to the squared profile value divided by N.

**Theorem 1.2 (Every saturated certified profile is realizable in dimension N − 1).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take A = G minus {0}. The translate A + z omits precisely z, so choosing b(z) = 1 − d_z realizes every profile of total mass N − 1. The saturation condition makes b a probability distribution.

**Theorem 1.3 (Positive amplitudes give the exact clipped optimum).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_clipped`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_clipped` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

Choose c > 0 so the sum of min(1, (tᵢ/c)²) is N − 1. The maximum guessing probability is (sum of tᵢ√dᵢ)²/N. For G = ℤ/3ℤ and amplitudes (12, 4, 3)/13, c = 5/13 gives d = (1, 16/25, 9/25). The two-dimensional optimum is (17/13)²/3 = 289/507.

**Theorem 1.4 (A zero amplitude gives the full-carrier success in dimension N − 1).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If t_z = 0, put d_z = 0 and all other dᵢ = 1. The translate weights form a point mass at z, which omits that zero coordinate. The maximum is (sum of the amplitudes)²/N, the full-carrier value.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_characterMemory_of_translate`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_clipped`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_certificate`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordDistillation.isGreatest_oneDeficit_of_zero`
- Dependency: [D5/S3/Quantum/PureState/FourierMemoryEncoder](FourierMemoryEncoder.md)
