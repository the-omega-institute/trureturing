# The clipped profile and its certificate

## Abstract

Clipping solves the scalar optimization for finite phase-memory profiles.

A profile d is feasible if every dᵢ lies in [0,1] and the sum of the dᵢ is at most M. Its value is the sum of tᵢ√dᵢ. For nonnegative amplitudes and positive integer M, the substitution xᵢ = √dᵢ turns this into the dual maximization in Regula, Fang, Wang and Adesso, supplement Eq. (S12). Their Theorem 2 evaluates the optimum.

**Theorem 1.1 (A saturated profile with a common slope below the cap is optimal).**

Lean statement: `D5/S3/Quantum/PureState/DistillationProfile.profileValue_le_of_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/DistillationProfile.profileValue_le_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

Write tᵢ = √dᵢ rᵢ with rᵢ at least c ≥ 0 and rᵢ = c whenever dᵢ < 1. For a competitor v, the inequality 2√(dᵢvᵢ) ≤ dᵢ + vᵢ reduces the comparison to a linear one. The common coefficient c is controlled by the total budget. The remaining coefficient rᵢ − c can contribute only where dᵢ = 1, where vᵢ is already capped.

**Theorem 1.2 (A clipped squared amplitude satisfies the slope conditions).**

Lean statement: `D5/S3/Quantum/PureState/DistillationProfile.clippedProfile_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/DistillationProfile.clippedProfile_certificate` (`✓ std3`). ∎

*Citation.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

For c > 0 take dᵢ = min(1, (tᵢ/c)²) and rᵢ = max(tᵢ,c). The constraints on individual coordinates and the factorization hold at every nonnegative amplitude, including tᵢ = 0. Supplement Eq. (S13) gives the corresponding clipped witness in the dual norm variables.

**Theorem 1.3 (Clipping can exhaust any positive budget up to the support size).**

Lean statement: `D5/S3/Quantum/PureState/DistillationProfile.exists_clippedProfile_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/DistillationProfile.exists_clippedProfile_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso (2018). *One-shot coherence distillation*. DOI: [10.1103/PhysRevLett.121.010401](https://doi.org/10.1103/PhysRevLett.121.010401). URL: <https://arxiv.org/abs/1711.10512v3>.

*Commentary.*

For a real budget M within this range, vary 1/c from zero to a finite value that saturates every positive coordinate. The sum of the clipped squares is continuous and reaches both endpoints. A positive budget forces the chosen reciprocal threshold to be positive.

## References

- Truth anchor: `D5/S3/Quantum/PureState/DistillationProfile.clippedProfile_certificate`
- Truth anchor: `D5/S3/Quantum/PureState/DistillationProfile.exists_clippedProfile_sum`
- Truth anchor: `D5/S3/Quantum/PureState/DistillationProfile.profileValue_le_of_certificate`
