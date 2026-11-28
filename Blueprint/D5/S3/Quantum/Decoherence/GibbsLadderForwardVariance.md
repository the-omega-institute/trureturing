# Forward energy variance in a finite Gibbs ladder

## Abstract

Finite cyclic Gibbs dynamics can have arbitrarily small forward variance at a fixed positive mean.

**Theorem 1.1 (Arbitrarily small forward variance at fixed positive mean).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance.exists_gibbs_ladder_forward_variance_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance.exists_gibbs_ladder_forward_variance_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso (2026). *Modular fluctuation relations on local causal horizons*. DOI: [10.48550/arXiv.2611.33384](https://doi.org/10.48550/arXiv.2611.33384). URL: <https://arxiv.org/abs/2611.33384v1>.

*Commentary.*

For every positive inverse temperature, positive target mean and positive tolerance, an equally spaced finite Gibbs ladder and its cyclic shift realize the target forward mean with variance below the tolerance.

Only the wraparound transition differs from the common energy increment. Its Gibbs weight decays exponentially in the number of levels. Continuity in the level spacing fixes the mean exactly.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance.exists_gibbs_ladder_forward_variance_lt`
- Dependency: [D5/S3/Quantum/Decoherence/GibbsBathBandwidth](GibbsBathBandwidth.md)
