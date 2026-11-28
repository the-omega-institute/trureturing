# Forward variance under a reverse mean budget

## Abstract

A reverse mean budget fixes the sharp logarithmic rate of forward variance.

**Theorem 1.1 (A finite-budget variance floor).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso (2026). *Modular fluctuation relations on local causal horizons*. DOI: [10.48550/arXiv.2611.33384](https://doi.org/10.48550/arXiv.2611.33384). URL: <https://arxiv.org/abs/2611.33384v1>.

*Commentary.*

Split the inverse tilted probability at a positive cutoff R. Its mass above R is at most (B + 1/(eβ))/R under the reverse mean budget B. The forward variance about a controls the contribution from outside a radius δ below the cutoff.

**Theorem 1.2 (Strict positivity at finite budget).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_exponential_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_exponential_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso (2026). *Modular fluctuation relations on local causal horizons*. DOI: [10.48550/arXiv.2611.33384](https://doi.org/10.48550/arXiv.2611.33384). URL: <https://arxiv.org/abs/2611.33384v1>.

*Commentary.*

When 0 < δ < a, an explicit choice of the reverse cutoff gives a strictly positive lower bound on the forward centered second moment for every finite nonnegative B.

**Theorem 1.3 (Calibrated Gibbs ladders attain the exponent).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.exists_calibrated_gibbs_rate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.exists_calibrated_gibbs_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso (2026). *Modular fluctuation relations on local causal horizons*. DOI: [10.48550/arXiv.2611.33384](https://doi.org/10.48550/arXiv.2611.33384). URL: <https://arxiv.org/abs/2611.33384v1>.

*Commentary.*

The spacing tends to the prescribed positive forward mean, which it realizes exactly for each sufficiently large ladder. Per level, the reverse mean tends to a(1 − exp(−βa)), and the log of the forward variance tends to −βa.

**Theorem 1.4 (Sharp logarithmic rate).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.tendsto_log_inf_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.tendsto_log_inf_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcos L. W. Basso (2026). *Modular fluctuation relations on local causal horizons*. DOI: [10.48550/arXiv.2611.33384](https://doi.org/10.48550/arXiv.2611.33384). URL: <https://arxiv.org/abs/2611.33384v1>.

*Commentary.*

At inverse temperature β > 0 and forward mean a > 0, the log of the infimum forward variance divided by the reverse mean budget B tends to −β/(1 − exp(−βa)) as B grows. The result holds for finite reflected-tilt laws, for cyclic Gibbs ladders, and for every class between these two.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.exists_calibrated_gibbs_rate`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.tendsto_log_inf_variance`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_exponential_floor`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.variance_lower_bound`
- Dependency: [D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance](GibbsLadderForwardVariance.md)
