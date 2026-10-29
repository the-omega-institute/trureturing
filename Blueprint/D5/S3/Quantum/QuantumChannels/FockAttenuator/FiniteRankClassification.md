# Cardinal rank classification for the actual completed channel

## Abstract

Cardinal rank classification for the actual completed channel.

**Theorem 1.1 (Cardinal rank classification for the actual completed channel).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification.actual_rank_three_iff_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification.actual_rank_three_iff_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero a in lp(Natural -> Complex,2), the actual output of the balanced two-photon pure attenuator has Cardinal Module.rank of its operator range at least three. Its rank equals three exactly when the Bargmann transform of a is c*exp(alpha*z) or c*exp(alpha*z)*(z-beta)^2, for arbitrary complex parameters with c nonzero.

Finite Cardinal output rank is equivalent to an exponential-polynomial Bargmann transform for every completed input, including zero. Thus a transform outside that class has no natural bound on its actual output range dimension. Infinite-dimensional ranges are never replaced by finrank.

The actual point-mass ProbabilityVector reduces the existing double-index pure output ensemble to purePartialTrace of the existing beam splitter output. The completed kernel formula, exact-count rescaling, Hilbert rank/separation equivalence and entire scalar classification then prove the statements. The nonzero lower bound also proves exact attainment for both equality profiles.

This independent rank classification does not settle the parent all-density entropy problem, the spectral entropy and mixed-ensemble joins, the remaining E1/M0/P1/M3 obligations, a universal elementary-symmetric lower bound, or the all-n/all-eta conjecture. Those parent obligations remain open.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification.actual_rank_three_iff_profile`
- Dependency: [D5/S3/Analytic/Entire/PolynomialKernelRank](../../../Analytic/Entire/PolynomialKernelRank.md)
- Dependency: [D5/S3/Analytic/Entire/WeightedHankelLowerRank](../../../Analytic/Entire/WeightedHankelLowerRank.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator](Attenuator.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel](CompletedKernel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock](ExponentialPolynomialFock.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/RankSeparation](RankSeparation.md)
