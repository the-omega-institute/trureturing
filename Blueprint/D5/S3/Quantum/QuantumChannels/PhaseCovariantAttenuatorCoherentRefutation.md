# PhaseCovariantAttenuatorCoherentRefutation

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (claim).**

$$claim = \forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\exists alpha : \mathbb{C}, (\forall rho : DensityOperator, (\operatorname{vonNeumannEntropy}\left(\operatorname{operator}\left(\operatorname{attenuator}\left(eta, hEta, p, \operatorname{coherentDensity}\left(alpha\right)\right)\right)\right) \le \operatorname{vonNeumannEntropy}\left(\operatorname{operator}\left(\operatorname{attenuator}\left(eta, hEta, p, rho\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.claim` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

Conjecture 2 (Phase-covariant attenuator), section IV.B, arXiv v2 PDF p. 12: "The minimum output entropy of a phase-covariant attenuator channel ℳ<sub>η,𝐩</sub> is achieved by coherent states, ∀η,𝐩." eta ranges over [0,1], p over every probability vector on Nat, alpha over all complex amplitudes, and rho over all positive trace-one operators on the full Fock space. The existential amplitude precedes the universal density input. Entropy is the infimum over complete countable bases of diagonal Shannon entropy. Equality with spectral von Neumann entropy for every density operator is literature-attested; its infinite-dimensional equivalence is not claimed as kernel-proved. Finite spectral equality and arbitrary-unitary invariance supply the entropy calculations used here.

**Theorem 1.2 (result).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/van-herstraeten-guha-cerf-2024-phase-covariant-attenuator-coherent-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"van-herstraeten-guha-cerf-2024-phase-covariant-attenuator-coherent-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

Take eta=1/2, p=(7/8)delta_1+(1/8)delta_5 and the input |1><1|. Vacuum output has diagonal (113,117,10,10,5,1)/256; the one-photon output has diagonal (115,8,117,0,5,8,3)/256. Displacement covariance and the entropy invariance obtained by transporting all complete bases show that every coherent input has the vacuum output entropy. The exact comparison 115^2*8^16*3^3=100507677308957491200>10^20, together with log(115)>log(113), proves strictly smaller one-photon output entropy. This excludes every coherent state as a minimizer for this channel; it makes no global-minimality assertion about |1>. Conjecture 1 for pure Fock environments remains open.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator](FockAttenuator/Attenuator.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter](FockAttenuator/BeamSplitter.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance](FockAttenuator/DisplacementCovariance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy](FockAttenuator/Entropy.md)
