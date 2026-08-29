# Zeta Prime-Observation Synthesis

## Abstract

The zeta Gibbs law unifies exact prime spectra, information, and observation limits.

**Definition 1.1 (Countable Hellinger affinity).**

$$\operatorname{countableHellingerAffinity}\left(P, Q\right) = \sum_{n \in \mathbb{N}} \sqrt{\operatorname{pmfReal}\left(P, n\right) \cdot \operatorname{pmfReal}\left(Q, n\right)}$$

*Formalization.* `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.countableHellingerAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The countable affinity is the sum of square roots of pointwise PMF mass products. It extends the repository's finite affinity formula to the natural-number carrier used by the zeta law.

**Definition 1.2 (Prime residual law at a precision threshold).**

$$R_{p, k} = \operatorname{LawGiven}\left(E - k, E \geq k\right)$$

*Formalization.* `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeResidualLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Condition the geometric exponent channel on values at least k, then translate the observed tail back by k. The resulting PMF names the unresolved exponent law after k precision layers.

**Definition 1.3 (Probability-weighted prime residual entropy).**

$$\operatorname{primeResidualEntropy}\left(p, k\right) = \operatorname{Pr}\left(E \geq k\right) \cdot \operatorname{H}\left(R_{p, k}\right)$$

*Formalization.* `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeResidualEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Residual entropy is the tail probability multiplied by the Shannon entropy of the translated conditional residual law.

**Definition 1.4 (Prime-indexed diagonal observables are phase blind).**

$$\forall A, \forall p, \operatorname{IsDiag}\left(A(p)\right) \Rightarrow \left(rhoPlus \ne rhoMinus \land \operatorname{jointReadout}\left(A, rhoPlus\right) = \operatorname{jointReadout}\left(A, rhoMinus\right)\right)$$

*Formalization.* `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.PrimeDiagonalPhaseBlindness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every prime-indexed family of diagonal qubit observables gives the same joint readout on the canonical distinct relative-phase pair.

**Theorem 1.5 (Prime exponents have the single-mode thermal spectrum).**

$$1 < s \land p \in \mathbb{P} \Rightarrow \operatorname{primeExponentPMF}\left(s, p\right) = \operatorname{singlePrimeThermalPMF}\left(p, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeExponentPMF_eq_singlePrimeThermalPMF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime and s greater than one, the geometric exponent PMF is exactly the named single-prime thermal PMF, pointwise at every occupation number.

**Theorem 1.6 (Zeta Hellinger affinity factors over prime modes).**

$$1 < s \land 1 < t \Rightarrow \operatorname{countableHellingerAffinity}\left(\operatorname{zetaDist}\left(s\right), \operatorname{zetaDist}\left(t\right)\right) = \prod_{p \in \mathbb{P}} \operatorname{countableHellingerAffinity}\left(\operatorname{primeExponentPMF}\left(s, p\right), \operatorname{primeExponentPMF}\left(t, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.countableHellingerAffinity_zeta_eq_tprod_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two normalizable zeta parameters, the global countable affinity is the convergent infinite product of the geometric prime-coordinate affinities. Euler-log summability licenses the product.

**Theorem 1.7 (FPOD theorem 145.1 on the available carriers).**

$$1 < s \Rightarrow \begin{aligned}\operatorname{Bijective}\left(primeExponentLanguageEquiv\right)\\\operatorname{IndependentPrimeExponents}\left(\operatorname{zetaDist}\left(s\right)\right)\\\operatorname{PrFiniteSupport}\left(s\right) = 1\\\operatorname{UniquePositiveIntegerLaw}\left(n^{-s} / zeta(s)\right)\\\operatorname{H}\left(\operatorname{zetaDist}\left(s\right)\right) = \operatorname{tsumPrimeEntropy}\left(s\right) \land \left(\operatorname{KL}\left(s, t\right) = \operatorname{tsumPrimeKL}\left(s, t\right) \land \left(\operatorname{SummablePrimeFisherSensitivity}\left(s\right) \land \operatorname{HellingerAffinity}\left(s, t\right) = \operatorname{tprodPrimeAffinity}\left(s, t\right)\right)\right)\\\operatorname{ResidualEntropy}\left(p, k + 1\right) = p^{-s} \cdot \operatorname{ResidualEntropy}\left(p, k\right)\\\operatorname{IndependentPrimeThermalSpectra}\left(\operatorname{zetaDist}\left(s\right)\right)\\\operatorname{ClassicallyCompletePrimeValuations}\left(\right) \land \operatorname{QuantumPhaseBlindPrimeDiagonals}\left(\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.zeta_prime_observation_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one, prime valuations separate positive integers and are independent geometric coordinates. Their product law has finite support almost surely and uniquely realizes the zeta masses.

Shannon entropy, real-valued log evidence, and Hellinger affinity have exact prime decompositions. The Fisher component records the proved summable prime sensitivity family; no unproved global score-variance identity is asserted.

Residual entropy contracts by p^(-s). The Fock clause is represented by independent prime modes with exact thermal PMF spectra and modal entropy additivity, not by an unavailable countable trace-class tensor-product operator.

The complete valuation language identifies classical positive integers, while every prime-indexed diagonal qubit family is blind to the named relative-phase pair.

**Theorem 1.8 (The lower boundary is necessary).**

$$\neg \exists q, \operatorname{RealizesPrimeExponentLaw}\left(1, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.one_lt_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the concrete critical parameter s = 1, no PMF on positive integers realizes the independent geometric prime-exponent law.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.PrimeDiagonalPhaseBlindness`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.countableHellingerAffinity`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.countableHellingerAffinity_zeta_eq_tprod_prime`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.one_lt_is_necessary`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeExponentPMF_eq_singlePrimeThermalPMF`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeResidualEntropy`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.primeResidualLaw`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/ZetaPrimeObservationSynthesis.zeta_prime_observation_synthesis`
- Dependency: [D5/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary](../Boundary/ZetaPrimeProductCommonBoundary.md)
- Dependency: [D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability](GlobalPrimeExponentRealizability.md)
- Dependency: [D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction](PrimePrecisionEntropyContraction.md)
- Dependency: [D5/S3/Analytic/ZetaObservation/PrimeChannelLogEvidence](../ZetaObservation/PrimeChannelLogEvidence.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy](../../ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.md)
- Dependency: [D5/S3/Quantum/CountableSlices/SinglePrimeThermalState](../../Quantum/CountableSlices/SinglePrimeThermalState.md)
- Dependency: [D5/S3/Quantum/Tomography/DiagonalPhaseBlindness](../../Quantum/Tomography/DiagonalPhaseBlindness.md)
