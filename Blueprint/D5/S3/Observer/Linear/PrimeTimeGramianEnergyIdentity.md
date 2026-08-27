# Prime-Time Gramian Energy Identity

## Abstract

The weighted prime-time Gramian quadratic form equals trace-readout energy.

**Theorem 1.1 (The Gramian quadratic form is total weighted trace energy).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}(d),\\{}Context, Outcome: Type,\\{}s, \beta\in \mathbb{R},\\{}H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianSpace}(d), \operatorname{HermitianSpace}(d)),\\{}E: NatPrimes \times \mathbb{N} \times Context \times Outcome \times \mathbb{N} \to \operatorname{HermitianSpace}(d),\\{}w: Context \times Outcome \to \mathbb{R},\\{}D\in \operatorname{HermitianTraceZero}(\operatorname{Fin}(d)),\\{}\text{let } primePartition := \sum_{p\in NatPrimes} primeEvidence\left(s, p\right);\\{}precisionWeight(p, k) := (1-primeEvidence\left(s, p\right)) \times p^{-s \times (k+1)} / primePartition;\\{}timeWeight(t) := (1-\beta) \times \beta^{t};\\{}centered(p, k, b, a, t) := centeredEffect\left((H^{t})(E\left(p, k, b, a\right))\right);\\{}gramTerm(p, k, b, a, t) := precisionWeight\left(p, k\right) \times timeWeight\left(t\right) \times w\left(b, a\right) \times \operatorname{rankOne}(\mathbb{R}, centered\left(p, k, b, a, t\right), centered\left(p, k, b, a, t\right));\\{}Summable\left(gramTerm\right) \Rightarrow\\{}\text{let } gramian := \sum_{p\in NatPrimes, k\in \mathbb{N}, b\in Context, a\in Outcome, t\in \mathbb{N}} gramTerm\left(p, k, b, a, t\right);\\{}\langle D, gramian\left(D\right) \rangle_{HS} = \sum_{p\in NatPrimes, k\in \mathbb{N}, b\in Context, a\in Outcome, t\in \mathbb{N}} precisionWeight\left(p, k\right) \times timeWeight\left(t\right) \times w\left(b, a\right) \times \left\lVert \operatorname{Tr}(\operatorname{matrix}(D) \times \operatorname{matrix}(centered\left(p, k, b, a, t\right))) \right\rVert^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity.prime_time_gramian_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the canonical real trace-zero Hermitian carrier, form each centered effect by applying the supplied Heisenberg evolution at its time index and then removing its scalar trace part.

The prime evidence partition, precision weight, geometric time weight, and context-outcome weight construct a weighted rank-one operator for every five-component index.

Whenever this operator family is summable, continuous evaluation and the real inner product transport its sum term by term. Hermitian trace reality then identifies each term with the squared modulus of the corresponding trace readout.

Repository and pinned-library searches found no packaged theorem for the complete five-index identity. Canonical centered-effect, trace-zero carrier, prime-evidence, and rank-one constructions are reused directly.

## References

- Truth anchor: `D5/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity.prime_time_gramian_energy_identity`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](../../Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold.md)
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../../Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../../Quantum/Measurement/BasisMeasurementProjection.md)
