# Finite Informational Effect Certificate

## Abstract

Informationally complete quantum effects admit a dimension-bounded finite certificate.

**Theorem 1.1 (A finite effect subfamily retains informational completeness).**

$$\forall d: \operatorname{Nat}, \operatorname{NeZero}(d),\\{}I: \operatorname{Type},\\{}E: I \to \{A: \operatorname{HermitianSpace}(d) \mid \operatorname{PosSemidef}(\operatorname{matrix}(A)) \land \operatorname{PosSemidef}(1-\operatorname{matrix}(A))\},\\{}\operatorname{Injective}((\rho: \operatorname{DensityState}(\operatorname{Fin}(d)) \mapsto (i: I \mapsto \Re \operatorname{Tr}(\operatorname{matrix}(\rho) \operatorname{matrix}(E(i)))))) \Rightarrow\\{}\exists S: \operatorname{Finset}(I), \operatorname{card}(S) \leq d^{2}-1 \land\\{}\operatorname{span}(\mathbb{R}, \{\operatorname{centeredHermitianMap}(d, E(i)): i\in S\}) = \operatorname{traceZeroHermitian}(d) \land\\{}\operatorname{Injective}((\rho: \operatorname{DensityState}(\operatorname{Fin}(d)) \mapsto (i\in S \mapsto \Re \operatorname{Tr}(\operatorname{matrix}(\rho) \operatorname{matrix}(E(i)))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate.finite_informational_effect_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source family consists of positive Hermitian effects bounded above by the identity. Its trace readout is injective on the canonical positive trace-one density states.

Canonical trace removal turns informational completeness into full span of the real trace-zero Hermitian carrier. Finite-dimensional basis extraction chooses source indices rather than replacement vectors, so the selected original effects still separate states.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate.finite_informational_effect_certificate`
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](FiniteSequentialWordCertificate.md)
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
