# Trace entropy for a finite Gibbs system and an observer clock

## Abstract

A positive observer clock gives a normalized faithful trace and a unique entropy-maximizing density in the finite Gibbs model.

**Theorem 1.1 (The positive-clock projection in total energy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.dressed_clock_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.dressed_clock_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

Shifting the ith clock coordinate by its matter energy turns the total energy into the common coordinate y. The positive-clock projection becomes diagonal and keeps precisely the entries with Eᵢ ≤ y.

**Theorem 1.2 (Semifinite trace weight).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.coreWeight_semifinite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.coreWeight_semifinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

Cut a bounded positive field to total energies y ≥ −k. Each cut has finite weight, since the exponential is integrable on that half-line. The supremum of the cut weights is the weight of the field.

**Theorem 1.3 (Normalization of the corner trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

The exponential weight is β exp(−βy)/Z, with β > 0 and Z the Gibbs partition function. For the ith diagonal entry, change variables to x = y − Eᵢ. Its contribution is the Gibbs probability of i.

**Theorem 1.4 (Faithfulness of the trace).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_faithful`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

A positive integrable field with zero trace has vanishing ordinary matrix trace almost everywhere, since the exponential weight is strictly positive. A positive semidefinite matrix with zero trace vanishes.

**Theorem 1.5 (Cyclicity in the total-energy fibers).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_mul_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_mul_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

Ordinary matrix trace is cyclic in each fiber. Its scalar-weighted integrals therefore agree on the two products.

**Theorem 1.6 (Gibbs and exponential clock moments).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.gibbs_clock_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.gibbs_clock_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

The trace of a compressed matter observable times a physical clock function is the Gibbs expectation of the matter observable times the expectation of the clock function under β exp(−βx) on x > 0.

**Theorem 1.7 (Unique entropy maximizer).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.trace_entropy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.trace_entropy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

The scalar gap r log r − r + 1 is nonnegative for r ≥ 0 and vanishes exactly at r = 1. Functional calculus and faithfulness make the extended trace entropy vanish precisely at the compressed unit.

**Theorem 1.8 (The physical-clock entropy identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_generalized_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_generalized_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

For a classical clock density p and a matter density σ in the Gibbs centralizer, the entropy is the differential entropy of p minus the p-weighted observer energy βx and matter relative entropy to the Gibbs state, plus log β. The finite identity assumes integrable p log p and xp. The constant comes from the normalization of the exponential clock density.

**Theorem 1.9 (Entropy gained by restriction to the energy blocks).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_entropy_coherence_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_entropy_coherence_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran, Roberto Longo, Geoff Penington, and Edward Witten (2023). *An algebra of observables for de Sitter space*. DOI: [10.1007/JHEP02(2023)082](https://doi.org/10.1007/JHEP02(2023)082). URL: <https://arxiv.org/abs/2206.10780>.

*Commentary.*

Pinching deletes matrix entries between distinct Gibbs energies and preserves the diagonal energy blocks. The gain is the p-weighted relative entropy from the unpinched state to its pinching. For integrable p log p and xp, the defect vanishes exactly when the state belongs to the centralizer almost everywhere for the clock law.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.coreWeight_semifinite`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.dressed_clock_cutoff`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.gibbs_clock_moments`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_entropy_coherence_defect`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_generalized_entropy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_faithful`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_mul_comm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.observer_trace_one`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy.trace_entropy_eq_zero_iff`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy](../TraceClass/FiniteEntropyRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../../Divergence/VonNeumannEntropyPinching.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Lieb/PositiveMapJensen](../../Lieb/PositiveMapJensen.md)
