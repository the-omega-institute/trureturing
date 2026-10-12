# FourQubitCompatibilityDegree

## Abstract

FourQubitCompatibilityDegree: exact analytic statements for four-qubit white-noise compatibility.

**Definition 1.1 (feasible).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \operatorname{feasible}\left(E\right) = \{(s: \mathbb{R}) \mid s \in \operatorname{Set.Icc}\left(0, 1\right) \land \operatorname{Compatible4}\left(\operatorname{noisy}\left(s, E\right)\right)\}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The feasible noise parameters lie in [0, 1] and admit one joint POVM.

**Definition 1.2 (compatDegree).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \operatorname{compatDegree}\left(E\right) = \operatorname{sSup}\left(\operatorname{feasible}\left(E\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.compatDegree` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.16 (p. 13): “Given a g-tuple of measurements E = (E·∣ₓ)ₓ∈[g] on a d-dimensional Hilbert space, having respectively k₁, …, kg outcomes, define their compatibility degree as” sℂ(E) := max{s ∈ [0, 1] : {(Eᵢ∣ₓ(s))ᵢ∈[kₓ]}ₓ∈[g] are compatible}. The closed feasible set has a greatest member, so sSup equals this maximum.

**Definition 1.3 (povmTuples).**

$$(povmTuples: \operatorname{Set}\left(\operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)) = \{(E: \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)) \mid \forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPOVM}\left(E\left(i\right)\right)\}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.povmTuples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the four measurements is a dichotomic POVM on ℂ².

**Definition 1.4 (minCompatDegree).**

$$(minCompatDegree: \mathbb{R}) = \operatorname{sInf}\left(compatDegree'' povmTuples\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.minCompatDegree` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.16 (p. 13): “Consider a measurement setting given by positive integers d, g ∈ ℕ and kₓ ∈ ℕ for all x ∈ [g]. The minimum compatibility degree of this measurement setting is defined as” sℂ(d, g, (k₁, …, kg)) := min{sℂ(E) : E is a g-tuple of measurements on a d-dimensional Hilbert space with k₁, …, kg outcomes}. “If k₁ = … = kg = 2, we write sℂ(d, g) instead.” The extremal tuple attains sInf.

**Definition 1.5 (claim).**

$$(claim: Prop) = \left(minCompatDegree = \frac{2}{\sqrt{13}}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.claim` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Conjecture 6.10 (p. 44): “We conjecture that sℂ(2, 4) = 2/√13. That would mean that the value computed in [BQG+17] is optimal up to numerical precision.” The left side is the minimum of the attained white-noise compatibility degrees over all four-tuples of dichotomic POVMs on ℂ², with the literal marginal and noise definitions.

**Theorem 1.6 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result` (`✓ std3`). ∎

*Resolves.* `Problems/bluhm-2025-four-qubit-compatibility-degree` (proved) by `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bluhm-2025-four-qubit-compatibility-degree","declaration_gid":"D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

The sharp four-vector inequality constructs a joint POVM at 2/√13 for every four-tuple of qubit effects, including biased effects. A trine-plus-perpendicular tuple admits an endpoint parent and a matching dual trace bound. Thus its compatibility degree attains the global minimum.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.compatDegree`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.feasible`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.minCompatDegree`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.povmTuples`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result`
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
