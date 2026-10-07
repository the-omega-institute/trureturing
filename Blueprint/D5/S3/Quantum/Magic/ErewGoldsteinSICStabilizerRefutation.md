# SIC fiducials beyond Clifford-stabilizer states

## Abstract

The special Clifford group of a qutrit is finite, and its eigenphase extension has only finitely many one-dimensional fixed spaces. The continuous qutrit SIC family supplies infinitely many distinct pure-state projectors. Consequently, some SIC fiducials are not Clifford-stabilizer states.

**Definition 1.1 (The half-period phase).**

$$\forall d \in \mathbb{N},\; \operatorname{zeta}\left(d\right) = \operatorname{exp}\left(\frac{(\pi) \cdot (i)}{d}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.zeta` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The computational basis is indexed by ZMod d. The clock phase is exp(2 pi i / d), and zeta is exp(pi i / d). The shift sends basis vector j to basis vector j + 1. Write D(a,b) for the displacement X to the power a times Z to the power b.

**Definition 1.2 (The single-qudit Pauli group).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall P \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; P \in \operatorname{pauliGroup}\left(d\right) \Leftrightarrow (\exists x \in \operatorname{ZMod}\left(2\right),\; \exists k \in \operatorname{ZMod}\left(d\right),\; \exists a \in \operatorname{ZMod}\left(d\right),\; \exists b \in \operatorname{ZMod}\left(d\right),\; P = (((-(1))^{\operatorname{val}\left(x\right)}) \cdot ((\operatorname{zeta}\left(d\right))^{\operatorname{val}\left(k\right)})) \cdot (\operatorname{displacement}\left(d, a, b\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.pauliGroup` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The finite Pauli group includes the sign exponent x in ZMod 2 and the phase, shift and clock exponents k, a and b in ZMod d. Powers use the least nonnegative representatives of residues.

**Definition 1.3 (The Clifford group).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall U \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; U \in \operatorname{cliffordGroup}\left(d\right) \Leftrightarrow ((U \in \operatorname{Unitary}\left(d\right)) \land (\operatorname{image}\left(\operatorname{Ad}\left(U\right), \operatorname{pauliGroup}\left(d\right)\right) = \operatorname{pauliGroup}\left(d\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.cliffordGroup` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

A Clifford matrix is unitary, and conjugation by it maps the entire Pauli group onto itself. Here Ad(U) sends P to U P U adjoint.

**Definition 1.4 (The special Clifford group).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall U \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; U \in \operatorname{specialClifford}\left(d\right) \Leftrightarrow ((U \in \operatorname{cliffordGroup}\left(d\right)) \land (\operatorname{det}\left(U\right) = 1)))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.specialClifford` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Special Clifford matrices have determinant one.

**Definition 1.5 (The eigenvalue set).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall mu \in \mathbb{C},\; mu \in \operatorname{Lambda}\left(d\right) \Leftrightarrow (\exists U \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{specialClifford}\left(d\right)) \land (\exists v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (v \ne 0) \land ((U) \cdot (v) = (mu) \cdot (v)))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.Lambda` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Lambda contains every eigenvalue of every special Clifford matrix. An eigenvalue has a nonzero eigenvector.

**Definition 1.6 (The eigenphase extension).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall V \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; V \in \operatorname{eigenphaseClifford}\left(d\right) \Leftrightarrow (\exists mu \in \mathbb{C},\; (mu \in \operatorname{Lambda}\left(d\right)) \land (\exists U \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{specialClifford}\left(d\right)) \land (V = (mu) \cdot (U)))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.eigenphaseClifford` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The extension consists of all scalar multiples mu U with U special Clifford and mu in Lambda.

**Definition 1.7 (The pointwise fixed space).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall S \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right),\; \forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; v \in \operatorname{invariantSubspace}\left(S\right) \Leftrightarrow (\forall U \in \operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right),\; (U \in S) \Rightarrow ((U) \cdot (v) = v)))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.invariantSubspace` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The invariant subspace is the intersection of the kernels of U minus the identity over U in S. The condition is pointwise fixation, U v = v.

**Definition 1.8 (Pure-state normalization).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall psi \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \operatorname{IsNormalized}\left(psi\right) \Leftrightarrow (\operatorname{inner}\left(psi, psi\right) = 1))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsNormalized` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The Hermitian inner product is the sum of conjugate(psi j) times phi j. Normalization is inner(psi,psi) = 1, equivalently Hilbert norm one.

**Definition 1.9 (Clifford-stabilizer states).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall psi \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \operatorname{IsCliffordStabilizerState}\left(d, psi\right) \Leftrightarrow ((\operatorname{IsNormalized}\left(psi\right)) \land (\exists S \in \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)\right),\; (S \subseteq \operatorname{eigenphaseClifford}\left(d\right)) \land (\operatorname{invariantSubspace}\left(S\right) = \operatorname{span}\left(\mathbb{C}, \left\{psi\right\}\right)))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsCliffordStabilizerState` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

A normalized state is Clifford-stabilized when its complex line is exactly the pointwise fixed space of a subset of the eigenphase extension. This is the fixed-space formulation of the source's convention.

**Definition 1.10 (SIC fiducials).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall psi \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \operatorname{IsSICFiducial}\left(d, psi\right) \Leftrightarrow ((\operatorname{IsNormalized}\left(psi\right)) \land (\forall a \in \operatorname{ZMod}\left(d\right),\; \forall b \in \operatorname{ZMod}\left(d\right),\; ((a, b) \ne (0, 0)) \Rightarrow (\operatorname{norm}\left(\operatorname{inner}\left(psi, (\operatorname{displacement}\left(d, a, b\right)) \cdot (psi)\right)\right) = \frac{1}{\operatorname{sqrt}\left((d) + (1)\right)}))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsSICFiducial` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Every nonidentity displacement has overlap modulus one divided by the square root of d + 1. Multiplying a displacement by a unit-modulus phase preserves this condition.

**Definition 1.11 (The proposed stabilizer nature of SIC fiducials).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (\operatorname{Prime}\left(d\right)) \Rightarrow (\forall psi \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsSICFiducial}\left(d, psi\right)) \Rightarrow (\operatorname{IsCliffordStabilizerState}\left(d, psi\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.claim` (`✓ std3`).

*Citation.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The conjecture quantifies over all prime dimensions and all single-qudit SIC fiducials.

**Theorem 1.12 (Finiteness of the special qutrit Clifford group).**

$$\operatorname{Finite}\left(\operatorname{specialClifford}\left(3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.specialClifford_three_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Conjugating X and Z gives a pair of Pauli matrices, so there are finitely many such pairs. If U and V give the same pair, V adjoint times U commutes with both X and Z. The clock-and-shift commutant consists of scalar matrices. Determinant one forces that scalar to be a cube root of unity. Thus every fiber contains finitely many matrices.

**Theorem 1.13 (Finiteness of the eigenphase extension).**

$$\operatorname{Finite}\left(\operatorname{eigenphaseClifford}\left(3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.eigenphaseClifford_three_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

A finite-dimensional matrix has finitely many eigenvalues. Taking the union over the finite special Clifford group leaves Lambda finite, and taking scalar multiples from two finite sets leaves the extension finite.

**Theorem 1.14 (Finitely many Clifford-stabilizer projectors).**

$$\operatorname{Finite}\left(\{ P \mid \exists psi \in (\operatorname{ZMod}\left(3\right) \to \mathbb{C}),\; (\operatorname{IsCliffordStabilizerState}\left(3, psi\right)) \land (P = (psi) \cdot (\operatorname{adjoint}\left(psi\right))) \}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.stabilizer_projectors_three_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

There are finitely many subsets of the eigenphase extension. Each subset determines one fixed space. Two normalized vectors spanning the same complex line have the same rank-one projector, so the set of resulting projectors is finite.

**Definition 1.15 (The continuous qutrit family).**

$$\forall z \in \mathbb{C},\; \operatorname{qutritFiducial}\left(z\right) = \frac{(0, 1, -(z))}{\operatorname{sqrt}\left(2\right)}$$

*Formalization.* `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutritFiducial` (`✓ std3`).

*Citation.* Gelo Noel M. Tabia; D. M. Appleby (2013). *Exploring the geometry of qutrit state space using symmetric informationally complete probabilities*. DOI: [10.1103/PhysRevA.88.012131](https://doi.org/10.1103/PhysRevA.88.012131). URL: <https://arxiv.org/abs/1304.8075v2>.

*Commentary.*

For each complex parameter z, the column vector has amplitudes 0, 1 and -z, divided by the square root of two.

**Theorem 1.16 (A unit circle of SIC fiducials).**

$$\forall z \in \mathbb{C},\; (\operatorname{norm}\left(z\right) = 1) \Rightarrow (\operatorname{IsSICFiducial}\left(3, \operatorname{qutritFiducial}\left(z\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutritFiducial_isSIC` (`✓ std3`). ∎

*Citation.* Gelo Noel M. Tabia; D. M. Appleby (2013). *Exploring the geometry of qutrit state space using symmetric informationally complete probabilities*. DOI: [10.1103/PhysRevA.88.012131](https://doi.org/10.1103/PhysRevA.88.012131). URL: <https://arxiv.org/abs/1304.8075v2>.

*Commentary.*

For modulus-one z the vector is normalized. When a = 0 and b is nonzero, the overlap is -1/2 because 1 + omega + omega squared = 0. When a = 1 the overlap is -conjugate(z) omega to the power b divided by two; when a = 2 it is -z omega to the power 2b divided by two. Each has modulus 1/2, equal to one divided by the square root of 3 + 1. Tabia and Appleby state this family for z = e^{2it} with t in [0, pi/6]; the proof here covers every unit z by direct computation.

**Theorem 1.17 (Distinct parameters give distinct projectors).**

$$\forall z \in \mathbb{C},\; \forall w \in \mathbb{C},\; ((\operatorname{qutritFiducial}\left(z\right)) \cdot (\operatorname{adjoint}\left(\operatorname{qutritFiducial}\left(z\right)\right)) = (\operatorname{qutritFiducial}\left(w\right)) \cdot (\operatorname{adjoint}\left(\operatorname{qutritFiducial}\left(w\right)\right))) \Rightarrow (z = w)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutrit_projector_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The projector entry in row 1, column 2 is -conjugate(z)/2. Equality of projectors therefore forces equality of the parameters.

**Theorem 1.18 (Refutation in dimension three).**

$$\neg (\forall d \in \mathbb{N},\; (\operatorname{Prime}\left(d\right)) \Rightarrow (\forall psi \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsSICFiducial}\left(d, psi\right)) \Rightarrow (\operatorname{IsCliffordStabilizerState}\left(d, psi\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/erew-goldstein-2025-sic-clifford-stabilizer` (refuted) by `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erew-goldstein-2025-sic-clifford-stabilizer","declaration_gid":"D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The complex unit circle is infinite: its real-coordinate image contains the entire range of cosine. The qutrit family maps that circle injectively to pure-state projectors. If every SIC fiducial were Clifford-stabilized, this infinite image would be a subset of the finite set of Clifford-stabilizer projectors. Hence the conjecture is false, already in prime dimension three.

## References

- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsCliffordStabilizerState`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsNormalized`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.IsSICFiducial`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.Lambda`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.cliffordGroup`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.eigenphaseClifford`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.eigenphaseClifford_three_finite`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.invariantSubspace`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.pauliGroup`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutritFiducial`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutritFiducial_isSIC`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.qutrit_projector_injective`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.specialClifford`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.specialClifford_three_finite`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.stabilizer_projectors_three_finite`
- Truth anchor: `D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.zeta`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacement](../Algebra/WeylDisplacement.md)
