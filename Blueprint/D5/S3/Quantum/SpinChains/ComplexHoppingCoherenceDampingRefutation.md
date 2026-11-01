# Coherence damping fails for complex hopping

## Abstract

Complex hopping can increase parity-twisted ground-state coherences.

**Definition 1.1 (Occupation configurations).**

$$\forall N \in \mathbb{N},\; \operatorname{Fock}\left(N\right) = \left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Fock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fock(N) is the occupation basis of N ordered modes, with each occupation in Fin 2. The Hilbert space consists of complex functions on this basis and has dimension 2ᴺ. val takes the natural value of a finite index.

**Definition 1.2 (Operators on fermionic Fock space).**

$$\forall N \in \mathbb{N},\; \operatorname{Operator}\left(N\right) = \operatorname{Matrix}\left(\operatorname{Fock}\left(N\right), \operatorname{Fock}\left(N\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Operator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An operator is a complex matrix whose row and column labels are occupation configurations. Matrix multiplication and the conjugate transpose use this basis.

**Definition 1.3 (Jordan–Wigner annihilation).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall s \in \operatorname{Fock}\left(N\right),\; \forall t \in \operatorname{Fock}\left(N\right),\; \operatorname{annihilator}\left(j, s, t\right) = \operatorname{if} ((t\left(j\right) = 1) \land (s = \operatorname{update}\left(t, j, 0\right))) \operatorname{then} (-1)^{\sum_{i : \operatorname{Fin}\left(N\right), i < j} \operatorname{val}\left(t\left(i\right)\right)} \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.annihilator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry is nonzero precisely when mode j is occupied in the input t and the output s empties that mode. Its sign counts the occupied modes before j. update(t,j,0) changes only occupation j; the sum in the exponent is a natural-number sum.

**Definition 1.4 (Number-conserving quadratic Hamiltonians).**

$$\forall N \in \mathbb{N},\; \forall h \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; \operatorname{hamiltonian}\left(h\right) = \sum_{j : \operatorname{Fin}\left(N\right)} (\sum_{k : \operatorname{Fin}\left(N\right)} (h\left(j, k\right) \cdot ((\operatorname{annihilator}\left(j\right))^{\operatorname{dagger}} \cdot \operatorname{annihilator}\left(k\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix h acts on the single-particle space. Its second quantization sums creation at j followed by annihilation at k. The dagger denotes conjugate transpose; no Hermiticity assumption is needed to define this operator.

**Definition 1.5 (Unit Fock vectors).**

$$\forall N \in \mathbb{N},\; \forall v \in \operatorname{Fock}\left(N\right) \to \mathbb{C},\; \operatorname{Normalized}\left(v\right) \Leftrightarrow (\sum_{s : \operatorname{Fock}\left(N\right)} (\overline{v\left(s\right)} \cdot v\left(s\right)) = 1)$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of squared moduli is one. The bar denotes complex conjugation.

**Definition 1.6 (The real quadratic form).**

$$\forall N \in \mathbb{N},\; \forall H \in \operatorname{Operator}\left(N\right),\; \forall v \in \operatorname{Fock}\left(N\right) \to \mathbb{C},\; \operatorname{energy}\left(H, v\right) = \Re\left(\sum_{s : \operatorname{Fock}\left(N\right)} (\overline{v\left(s\right)} \cdot \sum_{t : \operatorname{Fock}\left(N\right)} (H\left(s, t\right) \cdot v\left(t\right)))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Energy is the real part of the quadratic form, defined for every operator. For a Hermitian operator it is the usual expectation value.

**Definition 1.7 (Variational ground states).**

$$\forall N \in \mathbb{N},\; \forall H \in \operatorname{Operator}\left(N\right),\; \forall v \in \operatorname{Fock}\left(N\right) \to \mathbb{C},\; \operatorname{IsGroundState}\left(H, v\right) \Leftrightarrow ((\operatorname{Normalized}\left(v\right)) \land (\forall w \in \operatorname{Fock}\left(N\right) \to \mathbb{C},\; (\operatorname{Normalized}\left(w\right)) \Rightarrow (\operatorname{energy}\left(H, v\right) \le \operatorname{energy}\left(H, w\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.IsGroundState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ground state is normalized and minimizes energy among all normalized Fock vectors. The comparison includes every particle-number sector.

**Definition 1.8 (Three adjacent blocks and their complement).**

$$\forall N \in \mathbb{N},\; \operatorname{AdjacentPartition}\left(N\right) = \{(l, a, b, d, r) : \mathbb{N}^{5} \mid N = l + (a + (b + (d + r)))\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.AdjacentPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five natural lengths are ordered left, A, B, D, right. The complement E consists of both outer blocks. The displayed set describes the structure's five lengths and its size equality; zero lengths are allowed. For a partition p, left(p), a(p), b(p), d(p), right(p) and size(p) denote its fields.

**Definition 1.9 (Joining occupation configurations).**

$$\forall N \in \mathbb{N},\; \forall p \in \operatorname{AdjacentPartition}\left(N\right),\; \forall l \in \operatorname{Fock}\left(\operatorname{left}\left(p\right)\right),\; \forall a \in \operatorname{Fock}\left(\operatorname{a}\left(p\right)\right),\; \forall b \in \operatorname{Fock}\left(\operatorname{b}\left(p\right)\right),\; \forall d \in \operatorname{Fock}\left(\operatorname{d}\left(p\right)\right),\; \forall r \in \operatorname{Fock}\left(\operatorname{right}\left(p\right)\right),\; \forall i \in \operatorname{Fin}\left(N\right),\; \operatorname{concatenate}\left(p, l, a, b, d, r, i\right) = \operatorname{append}\left(l, \operatorname{append}\left(a, \operatorname{append}\left(b, \operatorname{append}\left(d, r\right)\right)\right)\right)\left(\operatorname{cast}\left(\operatorname{size}\left(p\right), i\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.concatenate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

append joins finite vectors in the displayed order. cast(size(p),i) transports i along N = left(p) + (a(p) + (b(p) + (d(p) + right(p)))). Thus no occupation is permuted.

**Definition 1.10 (Tracing out the whole complement).**

$$\forall R \in \operatorname{Type},\; [\operatorname{Semiring}\left(R\right)] [\operatorname{Star}\left(R\right)], \forall N \in \mathbb{N},\; \forall p \in \operatorname{AdjacentPartition}\left(N\right),\; \forall v \in \operatorname{Fock}\left(N\right) \to R,\; \forall x \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times ((\operatorname{Fock}\left(\operatorname{b}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right))),\; \forall y \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times ((\operatorname{Fock}\left(\operatorname{b}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right))),\; \operatorname{reducedState}\left(p, v, x, y\right) = \sum_{l : \operatorname{Fock}\left(\operatorname{left}\left(p\right)\right)} (\sum_{r : \operatorname{Fock}\left(\operatorname{right}\left(p\right)\right)} (v\left(\operatorname{concatenate}\left(p, l, \operatorname{fst}\left(x\right), \operatorname{fst}\left(\operatorname{snd}\left(x\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(x\right)\right), r\right)\right) \cdot \operatorname{star}\left(v\left(\operatorname{concatenate}\left(p, l, \operatorname{fst}\left(y\right), \operatorname{fst}\left(\operatorname{snd}\left(y\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(y\right)\right), r\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.reducedState` (`✓ std3`).

*Citation.* Aleksandrs Sokolovs (2026). *Parity superselection obstructs monogamy of mutual information in free fermions*. URL: <https://arxiv.org/abs/2603.14154v2>.

*Commentary.*

The state on A, B and D is obtained from the outer product of the full vector by tracing over both components of E. Here star is the supplied scalar operation; the formula is defined over any semiring with a star operation and does not require normalization. For complex scalars it is the occupation-basis form of the source's reduced density matrix.

**Definition 1.11 (Particle number of a configuration).**

$$\forall N \in \mathbb{N},\; \forall s \in \operatorname{Fock}\left(N\right),\; \operatorname{occupation}\left(s\right) = \sum_{i : \operatorname{Fin}\left(N\right)} (\operatorname{val}\left(s\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.occupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total occupation is the natural sum of the zero-or-one occupations.

**Definition 1.12 (Ordinary spin partial trace).**

$$\forall R \in \operatorname{Type},\; [\operatorname{Semiring}\left(R\right)] [\operatorname{Star}\left(R\right)], \forall N \in \mathbb{N},\; \forall p \in \operatorname{AdjacentPartition}\left(N\right),\; \forall v \in \operatorname{Fock}\left(N\right) \to R,\; \forall x \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; \forall y \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; \operatorname{spinTrace}\left(p, v, x, y\right) = \sum_{b : \operatorname{Fock}\left(\operatorname{b}\left(p\right)\right)} (\operatorname{reducedState}\left(p, v, (\operatorname{fst}\left(x\right), b, \operatorname{snd}\left(x\right)), (\operatorname{fst}\left(y\right), b, \operatorname{snd}\left(y\right))\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.spinTrace` (`✓ std3`).

*Citation.* Aleksandrs Sokolovs (2026). *Parity superselection obstructs monogamy of mutual information in free fermions*. URL: <https://arxiv.org/abs/2603.14154v2>.

*Commentary.*

Section 3 defines the spin trace by summing the A,B,D matrix entries with the same B configuration on the bra and ket. The formula retains the source's order of the A and D indices and is defined over any semiring with a star operation.

**Definition 1.13 (Partial trace with the B-parity insertion).**

$$\forall R \in \operatorname{Type},\; [\operatorname{Ring}\left(R\right)] [\operatorname{Star}\left(R\right)], \forall N \in \mathbb{N},\; \forall p \in \operatorname{AdjacentPartition}\left(N\right),\; \forall v \in \operatorname{Fock}\left(N\right) \to R,\; \forall x \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; \forall y \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; \operatorname{twistedTrace}\left(p, v, x, y\right) = \sum_{b : \operatorname{Fock}\left(\operatorname{b}\left(p\right)\right)} ((-1)^{\operatorname{occupation}\left(b\right)} \cdot \operatorname{reducedState}\left(p, v, (\operatorname{fst}\left(x\right), b, \operatorname{snd}\left(x\right)), (\operatorname{fst}\left(y\right), b, \operatorname{snd}\left(y\right))\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.twistedTrace` (`✓ std3`).

*Citation.* Aleksandrs Sokolovs (2026). *Parity superselection obstructs monogamy of mutual information in free fermions*. URL: <https://arxiv.org/abs/2603.14154v2>.

*Commentary.*

Section 3 defines the parity-twisted trace as tr_B[(-1)ᴺᴮ ρ_ABD]. The factor is determined by the B occupation in the row; tracing identifies the row and column B labels. The scalar domain is any ring with a star operation. On D-parity-changing entries this is the fermionic trace in the source's factorization.

**Definition 1.14 (The proposed extension to complex hopping).**

$$\operatorname{claim} \Leftrightarrow (\forall N \in \mathbb{N},\; \forall h \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; ((h)^{\operatorname{dagger}} = h) \Rightarrow (\forall v \in \operatorname{Fock}\left(N\right) \to \mathbb{C},\; (\operatorname{IsGroundState}\left(\operatorname{hamiltonian}\left(h\right), v\right)) \Rightarrow (\forall p \in \operatorname{AdjacentPartition}\left(N\right),\; \forall x \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; \forall y \in (\operatorname{Fock}\left(\operatorname{a}\left(p\right)\right)) \times (\operatorname{Fock}\left(\operatorname{d}\left(p\right)\right)),\; (\operatorname{mod}\left(\operatorname{occupation}\left(\operatorname{snd}\left(x\right)\right), 2\right) \ne \operatorname{mod}\left(\operatorname{occupation}\left(\operatorname{snd}\left(y\right)\right), 2\right)) \Rightarrow (\left\lVert \operatorname{twistedTrace}\left(p, v, x, y\right) \right\rVert \le \left\lVert \operatorname{spinTrace}\left(p, v, x, y\right) \right\rVert))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aleksandrs Sokolovs (2026). *Parity superselection obstructs monogamy of mutual information in free fermions*. URL: <https://arxiv.org/abs/2603.14154v2>.

*Commentary.*

Theorem 1 gives coherence damping for ground states with real non-positive hopping. Section 7 asks whether it extends to complex hopping or frustrated lattices. The displayed proposition is the modulus version for all Hermitian complex single-particle matrices: every ground state, every adjacent partition, and every pair whose D occupations have different parity. Here mod denotes natural-number remainder (the Lean % operation). It does not impose the nonnegative-amplitude hypothesis behind the source's equality between an ordinary entry and its modulus.

**Theorem 1.15 (A four-mode ground-state counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sokolovs-2026-complex-hopping-coherence-damping-refutation` (refuted) by `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sokolovs-2026-complex-hopping-coherence-damping-refutation","declaration_gid":"D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aleksandrs Sokolovs (2026). *Parity superselection obstructs monogamy of mutual information in free fermions*. URL: <https://arxiv.org/abs/2603.14154v2>.

*Commentary.*

Take four ordered modes labelled 0,1,2,3 and the Hermitian matrix h = (1/50)[[14, -9+16i, -48, -12-12i], [-9-16i, 14, -12+12i, -48], [-48, -12-12i, -14, -16+9i], [-12+12i, -48, -16-9i, -14]]. Let U = (1/√50)[[3,3,4,4], [3,-3,4,-4], [4,-4i,-3,3i], [4,4i,-3,-3i]]. Then UU† = U†U = I and h = U† diag(-3/2,-1/2,1/2,3/2) U. For cⱼ = annihilator(j), set dₖ = Σⱼ Uₖⱼ cⱼ. These are canonical fermionic modes.

The normalized Slater state is ψ = ((3c₀†+4c₂†)/5)((3c₁†+4c₃†)/5)|0000⟩ = (9|1100⟩ + 12|1001⟩ - 12|0110⟩ + 16|0011⟩)/25. It fills the two negative-energy modes, since the two occupied orbitals are (d₀†+d₁†)/√2 and (d₀†-d₁†)/√2. Its squared norm is (81+144+144+256)/625 = 1. Writing H = hamiltonian(h), the identity H+2I = (3/2)d₀d₀† + (1/2)d₁d₁† + (1/2)d₂†d₂ + (3/2)d₃†d₃ is a sum of positive semidefinite matrices. Each factor annihilates ψ: d₀†ψ = d₁†ψ = d₂ψ = d₃ψ = 0. Hence Hψ = -2ψ and every normalized φ has energy at least -2. This proves minimality on the entire Fock space.

Choose A={0}, B={1}, D={2} and E={3}, so the five block lengths are (0,1,1,1,1). For the A,D configurations x=(0,1) and y=(1,0), the D occupations have opposite parity. After tracing out E, the B=0 contribution to this entry is 192/625 and the B=1 contribution is -108/625. Thus spinTrace(p,ψ)(x,y) = 84/625, whereas twistedTrace(p,ψ)(x,y) = 300/625 = 12/25. Both entries are real and positive, and 12/25 > 84/625. The parity insertion reverses the negative contribution and increases the coherence instead of damping it. This construction answers the complex-hopping extension asked in Section 7; it does not contradict the real non-positive-hopping theorem.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.AdjacentPartition`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Fock`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.IsGroundState`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Normalized`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.Operator`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.annihilator`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.concatenate`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.energy`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.hamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.occupation`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.reducedState`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.spinTrace`
- Truth anchor: `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.twistedTrace`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation](../QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression](SupersymmetricFermion/HardCoreCompression.md)
