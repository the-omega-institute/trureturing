# Overlapping pairs refute the twirling phase index formula

## Abstract

Three characters of C3 with multiplicity two contradict the proposed twirling phase index formula.

**Theorem 1.1 (The squared two-coordinate scale).**

$$\operatorname{Complex}.\operatorname{normSq} (\sqrt{2}^{-1}) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.scale_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal of the positive real square root of two is regarded as a complex scalar. Its squared complex modulus is one half.

All vector and matrix coordinates are complex. Fin indices start at zero. Matrix.vecMulVec(x, star(x)) is the rank-one state of x. Anonymous brackets display Lean typeclass assumptions; val displays a unitary matrix's coercion. Natural suprema and infima encode the extremal dimensions and frame lengths. The finite-group conjecture is implied by the source's compact-group conjecture.

**Definition 1.2 (The finite twirling channel).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] \forall I \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall pi \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (I, \mathbb{C}),\; \forall X \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \operatorname{twirl}\left(pi, X\right) = (\operatorname{Fintype}.\operatorname{card} (G)^{-1} : \mathbb{C}) \cdot \sum_{g : G} (\operatorname{val}\left(pi (g)\right) \cdot X \cdot \operatorname{star}\left(\operatorname{val}\left(pi (g)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.twirl` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 3: “We define a linear map Φ<sub>π, σ</sub>: B(K, H) → B(K, H) by Φ<sub>π, σ</sub>(T) = ∫<sub>G</sub>π(g)Tσ(g<sup>−1</sup>) dμ(g) and denote Φ<sub>π, σ</sub> by Φ<sub>π</sub> when π = σ.” For finite G normalized Haar integration is the uniform average. pi is a group homomorphism into Matrix.unitaryGroup. Unitarity makes the inverse equal to star. I indexes the coordinate space.

**Definition 1.3 (Phase retrievable subspaces).**

$$\forall I \in \operatorname{Type}\left(\right),\; \forall Phi \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right) \to \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \forall M \in \operatorname{Submodule}\left(\mathbb{C}, I \to \mathbb{C}\right),\; \operatorname{PhaseRetrievable}\left(Phi, M\right) \Leftrightarrow \left(\forall x \in I \to \mathbb{C},\; x \in M \Rightarrow \left(\forall y \in I \to \mathbb{C},\; y \in M \Rightarrow \left(Phi (\operatorname{Matrix}.\operatorname{vecMulVec} (x, \operatorname{star}\left(x\right))) = Phi (\operatorname{Matrix}.\operatorname{vecMulVec} (y, \operatorname{star}\left(y\right))) \Rightarrow \operatorname{Matrix}.\operatorname{vecMulVec} (x, \operatorname{star}\left(x\right)) = \operatorname{Matrix}.\operatorname{vecMulVec} (y, \operatorname{star}\left(y\right))\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.PhaseRetrievable` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 5: “A subspace M of H is called phase retrievable under Φ if Φ is pure state injective on M, i.e., Φ(x⊗x) = Φ(y⊗y) implies that x⊗x = y⊗y for x, y∈M, or equivalently if there exists a POVM {F<sub>j</sub>}<sub>j∈𝕁</sub> in B(K) such that {P<sub>M</sub>Φ<sup>*</sup>(F<sub>j</sub>)P<sub>M</sub>}<sub>j∈𝕁</sub> is a phase retrievable operator valued frame for M, where P<sub>M</sub> is the orthogonal projection onto M.” The encoding uses the pure-state-injectivity clause. Phi maps square matrices, M is a complex submodule, and x and y range over every member of M, with no normalization restriction.

**Definition 1.4 (The phase retrievability index).**

$$\forall I \in \operatorname{Type}\left(\right),\; \forall Phi \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right) \to \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \operatorname{pr}\left(Phi\right) = \operatorname{sSup}\left(\ \{k : \mathbb{N} \mid \exists M \in \operatorname{Submodule}\left(\mathbb{C}, I \to \mathbb{C}\right),\; \operatorname{Module}.\operatorname{finrank} (\mathbb{C}, M) = k \land \operatorname{PhaseRetrievable}\left(Phi, M\right)\ \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.pr` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 5: “The phase retrievability index pr(Φ<sub>π</sub>) is defined to be the largest integer k such that there exits a k-dimensional subspace M⊂H such that M is phase retrievable under Φ.” The spelling exits is retained. k is a natural dimension, finrank is over Complex, and the supremum is over dimensions of all phase retrievable subspaces.

**Definition 1.5 (Correctable codes).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall I \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall pi \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (I, \mathbb{C}),\; \forall M \in \operatorname{Submodule}\left(\mathbb{C}, I \to \mathbb{C}\right),\; \operatorname{IsCode}\left(pi, M\right) \Leftrightarrow \left(\exists P \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \operatorname{star}\left(P\right) = P \land \left(P \cdot P = P \land \left(\operatorname{LinearMap}.\operatorname{range} (\operatorname{Matrix}.\operatorname{mulVecLin} (P)) = M \land \left(\exists c \in G \to \left(G \to \mathbb{C}\right),\; \forall g \in G,\; \forall h \in G,\; P \cdot \operatorname{star}\left(\operatorname{val}\left(pi (g)\right)\right) \cdot \operatorname{val}\left(pi (h)\right) \cdot P = c (g, h) \cdot P\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.IsCode` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 5, Lemma 3.1: “Let 𝒞 be a subspace of H, and let P be the orthogonal projections onto 𝒞. Suppose Φ is a quantum channel with Kraus operators {E<sub>i</sub>}<sub>i=1</sub><sup>r</sup>. Then the following are equivalent:” Its first two items read: “(i) 𝒞 is a quantum code for Φ. (ii) there exists a Hermitian matrix A = [a<sub>ij</sub>] such that PE<sub>i</sub><sup>*</sup>E<sub>j</sub>P = a<sub>ij</sub>P holds for all i, j.” The encoding takes the Knill–Laflamme clause for the Kraus family pi(g)/sqrt(card G). The common normalization is absorbed into c. A self-adjoint idempotent with range M is its orthogonal projection. The compression scalars are automatically Hermitian for a nonzero code; for the zero code they may be chosen zero.

**Definition 1.6 (The code dimension index).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall I \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall pi \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (I, \mathbb{C}),\; \operatorname{beta}\left(pi\right) = \operatorname{sSup}\left(\ \{k : \mathbb{N} \mid \exists M \in \operatorname{Submodule}\left(\mathbb{C}, I \to \mathbb{C}\right),\; \operatorname{Module}.\operatorname{finrank} (\mathbb{C}, M) = k \land \operatorname{IsCode}\left(pi, M\right)\ \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.beta` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 2: “β(Φ<sub>π</sub>) = max{m<sub>1</sub>, ... , m<sub>d</sub>} is the largest number m such that there exists a quantum code of dimension m.” Theorem 3.4, page 7, proves the equality. Here beta(pi) denotes beta of the induced twirling channel, as the supremum of the finranks of the IsCode subspaces.

**Definition 1.7 (Minimal complex frame length).**

$$\forall k \in \mathbb{N},\; \operatorname{frameLength}\left(k\right) = \operatorname{sInf}\left(\ \{n : \mathbb{N} \mid \exists f \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(k\right) \to \mathbb{C}\right),\; \forall x \in \operatorname{Fin}\left(k\right) \to \mathbb{C},\; \forall y \in \operatorname{Fin}\left(k\right) \to \mathbb{C},\; \left(\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{norm}\left(\operatorname{dotProduct}\left(x, \operatorname{star}\left(f (j)\right)\right)\right) = \operatorname{norm}\left(\operatorname{dotProduct}\left(y, \operatorname{star}\left(f (j)\right)\right)\right)\right) \Rightarrow \operatorname{Matrix}.\operatorname{vecMulVec} (x, \operatorname{star}\left(x\right)) = \operatorname{Matrix}.\operatorname{vecMulVec} (y, \operatorname{star}\left(y\right))\ \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.frameLength` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 4: “For an n-dimensional Hilbert space H, we will use ℐ<sub>n</sub> to denote the smallest integer N such that there is a phase retrievable frame {x<sub>j</sub>}<sub>j=1</sub><sup>N</sup> for H.” k is the source's n, and n is the family's length N. f has n vectors in Fin k to Complex. The norms of the complex dotProducts are their magnitudes. A retrieving family spans: a nonzero vector orthogonal to the family would collide with zero. No additional frame condition changes the family of admissible lengths.

**Definition 1.8 (Nonzero irreducible representations).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall n \in \mathbb{N},\; \forall rho \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin}\left(n\right), \mathbb{C}),\; \operatorname{Irreducible}\left(rho\right) \Leftrightarrow \left(0 < n \land \left(\forall M \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{Fin}\left(n\right) \to \mathbb{C}\right),\; \left(\forall g \in G,\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; x \in M \Rightarrow \operatorname{Matrix}.\operatorname{mulVec} (\operatorname{val}\left(rho (g)\right), x) \in M\right) \Rightarrow \left(M = \operatorname{Bot}.\operatorname{bot} \lor M = \operatorname{Top}.\operatorname{top}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.Irreducible` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 2: “A representation π is called irreducible if 0 and H are the only invariant subspaces.” rho acts on Fin n to Complex. The dimension is positive, as required for an irreducible representation. Every invariant submodule equals bottom or top.

**Definition 1.9 (No invertible intertwiner).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall rho \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin}\left(n\right), \mathbb{C}),\; \forall sigma \in G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin}\left(k\right), \mathbb{C}),\; \operatorname{Inequivalent}\left(rho, sigma\right) \Leftrightarrow \left(\neg \left(\exists T \in \operatorname{Fin}\left(n\right) \to \mathbb{C} \equiv{}_{l[\mathbb{C}]} \operatorname{Fin}\left(k\right) \to \mathbb{C},\; \forall g \in G,\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; T (\operatorname{Matrix}.\operatorname{mulVec} (\operatorname{val}\left(rho (g)\right), x)) = \operatorname{Matrix}.\operatorname{mulVec} (\operatorname{val}\left(sigma (g)\right), T (x))\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.Inequivalent` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 2: “where m<sub>i</sub>∈ℕ and π<sub>1</sub>, ... , π<sub>d</sub> are inequivalent irreducible unitary representations of G acting on Hilbert spaces H<sub>1</sub>, ... , H<sub>d</sub>, respectively.” rho and sigma are inequivalent when there is no complex-linear equivalence intertwining every group element. This is the finite-dimensional unitary equivalence convention.

**Definition 1.10 (The multiplicity decomposition).**

$$\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] \forall d \in \mathbb{N},\; \forall n \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall rho \in \left(\forall i \in \operatorname{Fin}\left(d\right),\; G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin}\left(n (i)\right), \mathbb{C})\right),\; \forall m \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall g \in G,\; (\operatorname{val}\left(\operatorname{blockRep}\left(rho, m\right) (g)\right) : \operatorname{Matrix}\left(\Sigma{}_{i : \operatorname{Fin}\left(d\right)} (\operatorname{Fin}\left(m (i)\right) \times \operatorname{Fin}\left(n (i)\right)), \Sigma{}_{i : \operatorname{Fin}\left(d\right)} (\operatorname{Fin}\left(m (i)\right) \times \operatorname{Fin}\left(n (i)\right)), \mathbb{C}\right)) = \operatorname{Matrix}.\operatorname{blockDiagonal}' (fun (i : \operatorname{Fin}\left(d\right)) \mapsto \operatorname{Matrix}.\operatorname{kronecker} ((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(m (i)\right), \operatorname{Fin}\left(m (i)\right), \mathbb{C}\right)), \operatorname{val}\left(rho (i, g)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.blockRep` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 2 displays U pi(g) U star = m1 pi1 direct-sum ... direct-sum md pid and states: “where m<sub>i</sub>∈ℕ and π<sub>1</sub>, ... , π<sub>d</sub> are inequivalent irreducible unitary representations of G acting on Hilbert spaces H<sub>1</sub>, ... , H<sub>d</sub>, respectively.” blockRep(rho,m) is the homomorphism with blocks Matrix.kronecker(1,val(rho(i,g))). The dependent index has a block label, a multiplicity coordinate and an irreducible coordinate. The displayed expression binds the complete family n and m.

**Definition 1.11 (The final conjecture of Section 5).**

$$claim \Leftrightarrow \left(\forall G \in \operatorname{Type}\left(\right),\; [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] \forall d \in \mathbb{N},\; \forall n \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall m \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall rho \in \left(\forall i \in \operatorname{Fin}\left(d\right),\; G \to^{*} \operatorname{Matrix}.\operatorname{unitaryGroup} (\operatorname{Fin}\left(n (i)\right), \mathbb{C})\right),\; \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{Irreducible}\left(rho (i)\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; i \ne j \Rightarrow \operatorname{Inequivalent}\left(rho (i), rho (j)\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; 1 \le m (i)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; \operatorname{frameLength}\left(k\right) \le d \Rightarrow \left(d < \operatorname{frameLength}\left(k + 1\right) \Rightarrow \operatorname{pr}\left(\operatorname{twirl}\left(\operatorname{blockRep}\left(rho, m\right)\right)\right) = \operatorname{max}\left(\operatorname{beta}\left(\operatorname{blockRep}\left(rho, m\right)\right), k\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.claim` (`✓ std3`).

*Citation.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Page 13: “Conjecture. Let π = m<sub>1</sub>π<sub>1</sub>⊕ ... ⊕ m<sub>d</sub>π<sub>d</sub> be a unitary representation of G such that π<sub>i</sub> and π<sub>j</sub> are inequivalent irreducible representations for all i≠j and ℐ<sub>k</sub> ≤ d < ℐ<sub>k+1</sub>. Then pr(Φ<sub>π</sub>) = max {β(Φ<sub>π</sub>), k}.” The encoding quantifies finite groups G, the number d of pairwise inequivalent irreducibles, their dimensions n, positive multiplicities m and the frame-length index k. The source's one-based summand labels become Fin d. The finite-group specialization is sufficient for a refutation of the compact-group assertion.

**Theorem 1.12 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-liu-2023-twirling-phase-retrievability` (refuted) by `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-liu-2023-twirling-phase-retrievability","declaration_gid":"D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Deguang Han and Kai Liu (2023). *Zero-Error Correctibility and Phase Retrievability for Twirling Channels*. DOI: [10.1016/S0034-4877(24)00012-0](https://doi.org/10.1016/S0034-4877(24)00012-0). URL: <https://arxiv.org/abs/2311.16349v1>.

*Commentary.*

Take G = Multiplicative(ZMod(3)), the three one-dimensional characters, d = 3 and every multiplicity equal to two. Character orthogonality identifies the twirl with three-block pinching. The isometric map (u,v,w) to ((u,v),(u,w),(v,w))/sqrt(2) places every entry of a three by three operator in a surviving two by two compression. Its range is phase retrievable, giving pr at least three. Knill–Laflamme compressions force every code to inject into a block of dimension two, and a whole block attains that dimension. One frame vector retrieves the complex one-dimensional space; three vectors cannot retrieve the two-dimensional space, whereas four can. Thus k = 1 and max(beta,k) = 2. The three-vector obstruction uses real rank-nullity to construct nonzero x and y for which x+y and x-y have equal measurements but different rank-one states. The rectangular matrix uses Matrix.conjTranspose, while square matrices use star. The multiplicity-one character case is compatible with this counterexample, as are the source's code formula and lower bounds.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.Inequivalent`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.Irreducible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.IsCode`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.PhaseRetrievable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.beta`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.blockRep`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.frameLength`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.pr`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.scale_normSq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.twirl`
