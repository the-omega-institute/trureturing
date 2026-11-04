# A strict gap for the noisy GHZ witness bound

## Abstract

The optimized GHZ witness bound is strictly below the geometric convex roof for three qutrits at noise three eighths.

Word (Fin d) n is the computational basis Fin n → Fin d. rankOneDensity ψ is the matrix with entries ψ(x) conjugate(ψ(y)); IsUnitState ψ means that the sum of Complex.normSq (ψ x) is one. readout A ψ is the real part of star ψ ⬝ᵥ (A *ᵥ ψ). Matrix multiplication, real scalar multiplication and finite sums have these types throughout. Nat.cast into ℝ and Complex.ofReal into ℂ display the scalar embeddings. Subtype.val displays the inclusion of a coordinate in a chosen part of a bipartition.

**Definition 1.1 (The GHZ amplitude).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ((\operatorname{ghz}\left(n, d\right): (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})) = (\lambda (x: \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \mapsto (if (\exists (j: \operatorname{Fin}\left(d\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (x\left(i\right) = j))) then \operatorname{Inv.inv}\left((\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left((\operatorname{Nat.cast}\left(d\right): \mathbb{R})\right)\right): \mathbb{C})\right) else (0: \mathbb{C})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.ghz` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, line 284, defines the equal superposition of the d constant words, divided by √d. The formula gives its amplitude at every computational word and defines it for all natural n and d.

**Definition 1.2 (Pure biseparability).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (\varphi: (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})), ((\operatorname{IsBiseparable}\left(\varphi\right)) \Leftrightarrow ((\operatorname{IsUnitState}\left(\varphi\right)) \land (\exists (a: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{Finset.Nonempty}\left(a\right)) \land ((\operatorname{Finset.Nonempty}\left(\operatorname{Compl.compl}\left(a\right)\right)) \land (\exists (u: ((\operatorname{Subtype}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (i \in a))\right)) \to (\operatorname{Fin}\left(d\right))) \to (\mathbb{C})), (\exists (v: ((\operatorname{Subtype}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (i \in \operatorname{Compl.compl}\left(a\right)))\right)) \to (\operatorname{Fin}\left(d\right))) \to (\mathbb{C})), (\forall (x: \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)), (\varphi\left(x\right) = u\left((\lambda (i: \operatorname{Subtype}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (i \in a))\right)) \mapsto (x\left(\operatorname{Subtype.val}\left(i\right)\right)))\right) \cdot v\left((\lambda (i: \operatorname{Subtype}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (i \in \operatorname{Compl.compl}\left(a\right)))\right)) \mapsto (x\left(\operatorname{Subtype.val}\left(i\right)\right)))\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.IsBiseparable` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

A unit vector is biseparable when its amplitudes factor across a nonempty proper set a of parties. The two factors are arbitrary complex functions on the coordinates in a and its complement. This expresses the pure biseparable states in GMEwitness.tex, lines 284 and 307–309.

**Definition 1.3 (The support projector).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ((\operatorname{supportProjector}\left(n, d\right): \operatorname{Matrix}\left(\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right)) = \operatorname{Matrix.diagonal}\left((\lambda (x: \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \mapsto (if (\operatorname{Finset.card}\left(\operatorname{Finset.image}\left(x, (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right) \le (2: \mathbb{N})) then (1: \mathbb{C}) else (0: \mathbb{C})))\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.supportProjector` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The diagonal entry is one exactly on words using at most two distinct symbols. These are the constant words and the distinct arrangements of two-symbol words in GMEwitness.tex, lines 690–699. The cardinality in the condition is natural-valued.

**Definition 1.4 (The GHZ witness operator).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ((\operatorname{witnessOp}\left(n, d\right): \operatorname{Matrix}\left(\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right)) = \operatorname{HSMul.hSMul}\left(\frac{1}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})}, \operatorname{supportProjector}\left(n, d\right)\right) - \operatorname{rankOneDensity}\left(\operatorname{ghz}\left(n, d\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.witnessOp` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, lines 295–300, gives one dth of the support projector minus the GHZ rank-one matrix. The coefficient is a real scalar; the natural dimension is cast to ℝ before division.

**Definition 1.5 (The noisy GHZ matrix).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (p: \mathbb{R}), ((\operatorname{noisyGhz}\left(n, d, p\right): \operatorname{Matrix}\left(\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right)) = \operatorname{HSMul.hSMul}\left(\frac{p}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{n}}, (1: \operatorname{Matrix}\left(\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right))\right) + \operatorname{HSMul.hSMul}\left(1 - p, \operatorname{rankOneDensity}\left(\operatorname{ghz}\left(n, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.noisyGhz` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, line 284, mixes white noise with the GHZ rank-one matrix. The identity has dimension dⁿ, and its coefficient is p/dⁿ. The definition accepts every real p; the probability restrictions occur in claim.

**Definition 1.6 (The witness expectation).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (p: \mathbb{R}), ((\operatorname{witnessValue}\left(n, d, p\right): \mathbb{R}) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{noisyGhz}\left(n, d, p\right) \cdot \operatorname{witnessOp}\left(n, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.witnessValue` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, line 301, defines the trace of the noisy GHZ matrix times the witness. The real part gives its real-valued expectation.

**Definition 1.7 (The pure geometric measure).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (\psi: (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})), ((\operatorname{geometricMeasurePure}\left(\psi\right): \mathbb{R}) = 1 - \operatorname{sSup}\left(\{(t: \mathbb{R}) | \exists (\varphi: (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})), ((\operatorname{IsBiseparable}\left(\varphi\right)) \land (t = \operatorname{Complex.normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\varphi\right), \psi\right)\right)))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.geometricMeasurePure` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, line 284, subtracts the largest squared biseparable overlap from one. Here sSup is the real supremum of the squared overlaps with all biseparable unit vectors.

**Definition 1.8 (The finite-ensemble convex roof).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right), \mathbb{C}\right)), ((\operatorname{geometricMeasure}\left(\rho\right): \mathbb{R}) = \operatorname{sInf}\left(\{(t: \mathbb{R}) | \exists (k: \mathbb{N}), (\exists (p: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\exists (\psi: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C}))), ((\forall (i: \operatorname{Fin}\left(k\right)), (0 \le p\left(i\right))) \land ((\sum_{i: \operatorname{Fin}\left(k\right)} (p\left(i\right)) = 1) \land ((\forall (i: \operatorname{Fin}\left(k\right)), (\operatorname{IsUnitState}\left(\psi\left(i\right)\right))) \land ((\rho = \sum_{i: \operatorname{Fin}\left(k\right)} (\operatorname{HSMul.hSMul}\left(p\left(i\right), \operatorname{rankOneDensity}\left(\psi\left(i\right)\right)\right))) \land (t = \sum_{i: \operatorname{Fin}\left(k\right)} (p\left(i\right) \cdot \operatorname{geometricMeasurePure}\left(\psi\left(i\right)\right)))))))))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.geometricMeasure` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, lines 284–288, extends the pure measure by the convex roof. The infimum here ranges over all finite ensembles: nonnegative real weights summing to one, unit pure vectors, and exact rank-one reconstruction of the matrix. The value averaged in each ensemble is the pure geometric measure.

**Definition 1.9 (The convex conjugate).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (r: \mathbb{R}), ((\operatorname{hatE}\left(n, d, r\right): \mathbb{R}) = \operatorname{sSup}\left(\{(t: \mathbb{R}) | \exists (\psi: (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})), (\exists (\varphi: (\operatorname{Word}\left(\operatorname{Fin}\left(d\right), n\right)) \to (\mathbb{C})), ((\operatorname{IsUnitState}\left(\psi\right)) \land ((\operatorname{IsBiseparable}\left(\varphi\right)) \land (t = \operatorname{readout}\left(\operatorname{HSMul.hSMul}\left(r, \operatorname{witnessOp}\left(n, d\right)\right) + \operatorname{rankOneDensity}\left(\varphi\right), \psi\right) - 1))))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.hatE` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, lines 305–309, takes both pure-state optimizations. The single supremum ranges over every unit ψ and every biseparable φ, of the expectation of r times the witness plus the φ rank-one matrix, minus one.

**Definition 1.10 (The optimized witness bound).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (p: \mathbb{R}), ((\operatorname{epsilonO}\left(n, d, p\right): \mathbb{R}) = \operatorname{sSup}\left(\{(t: \mathbb{R}) | \exists (r: \mathbb{R}), (t = r \cdot \operatorname{witnessValue}\left(n, d, p\right) - \operatorname{hatE}\left(n, d, r\right))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.epsilonO` (`✓ std3`).

*Citation.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, lines 301–305, optimizes r times the measured witness value minus the conjugate over every real slope r. The real supremum expresses this optimization.

**Definition 1.11 (The universal equality question).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ((3 \le n) \to ((3 \le d) \to (\forall (p: \mathbb{R}), ((0 \le p) \to ((p \le 1) \to (\operatorname{epsilonO}\left(n, d, p\right) = \operatorname{geometricMeasure}\left(\operatorname{noisyGhz}\left(n, d, p\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

GMEwitness.tex, line 325, asks whether the optimized witness bound equals the geometric measure of the noisy GHZ state. The displayed equality question quantifies over all natural n and d at least three and every real noise probability p between zero and one.

**Theorem 1.12 (Three qutrits give a strict gap).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/xu-et-al-2023-noisy-ghz-witness-bound-gap` (refuted) by `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"xu-et-al-2023-noisy-ghz-witness-bound-gap","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Take n = d = 3 and p = 3/8. Write G for the GHZ rank-one projector, P for the support projector and Q = I − P. Counting the computational words gives Tr(P) = 21 and Tr(Q) = 6. The GHZ vector is unit, P² = P, PG = GP = G and G² = G. Thus P − G and Q are positive semidefinite. Consequently ρ = I/72 + (5/8)G, W = P/3 − G and Tr(ρW) = −1/3.

The unit vector (4|000⟩ + |111⟩ + |222⟩)/√18 has P expectation one, G expectation 2/3, W expectation −1/3 and squared overlap 8/9 with |000⟩. The latter vector factors across the first party and the other two parties. For every unit vector the W expectation lies between −1 and 1/3, and every squared overlap of unit vectors is at most one. These estimates bound the set defining hatE at slope r above by |r|. The chosen pair belongs to this set and gives hatE(3,3,r) ≥ −r/3 − 1/9. The set defining epsilonO is nonempty by taking r = 0; each of its values is at most 1/9, so epsilonO(3,3,3/8) ≤ 1/9.

For any biseparable φ, let g be its G expectation and s its P expectation. Choose a nonempty proper cut on which φ factors as u times v. Cauchy–Schwarz bounds the squared sum of its three constant-word amplitudes by the product of the sums of the squared constant amplitudes of u and v. This product is the sum over the nine words constant on each side of the cut. Those nine words are distinct because both parts are nonempty, and each lies in the support of P. Their nonnegative squared amplitudes therefore sum to at most s. The squared constant-word sum equals 3g, proving 3g ≤ s.

Set B = −(2/3)W + Q/9, D = (2/3)G + (4/3)(P − G) + Q and T = (3/2)G + (3/4)(P − G) + Q. The inequality 3g ≤ s and normalization give ⟨φ,Tφ⟩ = 1 + (3g − s)/4 ≤ 1. Also D = (2/3)I + (2/3)(P − G) + Q/3 is positive definite, T is positive semidefinite, and the projector identities give DT = I. Apply the positive semidefinite Cauchy–Schwarz inequality for D to ψ and Tφ. Using DTφ = φ and the Hermitian symmetry of T gives |⟨φ,ψ⟩|² ≤ ⟨φ,Tφ⟩⟨ψ,Dψ⟩ ≤ ⟨ψ,Dψ⟩. There is a biseparable vector |000⟩, so taking the supremum over biseparable overlaps is legitimate. Since D + B = (10/9)I, every unit ψ satisfies geometricMeasurePure ψ ≥ ⟨ψ,Bψ⟩ − 1/9.

The relations GQ = 0 and Tr(Q) = 6 give Tr(ρQ) = 1/12. Hence Tr(ρB) − 1/9 = −(2/3)Tr(ρW) + Tr(ρQ)/9 − 1/9 = 13/108. The matrix ρ is positive semidefinite with trace one, so a finite spectral ensemble exists. For any such ensemble, the rank-one trace identity identifies the average of ⟨ψ,Bψ⟩ with Tr(ρB). Multiplying the pure bound by each nonnegative weight and summing yields an average geometric measure at least 13/108. Taking the infimum over the nonempty set of finite ensembles gives geometricMeasure ρ ≥ 13/108. The equality in claim at these parameters would imply 13/108 ≤ 1/9 = 12/108, a contradiction. No exact value of the convex roof is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.IsBiseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.epsilonO`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.geometricMeasure`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.geometricMeasurePure`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.ghz`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.hatE`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.noisyGhz`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.supportProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.witnessOp`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.witnessValue`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../../Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness](../GHZ/OddGhzTenSettingWitness.md)
- Dependency: [D5/S3/Quantum/Information/MultiEntropyPositivityRefutation](../../Information/MultiEntropyPositivityRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality](../../Measurement/DetectorSensorDickeOptimality.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneTraceBound](../../../Zeros/CriticalPoints/RankOneTraceBound.md)
