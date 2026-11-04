# Second-family data in every dimension

## Abstract

Cyclic translations supply the orthogonal matrices, difference labels, and sum-indexed shield vectors required for the second family in every dimension.

**Definition 1.1 (The nonzero label-fiber multiplicity).**

$$\forall (d: \mathbb{N}), (\forall (a: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (\mu: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right)))), (\forall (m: \operatorname{Fin}\left(d\right)), (\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.multiplicity}\left(a, \mu, m\right) = \operatorname{Fintype.card}\left(\operatorname{Subtype}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \lambda (p: \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \mapsto ((a\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right) \ne (0: \mathbb{R})) \land (\mu\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right) = m))\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.multiplicity` (`✓ std3`).

*Citation.* Pál, Károly F.; Tóth, Géza; Bene, Erika; Vértesi, Tamás (2021). *Bound entangled singlet-like states for quantum metrology*. DOI: [10.1103/PhysRevResearch.3.023101](https://doi.org/10.1103/PhysRevResearch.3.023101). URL: <https://arxiv.org/abs/2002.12409v4>.

*Commentary.*

For a natural dimension d, a real array a on pairs of Fin d and a label array μ on the same pairs, multiplicity a μ m is the finite cardinality of the subtype of pairs p whose value a p.1 p.2 is nonzero and whose label μ p.1 p.2 equals m. This is the number N_m of nonzero pairs in the m-th label fiber. The source introduces these fibers in TeX lines 606–614.

**Definition 1.2 (The label-indexed vector).**

$$\forall (d: \mathbb{N}), (\forall (a: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (\mu: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right)))), (\forall (m: \operatorname{Fin}\left(d\right)), (\forall (p: \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)), (\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.tVec}\left(a, \mu, m, p\right) = \operatorname{ite}\left(((a\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right) \ne (0: \mathbb{R})) \land (\mu\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right) = m)), \frac{(a\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right): \mathbb{C})}{(\operatorname{Real.sqrt}\left((d: \mathbb{R})\right): \mathbb{C})}, (0: \mathbb{C})\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.tVec` (`✓ std3`).

*Citation.* Pál, Károly F.; Tóth, Géza; Bene, Erika; Vértesi, Tamás (2021). *Bound entangled singlet-like states for quantum metrology*. DOI: [10.1103/PhysRevResearch.3.023101](https://doi.org/10.1103/PhysRevResearch.3.023101). URL: <https://arxiv.org/abs/2002.12409v4>.

*Commentary.*

For each label m, tVec a μ m is the complex-valued vector on pairs whose coordinate at p equals a p.1 p.2 divided by the square root of d, with both real quantities coerced to complex numbers, when that coefficient is nonzero and μ p.1 p.2=m; the coordinate is zero otherwise. This is the coordinate form of the vectors t_m in Definition 2, TeX lines 627–631.

**Definition 1.3 (The requirements for second-family data).**

$$\forall (d: \mathbb{N}), (\forall (q: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right))), (\forall (qbar: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (\mu: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right)))), (\forall (a: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (s: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \to (\mathbb{C}))), ((\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.IsSecondFamilyData}\left(d, q, qbar, \mu, a, s\right)) \Leftrightarrow ((\forall (j: \operatorname{Fin}\left(d\right)), ((\operatorname{Matrix.transpose}\left(q\left(j\right)\right)) \cdot (q\left(j\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)))) \land ((\forall (m: \operatorname{Fin}\left(d\right)), (\forall (n: \operatorname{Fin}\left(d\right)), (\sum_{(k: \operatorname{Fin}\left(d\right))} ((qbar\left(m, k\right)) \cdot (qbar\left(n, k\right))) = \operatorname{ite}\left((m = n), (1: \mathbb{R}), (0: \mathbb{R})\right)))) \land ((\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), (\forall (k: \operatorname{Fin}\left(d\right)), (q\left(k, i, j\right) = (a\left(i, j\right)) \cdot (qbar\left(\mu\left(i, j\right), k\right)))))) \land ((\forall (i: \operatorname{Fin}\left(d\right)), (\forall (j: \operatorname{Fin}\left(d\right)), ((a\left(i, j\right) \ne (0: \mathbb{R})) \Rightarrow ((a\left(i, j\right))^{2} = \frac{(d: \mathbb{R})}{(\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.multiplicity}\left(a, \mu, \mu\left(i, j\right)\right): \mathbb{R})})))) \land ((\forall (m: \operatorname{Fin}\left(d\right)), (\forall (n: \operatorname{Fin}\left(d\right)), (\sum_{(x: \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right))} ((\operatorname{star}\left(s\left(m, x\right)\right)) \cdot (s\left(n, x\right))) = \operatorname{ite}\left((m = n), (1: \mathbb{C}), (0: \mathbb{C})\right)))) \land (\operatorname{D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose}\left(\sum_{(m: \operatorname{Fin}\left(d\right))} (\operatorname{Matrix.vecMulVec}\left(s\left(m\right), \operatorname{star}\left(s\left(m\right)\right)\right))\right) = \sum_{(m: \operatorname{Fin}\left(d\right))} (\operatorname{Matrix.vecMulVec}\left(\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.tVec}\left(a, \mu, m\right), \operatorname{star}\left(\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.tVec}\left(a, \mu, m\right)\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.IsSecondFamilyData` (`✓ std3`).

*Citation.* Pál, Károly F.; Tóth, Géza; Bene, Erika; Vértesi, Tamás (2021). *Bound entangled singlet-like states for quantum metrology*. DOI: [10.1103/PhysRevResearch.3.023101](https://doi.org/10.1103/PhysRevResearch.3.023101). URL: <https://arxiv.org/abs/2002.12409v4>.

*Commentary.*

IsSecondFamilyData d q qbar μ a s collects the formal requirements of Definition 2. Every q j is orthogonal, the rows qbar m are orthonormal, and q k i j equals a i j times qbar (μ i j) k. Every nonzero coefficient has square d divided by the multiplicity of its label fiber. The vectors s m are orthonormal in the complex pair space, and the partial transpose of their projector sum equals the projector sum formed from tVec. These are the orthogonality, factorization, normalization, and shield requirements stated at TeX lines 567–571, 594–640.

The shield identity uses `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose`, the second-factor partial transpose: its entry at (p,q) is the input entry at ((p.1,q.2),(q.1,p.2)).

**Definition 1.4 (Existence of second-family data).**

$$(\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.claim}\left(\right)) \Leftrightarrow (\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \Rightarrow (\exists (q: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right))), (\exists (qbar: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\exists (\mu: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right)))), (\exists (a: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\exists (s: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \to (\mathbb{C}))), (\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.IsSecondFamilyData}\left(d, q, qbar, \mu, a, s\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.claim` (`✓ std3`).

*Citation.* Pál, Károly F.; Tóth, Géza; Bene, Erika; Vértesi, Tamás (2021). *Bound entangled singlet-like states for quantum metrology*. DOI: [10.1103/PhysRevResearch.3.023101](https://doi.org/10.1103/PhysRevResearch.3.023101). URL: <https://arxiv.org/abs/2002.12409v4>.

*Commentary.*

The claim asks for second-family data for every natural dimension d at least two, as in the source's question at TeX line 674. Its five witnesses are a family q of d real d-by-d matrices, a family qbar of d real vectors on Fin d, a label function μ on pairs, a real coefficient function a on pairs, and a family s of d complex vectors on pairs. The witnesses satisfy all six requirements of IsSecondFamilyData.

**Theorem 1.5 (Cyclic translations prove existence in every dimension).**

$$\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \Rightarrow (\exists (q: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right))), (\exists (qbar: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\exists (\mu: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right)))), (\exists (a: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\exists (s: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \to (\mathbb{C}))), (\operatorname{D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions.IsSecondFamilyData}\left(d, q, qbar, \mu, a, s\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.result` (`✓ std3`). ∎

*Resolves.* `Problems/pal-toth-bene-vertesi-2021-second-family-all-dimensions` (proved) by `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pal-toth-bene-vertesi-2021-second-family-all-dimensions","declaration_gid":"D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pál, Károly F.; Tóth, Géza; Bene, Erika; Vértesi, Tamás (2021). *Bound entangled singlet-like states for quantum metrology*. DOI: [10.1103/PhysRevResearch.3.023101](https://doi.org/10.1103/PhysRevResearch.3.023101). URL: <https://arxiv.org/abs/2002.12409v4>.

*Commentary.*

Fix d at least two. For each k in Fin d, let Qᵏ be the real permutation matrix of the cyclic shift i ↦ i+k on Fin d. The shift is Mathlib's permutation finCycle k; Equiv.Perm.permMatrix_mem_unitaryGroup gives unitarity, and real conjugation turns its adjoint identity into (Qᵏ)ᵀQᵏ=1.

Set μ i j to be the cyclic difference j−i in Fin d, set a i j=1, and let qbar m be the m-th coordinate vector. Thus Qᵏ i j is one exactly when j=i+k, equivalently k=μ i j, and the shift factorization says Qᵏ i j = a i j qbar (μ i j) k. The map i ↦ (i,i+m) parametrizes the m-th label fiber bijectively, so its multiplicity is d and the square law for a is d/d=1. The coordinate vectors qbar are orthonormal by a finite case split on their labels.

For these witnesses, tVec at label m has coefficient (sqrt d)⁻¹ on pairs with j−i=m and zero elsewhere. All sums and differences of pair coordinates are taken modulo d.

Define the shield vector at label m by the constant coefficient (sqrt d)⁻¹ on pairs with i+j=m in the cyclic group and zero elsewhere. Transport (i,j) to the two-coordinate residue string (i,−j) through ZMod.finEquiv d. The shield vector becomes the zero-frequency Fourier vector with sector label (0,−m). The shared sector_basis theorem in AbsolutePPT.Bipartite then proves orthonormality.

For the partial-transpose identity, evaluate both matrix sides at arbitrary pair indices p and q. After the pair-coordinate substitution, the shield side is nonzero exactly when q.1+p.2=p.1+q.2, which is equivalent in the cyclic group to q.2−q.1=p.2−p.1. That is exactly equality of the difference labels, so the resulting entry agrees with the sum of the tVec projectors. These constructions give the five witnesses and IsSecondFamilyData, proving the full quantified claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.IsSecondFamilyData`
- Truth anchor: `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.multiplicity`
- Truth anchor: `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.tVec`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](../AbsolutePPT/Bipartite.md)
