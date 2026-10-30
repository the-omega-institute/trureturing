# A non-extreme minimum-rank superchannel extension

## Abstract

A two-qubit quantum superchannel has reduced Choi rank four for every extension and a minimizing extension that is a midpoint of distinct extensions.

**Definition 1.1 (The span of quantum channels).**

$$\forall (d: \mathbb{N}), \forall (r: \mathbb{N}), SCPTP\left(d, r\right) = \operatorname{Submodule.span}\left(\mathbb{C}, \{phi: MatrixMap\left(Fin\left(d\right), Fin\left(r\right), \mathbb{C}\right) \Vert (\operatorname{MatrixMap.IsCompletelyPositive}\left(phi\right)) \land (\forall (X: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), (phi\left(X\right)).trace = (X).trace)\}\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.SCPTP` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Definition 3.1, page 3: "Given positive integers d, r ≥ 1 define SCPTP(d, r) := span{φ | φ : M_d → M_r is a CPTP map} ⊂ L(M_d, M_r). Also define S(d, r) ⊂ M_d(M_r) to be the set of block matrices (P_{i,j}) such that for all 1 ≤ i, j ≤ d, Tr(P_{i,i}) = Tr(P_{j,j}) and for i ≠ j Tr(P_{i,j}) = 0." The complex span is formed in MatrixMap, whose elements are complex-linear matrix maps. Complete positivity is MatrixMap.IsCompletelyPositive; trace preservation is stated for every input matrix. Fin n indices start at zero.

**Definition 1.2 (The bilinear tensor product of matrix maps).**

$$\forall (A: Type), \forall (B: Type), \forall (C: Type), \forall (D: Type), [Fintype\left(A\right)] [DecidableEq\left(A\right)] [Fintype\left(B\right)] [Fintype\left(C\right)] [DecidableEq\left(C\right)] [Fintype\left(D\right)] \forall (phi: MatrixMap\left(A, B, \mathbb{C}\right)), \forall (psi: MatrixMap\left(C, D, \mathbb{C}\right)), kronBilin\left(phi, psi\right) = \operatorname{MatrixMap.kron}\left(phi, psi\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.kronBilin` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Remark 3.3, page 4: "A tensor product of linear maps gives a map on the tensor product of the spaces so there is an inclusion". The bilinear map is LinearMap.mk₂ applied to MatrixMap.kron, with its additive and scalar laws. The displayed equality specifies its value on every pair of maps.

**Definition 1.3 (The tensor-product lift).**

$$\forall (A: Type), \forall (B: Type), \forall (C: Type), \forall (D: Type), [Fintype\left(A\right)] [DecidableEq\left(A\right)] [Fintype\left(B\right)] [Fintype\left(C\right)] [DecidableEq\left(C\right)] [Fintype\left(D\right)] (kronLift: (TensorProduct\left(\mathbb{C}, MatrixMap\left(A, B, \mathbb{C}\right), MatrixMap\left(C, D, \mathbb{C}\right)\right)) \to_{\mathbb{C}} (MatrixMap\left(A \times C, B \times D, \mathbb{C}\right))) = \operatorname{TensorProduct.lift}\left(kronBilin\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.kronLift` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Remark 3.3, page 4: "A tensor product of linear maps gives a map on the tensor product of the spaces so there is an inclusion". TensorProduct.lift applies the bilinear map kronBilin to arbitrary tensors, including sums of elementary tensors.

**Definition 1.4 (Quantum superchannels on channel spans).**

$$\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), \forall (Gamma: (SCPTP\left(d1, r1\right)) \to_{\mathbb{C}} (SCPTP\left(d2, r2\right))), IsQSC\left(Gamma\right) = \left((\forall (phi: SCPTP\left(d1, r1\right)), ((\operatorname{MatrixMap.IsCompletelyPositive}\left(val\left(phi\right)\right)) \land (\forall (X: Matrix\left(Fin\left(d1\right), Fin\left(d1\right), \mathbb{C}\right)), (val\left(phi\right)\left(X\right)).trace = (X).trace)) \Rightarrow ((\operatorname{MatrixMap.IsCompletelyPositive}\left(val\left(Gamma\left(phi\right)\right)\right)) \land (\forall (X: Matrix\left(Fin\left(d2\right), Fin\left(d2\right), \mathbb{C}\right)), (val\left(Gamma\left(phi\right)\right)\left(X\right)).trace = (X).trace))) \land (\forall (d3: \mathbb{N}), \forall (r3: \mathbb{N}), \forall (t: TensorProduct\left(\mathbb{C}, SCPTP\left(d1, r1\right), SCPTP\left(d3, r3\right)\right)), (\operatorname{MatrixMap.IsCompletelyPositive}\left(kronLift\left(\operatorname{TensorProduct.map}\left((SCPTP\left(d1, r1\right)).subtype, (SCPTP\left(d3, r3\right)).subtype, t\right)\right)\right)) \Rightarrow (\operatorname{MatrixMap.IsCompletelyPositive}\left(kronLift\left(\operatorname{TensorProduct.map}\left((SCPTP\left(d2, r2\right)).subtype, (SCPTP\left(d3, r3\right)).subtype, \operatorname{TensorProduct.map}\left(Gamma, \operatorname{LinearMap.id}, t\right)\right)\right)\right)))\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQSC` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Definition 3.4, page 5: "Given two spaces of quantum channels SCPTP(d_i, r_i), i = 1, 2, a QSC is a linear map Γ : SCPTP(d_1, r_1) → SCPTP(d_2, r_2) which satisfies (1) if φ is CPTP then Γ(φ) is CPTP (2) given any other dimensions d_3, r_3 ∈ ℕ and the identity map id_{d_3,r_3} : SCPTP(d_3, r_3) → SCPTP(d_3, r_3) then Γ⊗id_{d_3,r_3} : SCPTP(d_1, r_1)⊗SCPTP(d_3, r_3) → SCPTP(d_2, r_2)⊗SCPTP(d_3, r_3) sends CP maps to CP maps." Subtype.val includes the span into the full map space, and TensorProduct.map includes both tensor factors. The second condition ranges over every auxiliary dimension and every tensor.

**Definition 1.5 (Superchannels on full map spaces).**

$$\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), \forall (S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), IsQuantumSuperchannel\left(S\right) = \left((\forall (phi: MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)), (\operatorname{MatrixMap.IsCompletelyPositive}\left(phi\right)) \Rightarrow (\operatorname{MatrixMap.IsCompletelyPositive}\left(S\left(phi\right)\right))) \land ((\forall (d: \mathbb{N}), \forall (r: \mathbb{N}), \forall (t: TensorProduct\left(\mathbb{C}, MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right), MatrixMap\left(Fin\left(d\right), Fin\left(r\right), \mathbb{C}\right)\right)), (\operatorname{MatrixMap.IsCompletelyPositive}\left(kronLift\left(t\right)\right)) \Rightarrow (\operatorname{MatrixMap.IsCompletelyPositive}\left(kronLift\left(\operatorname{TensorProduct.map}\left(S, \operatorname{LinearMap.id}, t\right)\right)\right))) \land (\forall (phi: MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)), (\forall (X: Matrix\left(Fin\left(d1\right), Fin\left(d1\right), \mathbb{C}\right)), (phi\left(X\right)).trace = (X).trace) \Rightarrow (\forall (X: Matrix\left(Fin\left(d2\right), Fin\left(d2\right), \mathbb{C}\right)), (S\left(phi\right)\left(X\right)).trace = (X).trace)))\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQuantumSuperchannel` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Remark 3.7, page 6: "a quantum superchannel is a linear map S : L(M_{d_1}, M_{r_1}) → L(M_{d_2}, M_{r_2}) which satisfies • CP preserving: S sends CP maps to CP maps • Completely CP preserving: For any d, r if id_{d,r} is the identity map acting on L(M_d, M_r) then S ⊗ id_{d,r} is CP preserving • TP preserving: S sends TP maps to TP maps" All three clauses concern the full complex-linear map spaces; the last clause applies to every trace-preserving input, without a positivity hypothesis.

**Definition 1.6 (The set of extensions).**

$$\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), \forall (Gamma: (SCPTP\left(d1, r1\right)) \to_{\mathbb{C}} (SCPTP\left(d2, r2\right))), extensions\left(Gamma\right) = \{S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right)) \Vert (IsQuantumSuperchannel\left(S\right)) \land (\forall (phi: SCPTP\left(d1, r1\right)), S\left(val\left(phi\right)\right) = val\left(Gamma\left(phi\right)\right))\}$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.extensions` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Theorem 3.8, page 6: "Every QSC extends to a quantum superchannel." The set here consists of the full superchannels agreeing with Gamma on every element of SCPTP. Agreement is equality of matrix maps, after Subtype.val on both sides.

**Definition 1.7 (The input-first Choi matrix).**

$$\forall (A: Type), \forall (B: Type), [DecidableEq\left(A\right)] \forall (L: MatrixMap\left(A, B, \mathbb{C}\right)), \forall (i: A), \forall (j: A), \forall (k: B), \forall (l: B), choi\left(L\right)\left((i, k), (j, l)\right) = L\left(\operatorname{Matrix.single}\left(i, j, 1\right), k, l\right)$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choi` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Section 2, page 3: "Now any linear map is determined by its action on basis elements so for a linear L : M_d → M_r we get a vector space isomorphism from L(M_d, M_r) onto M_d(M_r) via L ↦ (L(E_{i,j}))." The entry with row (i,k) and column (j,l) is the (k,l) entry of L applied to Matrix.single i j 1.

**Definition 1.8 (The Choi linear equivalence).**

$$\forall (A: Type), \forall (B: Type), [Fintype\left(A\right)] [DecidableEq\left(A\right)] (\forall (L: MatrixMap\left(A, B, \mathbb{C}\right)), \forall (i: A), \forall (j: A), \forall (k: B), \forall (l: B), (choiEquiv\left(A, B\right)).toFun\left(L\right)\left((i, k), (j, l)\right) = L\left(\operatorname{Matrix.single}\left(i, j, 1\right), k, l\right)) \land (\forall (X: Matrix\left(A \times B, A \times B, \mathbb{C}\right)), \forall (Y: Matrix\left(A, A, \mathbb{C}\right)), \forall (k: B), \forall (l: B), (choiEquiv\left(A, B\right)).invFun\left(X, Y, k, l\right) = \sum_{i: A} (\sum_{j: A} (Y\left(i, j\right) \cdot X\left((i, k), (j, l)\right))))$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choiEquiv` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Section 2, page 3: "Now any linear map is determined by its action on basis elements so for a linear L : M_d → M_r we get a vector space isomorphism from L(M_d, M_r) onto M_d(M_r) via L ↦ (L(E_{i,j}))." The forward action applies L to each matrix unit. Its inverse maps X and Y to the matrix with entry ∑ i, ∑ j, Y i j * X (i,k) (j,l). Only the input carrier A requires Fintype and DecidableEq instances.

**Definition 1.9 (The induced map on Choi matrices).**

$$\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), \forall (S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), induced\left(S\right) = ((choiEquiv\left(Fin\left(d2\right), Fin\left(r2\right)\right)).toLinearMap) \circ ((S) \circ (((choiEquiv\left(Fin\left(d1\right), Fin\left(r1\right)\right)).symm).toLinearMap))$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.induced` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

After Definition 3.4, page 5: "If Γ is a QSC it induces a map Γ̃ : S(d_1, r_1) → S(d_2, r_2) via Γ̃ = R_2 ∘ Γ ∘ R_1^{−1}." For a full superchannel S the same composition acts on all block matrices. The displayed expression uses the forward and inverse Choi linear equivalences.

**Definition 1.10 (The reduced Choi rank).**

$$\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), \forall (S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), e\left(S\right) = (\operatorname{PartialTraceMutualInformation.partialTraceRight}\left((\operatorname{LiJiangPolarPairOptimalityRefutation.inputFirstChoi}\left(induced\left(S\right)\right)).reindex\left(\operatorname{Equiv.prodProdProdComm}\left(Fin\left(d1\right), Fin\left(r1\right), Fin\left(d2\right), Fin\left(r2\right)\right), \operatorname{Equiv.prodProdProdComm}\left(Fin\left(d1\right), Fin\left(r1\right), Fin\left(d2\right), Fin\left(r2\right)\right)\right)\right)).rank$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.e` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Section 4, page 10: "The dimension e can be chosen to be the rank of Tr_{r_1} Tr_{r_2} C_{Γ̃}" The permutation Equiv.prodProdProdComm changes ((d1,r1),(d2,r2)) to ((d1,d2),(r1,r2)); partialTraceRight traces out the latter pair, and Matrix.rank takes the complex rank.

**Definition 1.11 (The minimum-rank extremality question).**

$$claim = (\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), (1 \le d1) \Rightarrow ((1 \le r1) \Rightarrow ((1 \le d2) \Rightarrow ((1 \le r2) \Rightarrow (\forall (Gamma: (SCPTP\left(d1, r1\right)) \to_{\mathbb{C}} (SCPTP\left(d2, r2\right))), (IsQSC\left(Gamma\right)) \Rightarrow (\forall (S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), (S \in extensions\left(Gamma\right)) \Rightarrow ((\forall (G: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), (G \in extensions\left(Gamma\right)) \Rightarrow (e\left(S\right) \le e\left(G\right))) \Rightarrow (S \in (extensions\left(Gamma\right)).extremePoints\left(\mathbb{R}\right)))))))))$$

*Formalization.* `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.claim` (`✓ std3`).

*Citation.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

Remark 4.1, page 11: "The set of possible superchannel extensions of a QSC is a convex set. In the example given the extensions with minimal e are extreme points. A natural question to ask is whether it is generally true that the extensions which give minimal dimensions e are extreme points." The proposition quantifies over four positive dimensions, every QSC Gamma and every minimizing extension S. The comparison includes all extensions G, and extremePoints uses real scalars.

**Theorem 1.12 (A non-extreme minimizing extension).**

$$\neg (\forall (d1: \mathbb{N}), \forall (r1: \mathbb{N}), \forall (d2: \mathbb{N}), \forall (r2: \mathbb{N}), (1 \le d1) \Rightarrow ((1 \le r1) \Rightarrow ((1 \le d2) \Rightarrow ((1 \le r2) \Rightarrow (\forall (Gamma: (SCPTP\left(d1, r1\right)) \to_{\mathbb{C}} (SCPTP\left(d2, r2\right))), (IsQSC\left(Gamma\right)) \Rightarrow (\forall (S: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), (S \in extensions\left(Gamma\right)) \Rightarrow ((\forall (G: (MatrixMap\left(Fin\left(d1\right), Fin\left(r1\right), \mathbb{C}\right)) \to_{\mathbb{C}} (MatrixMap\left(Fin\left(d2\right), Fin\left(r2\right), \mathbb{C}\right))), (G \in extensions\left(Gamma\right)) \Rightarrow (e\left(S\right) \le e\left(G\right))) \Rightarrow (S \in (extensions\left(Gamma\right)).extremePoints\left(\mathbb{R}\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result` (`✓ std3`). ∎

*Resolves.* `Problems/daly-2022-superchannel-minimal-extension-extremality` (refuted) by `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"daly-2022-superchannel-minimal-extension-extremality","declaration_gid":"D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. C. Daly (2022). *Axiomatic Approach to Quantum Superchannels*. DOI: [10.48550/arXiv.2210.00370](https://doi.org/10.48550/arXiv.2210.00370). URL: <https://arxiv.org/abs/2210.00370v1>.

*Commentary.*

For dimensions 2,2,2,2, take the restriction of the map induced by F₀, where Fₛ(X) = X/2 + (I ⊗ TrA X)/8 + Tr(X)I/16 + s Tr((Z ⊗ I)X)(Z ⊗ I)/32 and Z = diag(1,−1). For −1 ≤ s ≤ 1 these maps give extensions with the same restriction. Their fixed off-diagonal coherence block is positive definite. Compressing any extension against a vector in the kernel of its reduced Choi matrix gives a positive semidefinite matrix of trace zero, contradicting that block's strict positivity. Thus every extension has e = 4. The extension at s = 0 is the midpoint of the distinct extensions at s = 1 and s = −1, so it minimizes e and is not extreme. The existence of an extreme minimizer is a separate question.

## References

- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQSC`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQuantumSuperchannel`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.SCPTP`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choi`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choiEquiv`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.claim`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.e`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.extensions`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.induced`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.kronBilin`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.kronLift`
- Truth anchor: `D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Quantum/Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../Quantum/QuantumChannels/PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../Quantum/Reduction/IsometricCompression.md)
