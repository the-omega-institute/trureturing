# The exact quantum bound for nonlocality depth

## Abstract

For every n >= 3, the Bernards--Gühne Bell functional has exact quantum maximum sqrt(2) n 2^(n-2), over all finite local dimensions, binary observables and density matrices.

**Lemma 1.1 (Adjoints commute with the tensor product).**

$$\forall n \in \mathbb{N},\; \forall sigma \in (Fin\left(n\right) \to Type),\; [\forall j \in Fin\left(n\right),\; Fintype\left(sigma\left(j\right)\right)] [\forall j \in Fin\left(n\right),\; DecidableEq\left(sigma\left(j\right)\right)] \forall M \in ((j:Fin\left(n\right)) \to Matrix\left(sigma\left(j\right), sigma\left(j\right), \mathbb{C}\right)),\; \operatorname{ProductPrefixRigidity.productMap}\left(sigma, (\lambda (j : Fin\left(n\right)) \mapsto \operatorname{Matrix.conjTranspose}\left(M\left(j\right)\right))\right) = \operatorname{Matrix.conjTranspose}\left(\operatorname{ProductPrefixRigidity.productMap}\left(sigma, M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.tensor_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor product of the adjoints of a finite family of complex matrices equals the adjoint of their tensor product. The local matrix carriers may be arbitrary types.

**Definition 1.2 (Binary observables).**

$$\forall m \in \mathbb{N},\; \forall M \in Matrix\left(Fin\left(m\right), Fin\left(m\right), \mathbb{C}\right),\; IsBinaryObservable\left(M\right) \Leftrightarrow \left((\operatorname{Matrix.IsHermitian}\left(M\right)) \land ((\operatorname{Matrix.PosSemidef}\left(1 - M\right)) \land (\operatorname{Matrix.PosSemidef}\left(1 + M\right)))\right)$$

*Formalization.* `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.IsBinaryObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A binary observable is Hermitian and both its shifts 1 - M and 1 + M are positive semidefinite. The Bell maximum ranges over two such observables at each party.

**Theorem 1.3 (The positive shift of a Hermitian contraction).**

$$\forall iota \in Type,\; [Fintype\left(iota\right)] [DecidableEq\left(iota\right)] \forall C \in Matrix\left(iota, iota, \mathbb{C}\right),\; (\operatorname{Matrix.IsHermitian}\left(C\right)) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(1 - \operatorname{Matrix.conjTranspose}\left(C\right) \cdot C\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(1 + C\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.one_add_posSemidef_of_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian matrix C, positivity of 1 - C conjugate-transpose times C implies positivity of 1 + C. Adding the positive square of 1 + C to the contraction defect gives twice 1 + C. This implication gives positivity of both shifts of an involution and of the diagonal blocks in the separable scalar-shift construction.

**Lemma 1.4 (Both shifts of a Hermitian involution are positive).**

$$\forall m \in Type,\; [Fintype\left(m\right)] [DecidableEq\left(m\right)] \forall A \in Matrix\left(m, m, \mathbb{C}\right),\; (\operatorname{Matrix.IsHermitian}\left(A\right)) \Rightarrow ((A^{2} = 1) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(1 - A\right)) \land (\operatorname{Matrix.PosSemidef}\left(1 + A\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.involution_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian matrix whose square is the identity has positive semidefinite shifts 1 - A and 1 + A.

**Definition 1.5 (The Bell polynomial of Eq. (28)).**

$$\forall n \in \mathbb{N},\; \forall d \in (Fin\left(n\right) \to \mathbb{N}),\; \forall A \in ((j:Fin\left(n\right)) \to (Bool \to Matrix\left(Fin\left(d\left(j\right)\right), Fin\left(d\left(j\right)\right), \mathbb{C}\right))),\; bellOp\left(n, A\right) = \sum_{x:(Fin\left(n\right) \to Bool)} (\operatorname{SMul.smul}\left(((hammingDist\left(x, \operatorname{Function.const}\left(Fin\left(n\right), false\right)\right):\mathbb{Z}) \cdot phase\left(hammingDist\left(x, \operatorname{Function.const}\left(Fin\left(n\right), false\right)\right)\right):\mathbb{C}), (\lambda a b \mapsto \prod_{j:Fin\left(n\right)} (A\left(j, x\left(j\right)\right)\left(a\left(j\right), b\left(j\right)\right)))\right))$$

*Formalization.* `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.bellOp` (`✓ std3`).

*Citation.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Section III.F, PDF p. 5, Eq. (28), reads: “F_n = ∑_{ℓ=1}^n (−1)^{1+⌈ℓ/2⌉} ℓ (1…1 2…2) ≤ n 2^{n−2}.” The bracket sums the distinct party permutations, with n - ℓ settings 1 and ℓ settings 2. Each Boolean setting string therefore occurs once. Its weight hammingDist(x,fun j ↦ false) counts the true coordinates. The integer sign phase(h) is the sign (-1)^(1+ceil(h/2)) defined in HybridMerminDepthBound.

**Definition 1.6 (The exact maximum in every party number).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow (IsGreatest\left(\{v:\mathbb{R} \mid \exists d \in (Fin\left(n\right) \to \mathbb{N}),\; \exists A \in ((j:Fin\left(n\right)) \to (Bool \to Matrix\left(Fin\left(d\left(j\right)\right), Fin\left(d\left(j\right)\right), \mathbb{C}\right))),\; \exists rho \in Matrix\left(((j:Fin\left(n\right)) \to Fin\left(d\left(j\right)\right)), ((j:Fin\left(n\right)) \to Fin\left(d\left(j\right)\right)), \mathbb{C}\right),\; (\forall j \in Fin\left(n\right),\; \forall s \in Bool,\; IsBinaryObservable\left(A\left(j, s\right)\right)) \land (((\operatorname{Matrix.PosSemidef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = 1)) \land (v = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot bellOp\left(n, A\right)\right)\right)))\}, \operatorname{Real.sqrt}\left(2\right) \cdot (n:\mathbb{R}) \cdot 2^{\operatorname{Nat.sub}\left(n, 2\right)}\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.claim` (`✓ std3`).

*Citation.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Section III.F, PDF p. 5, Eq. (29), states verbatim: “In the following, we discuss numerical findings concerning the Bell inequalities F_n for n ≤ 8 parties. We find, that the quantum bound of the inequalities is F_n = √2 n 2^{n−2} (29) up to numerical precision, which is achieved by choosing A₁ = B₁ = … = σ_x and A₂ = B₂ = … = σ_z”. The assertion extends this value to every n >= 3. Fin n labels parties; d gives their arbitrary finite local dimensions. A assigns two local observables per party, and rho ranges over positive-semidefinite matrices of trace one. IsGreatest asserts both the upper bound and its attainment. Nat.sub denotes truncated natural-number subtraction.

**Definition 1.7 (The shifted unweighted polynomial).**

$$\forall n \in \mathbb{N},\; \forall sigma \in (Fin\left(n\right) \to Type),\; [\forall j \in Fin\left(n\right),\; Fintype\left(sigma\left(j\right)\right)] \forall A \in ((j:Fin\left(n\right)) \to (Bool \to Matrix\left(sigma\left(j\right), sigma\left(j\right), \mathbb{C}\right))),\; \forall r \in \mathbb{N},\; \operatorname{Upper.unweighted}\left(A, r\right) = \sum_{x:(Fin\left(n\right) \to Bool)} (\operatorname{SMul.smul}\left((phase\left(hammingDist\left(x, \operatorname{Function.const}\left(Fin\left(n\right), false\right)\right) + r\right):\mathbb{C}), ((\lambda a b \mapsto \prod_{j:Fin\left(n\right)} (A\left(j, x\left(j\right)\right)\left(a\left(j\right), b\left(j\right)\right))):Matrix\left(((j:Fin\left(n\right)) \to sigma\left(j\right)), ((j:Fin\left(n\right)) \to sigma\left(j\right)), \mathbb{C}\right))\right))$$

*Formalization.* `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.unweighted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

The natural number shift r changes the phase of the coefficient sequence. Removing one party splits this polynomial into its two local settings, with shifts r and r + 1.

**Lemma 1.8 (The all-party shifted operator estimate).**

$$\forall k \in \mathbb{N},\; \forall sigma \in (Fin\left(k + 2\right) \to Type),\; [\forall j \in Fin\left(k + 2\right),\; Fintype\left(sigma\left(j\right)\right)] [\forall j \in Fin\left(k + 2\right),\; DecidableEq\left(sigma\left(j\right)\right)] \forall A \in ((j:Fin\left(k + 2\right)) \to (Bool \to Matrix\left(sigma\left(j\right), sigma\left(j\right), \mathbb{C}\right))),\; (\forall j \in Fin\left(k + 2\right),\; \forall s \in Bool,\; \operatorname{Matrix.IsHermitian}\left(A\left(j, s\right)\right)) \Rightarrow ((\forall j \in Fin\left(k + 2\right),\; \forall s \in Bool,\; A\left(j, s\right)^{2} = 1) \Rightarrow (\forall r \in \mathbb{N},\; \operatorname{Matrix.PosSemidef}\left(\operatorname{SMul.smul}\left(\operatorname{Real.sqrt}\left(2\right) \cdot 2^{k + 1}, (1:Matrix\left(((j:Fin\left(k + 2\right)) \to sigma\left(j\right)), ((j:Fin\left(k + 2\right)) \to sigma\left(j\right)), \mathbb{C}\right))\right) - \operatorname{Upper.unweighted}\left(A, r\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.unweighted_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

The identity phase(h + 2) = -phase(h) makes the two-party polynomial a signed CHSH operator. Mathlib's Tsirelson inequality gives its positive-semidefinite upper bound 2 sqrt(2). For a Hermitian involution A and a matrix B bounded on both sides by q, the positive tensor sum ((1 + A) tensor (q - B) + (1 - A) tensor (q + B))/2 equals q - A tensor B. Applying this identity to the two terms in the party split propagates the estimate by induction. The statement includes all natural number shifts and every finite local carrier.

**Theorem 1.9 (The universal upper bound is attained).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/bernards-guhne-2023-nonlocality-depth-quantum-bound` (proved) by `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bernards-guhne-2023-nonlocality-depth-quantum-bound","declaration_gid":"D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. Bernards; O. Gühne (2023). *Bell inequalities for nonlocality depth*. DOI: [10.1103/PhysRevA.107.022412](https://doi.org/10.1103/PhysRevA.107.022412). URL: <https://arxiv.org/abs/2205.04250v2>.

*Commentary.*

Distributing the Hamming weight over the marked parties writes bellOp as a sum of n terms. Each term consists of a local observable at setting true tensored with a shifted unweighted polynomial on the other n - 1 parties. The shifted estimate bounds each term by sqrt(2) 2^(n-2), and addition gives sqrt(2) n 2^(n-2). A Hermitian contraction dilates to the involution with blocks A, sqrt(1 - A²), sqrt(1 - A²), -A. Compression preserves every correlator, so the same bound holds for all binary observables. Positivity of the trace of a product of positive-semidefinite matrices gives the expectation bound for every density matrix. For attainment take X and Y at every party. On the two constant basis strings the off-diagonal amplitude is n 2^(n-2)(-1 + i). The normalized vector (e0 + eta e1)/sqrt(2), with eta = (-1 + i)/sqrt(2), is an eigenvector with the positive maximal eigenvalue. Its rank-one density matrix attains the bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.IsBinaryObservable`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.bellOp`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.claim`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.involution_binary`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.one_add_posSemidef_of_contraction`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.result`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.tensor_star`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.unweighted`
- Truth anchor: `D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.unweighted_bound`
- Dependency: [D5/S1/Words/AdmissibleWords/FibonacciGrayPath](../../S1/Words/AdmissibleWords/FibonacciGrayPath.md)
- Dependency: [D5/S3/Analytic/Hunter/NCHunterPositivity](../Analytic/Hunter/NCHunterPositivity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Quantum/Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/QuantumBounds/HybridMerminDepthBound](HybridMerminDepthBound.md)
