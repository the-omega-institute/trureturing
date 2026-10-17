# Coherent discrimination bias is not a channel metric

## Abstract

Coherent discrimination bias fails the triangle inequality for three qubit replacement channels.

The input A, output B and flag F have basis Fin(2); the four Kraus operators are indexed by Fin(4). Fin(n) consists of the integers from 0 to n − 1. Matrices and vectors have complex entries. Matrix.unitaryGroup consists of unitary matrices, and a dagger denotes conjugate transpose. A finite reference R is retained throughout the experiment. The finite ancilla E, representing E′, has a specified zero state e₀, denoted e in the formulas. Products of types index tensor-product bases. Prod.fst and Prod.snd select the first and second coordinates of a pair; tuples are nested to the right. The anonymous brackets supply finite enumerations and decidable equality. All finite sums include every index.

**Definition 1.1 (The canonical isometric extension).**

$$\forall R \in \mathit{Type},\; \forall K \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall psi \in R \times \operatorname{\mathit{Fin}}\left(2\right) \to \mathit{Complex},\; \forall r \in R,\; \forall b \in \operatorname{\mathit{Fin}}\left(2\right),\; \forall k \in \operatorname{\mathit{Fin}}\left(4\right),\; \operatorname{\mathit{extend}}\left(K, \mathit{psi}\right)\left((r, (b, k))\right) = \sum_{a:\operatorname{\mathit{Fin}}\left(2\right)}(K\left(k, b, a\right) \cdot \mathit{psi}\left((r, a)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.extend` (`✓ std3`).

*Citation.* Mark M. Wilde (2020). *Coherent Quantum Channel Discrimination*. DOI: [10.1109/ISIT44484.2020.9174425](https://doi.org/10.1109/ISIT44484.2020.9174425). URL: <https://arxiv.org/abs/2001.02668v1>.

*Commentary.*

For a Kraus family K, the vector extend(K, ψ) has coordinate (r,b,k) equal to the sum over a of K_k(b,a) ψ(r,a). This is the canonical extension of Eq. (10), with the reference coordinate unchanged. The formula is defined for every K and ψ. For a channel, the Kraus normalization is the matrix identity Σ_k K_k† K_k = 1; under this condition the extension is an isometry. The identity matrix acts on the input qubit.

**Definition 1.2 (Success of a coherent discrimination strategy).**

$$\forall R \in \mathit{Type},\; \forall E \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(R\right)], [\operatorname{\mathit{Fintype}}\left(E\right)], [\operatorname{\mathit{DecidableEq}}\left(R\right)], [\operatorname{\mathit{DecidableEq}}\left(E\right)], \forall K \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall L \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall psi \in R \times \operatorname{\mathit{Fin}}\left(2\right) \to \mathit{Complex},\; \forall V \in \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(R \times \operatorname{\mathit{Fin}}\left(2\right) \times E \times \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall e \in E,\; \operatorname{\mathit{successProbability}}\left(K, L, \mathit{psi}, V, e\right) = \frac{1}{4} \cdot \sum_{x:R \times \operatorname{\mathit{Fin}}\left(2\right) \times E}(\left\lVert \sum_{i:\operatorname{\mathit{Fin}}\left(2\right)}(\sum_{b:\operatorname{\mathit{Fin}}\left(2\right)}(\sum_{k:\operatorname{\mathit{Fin}}\left(4\right)}(\operatorname{\mathit{conj}}\left((\operatorname{\mathit{if}} (i = 0) \operatorname{\mathit{then}} K \operatorname{\mathit{else}} L)\left(k, b, \operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(x\right)\right)\right)\right) \cdot \sum_{y:R \times \operatorname{\mathit{Fin}}\left(2\right) \times E \times \operatorname{\mathit{Fin}}\left(2\right)}(\operatorname{\mathit{Subtype}}.\operatorname{\mathit{val}}\left(V\right)\left((\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(x\right), (b, (\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(x\right)\right), i))), y\right) \cdot (\operatorname{\mathit{if}} ((\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(y\right)\right)\right) = e) \land (\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(y\right)\right)\right) = 0)) \operatorname{\mathit{then}} \operatorname{\mathit{extend}}\left((\operatorname{\mathit{if}} (i = 0) \operatorname{\mathit{then}} K \operatorname{\mathit{else}} L), \mathit{psi}\right)\left((\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(y\right), (\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(y\right)\right), k))\right) \operatorname{\mathit{else}} 0))))) \right\rVert^{2})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.successProbability` (`✓ std3`).

*Citation.* Mark M. Wilde (2020). *Coherent Quantum Channel Discrimination*. DOI: [10.1109/ISIT44484.2020.9174425](https://doi.org/10.1109/ISIT44484.2020.9174425). URL: <https://arxiv.org/abs/2001.02668v1>.

*Commentary.*

Equation (17) adjoins the basis states e₀ and 0 of E′ and F, applies the prover's unitary V on R, B, E′ and F while retaining the Kraus index, and applies the adjoint extension. For the first channel the final flag is 0; for the second it is 1. The sum over i adds the two resulting vectors on R, A and E′ coherently, using K when i = 0 and L when i = 1. Their squared Euclidean norm is the sum of squared complex moduli displayed here. The factor 1/4 is the initial factor 1/2 in Eq. (17) multiplied by the factor 1/2 from contraction with the normalized Bell bra. The conditional inserts the two initial zero states. For a physical strategy ψ is a unit vector and the Kraus families satisfy the normalization Σ_k K_k† K_k = 1. The expression itself is defined for arbitrary ψ and Kraus matrices.

**Definition 1.3 (The optimal coherent success probability).**

$$\forall K \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall L \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \operatorname{\mathit{coherentValue}}\left(K, L\right) = \operatorname{\mathit{sSup}}\left(\{p:\mathit{Real}|\exists R \in \mathit{Type},\; \exists E \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(R\right)], [\operatorname{\mathit{Fintype}}\left(E\right)], [\operatorname{\mathit{DecidableEq}}\left(R\right)], [\operatorname{\mathit{DecidableEq}}\left(E\right)], \exists e \in E,\; \exists psi \in R \times \operatorname{\mathit{Fin}}\left(2\right) \to \mathit{Complex},\; \exists V \in \operatorname{\mathit{Matrix}}.\operatorname{\mathit{unitaryGroup}}\left(R \times \operatorname{\mathit{Fin}}\left(2\right) \times E \times \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; (\sum_{x:R \times \operatorname{\mathit{Fin}}\left(2\right)}(\left\lVert \mathit{psi}\left(x\right) \right\rVert^{2}) = 1) \land (p = \operatorname{\mathit{successProbability}}\left(K, L, \mathit{psi}, V, e\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.coherentValue` (`✓ std3`).

*Citation.* Mark M. Wilde (2020). *Coherent Quantum Channel Discrimination*. DOI: [10.1109/ISIT44484.2020.9174425](https://doi.org/10.1109/ISIT44484.2020.9174425). URL: <https://arxiv.org/abs/2001.02668v1>.

*Commentary.*

Equation (18) takes the real supremum over every finite reference R, finite pointed ancilla E′, unit input ψ on R and A, and prover unitary V on R, B, E′ and F. The set explicitly includes every such choice of finite types in Type and its instances. For normalized Kraus families this is p_s^coh. The source states after Eq. (17) that its value is independent of the chosen isometric extensions. No normalization condition on the Kraus matrices is imposed by this definition alone.

**Definition 1.4 (The proposed triangle inequality).**

$$(\mathit{claim}) \Leftrightarrow (\forall K \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall L \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; \forall M \in \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right),\; (\sum_{k:\operatorname{\mathit{Fin}}\left(4\right)}(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(K\left(k\right)\right) \cdot K\left(k\right)) = 1) \Rightarrow ((\sum_{k:\operatorname{\mathit{Fin}}\left(4\right)}(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(L\left(k\right)\right) \cdot L\left(k\right)) = 1) \Rightarrow ((\sum_{k:\operatorname{\mathit{Fin}}\left(4\right)}(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{conjTranspose}}\left(M\left(k\right)\right) \cdot M\left(k\right)) = 1) \Rightarrow (\operatorname{\mathit{coherentValue}}\left(K, M\right) - \frac{1}{2} \le (\operatorname{\mathit{coherentValue}}\left(K, L\right) - \frac{1}{2}) + (\operatorname{\mathit{coherentValue}}\left(L, M\right) - \frac{1}{2})))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim` (`✓ std3`).

*Citation.* Mark M. Wilde (2020). *Coherent Quantum Channel Discrimination*. DOI: [10.1109/ISIT44484.2020.9174425](https://doi.org/10.1109/ISIT44484.2020.9174425). URL: <https://arxiv.org/abs/2001.02668v1>.

*Commentary.*

Put d(N,M) = p_s^coh(N,M) − 1/2. The assertion requires the triangle inequality for every three qubit channels represented by four Kraus operators each. Each displayed normalization Σ_k K_k† K_k = 1 is exactly the channel condition. Section VI asks whether p_s^coh − 1/2 is a metric on quantum channels. That metric property implies this triangle inequality, because the optimal value is independent of the choice of isometric extensions.

**Theorem 1.5 (Three replacement channels violate the triangle inequality).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wilde-2020-coherent-discrimination-triangle-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wilde-2020-coherent-discrimination-triangle-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark M. Wilde (2020). *Coherent Quantum Channel Discrimination*. DOI: [10.1109/ISIT44484.2020.9174425](https://doi.org/10.1109/ISIT44484.2020.9174425). URL: <https://arxiv.org/abs/2001.02668v1>.

*Commentary.*

For a strictly positive probability vector t = (t₀,t₁), consider the qubit channel R_t(X) = Tr(X) diag(t₀,t₁). Its four Kraus operators are √t_j |j⟩⟨k|, with j,k in Fin(2), indexed by the equivalence Fin(2) × Fin(2) ≃ Fin(4). Their conjugate-transpose products sum to the identity.

For two such vectors t,u, set s_j = √(t_j² + u_j²). Then p_s^coh(R_t,R_u) = (s₀ + s₁)²/4. To obtain the upper bound, fix any strategy and write Q_ij for the part of V from (B = j, E′ = e₀, F = 0) to (B = j, F = i): explicitly, (Q_ij ψ)(r,a,e′) = Σ_q V((r,j,e′,i),(q,j,e₀,0)) ψ(q,a). Unitarity gives ‖Q_0j ψ‖² + ‖Q_1j ψ‖² ≤ ‖ψ‖². The vector in the success expression is Σ_j (t_j Q_0j + u_j Q_1j) ψ. Cauchy–Schwarz bounds each summand's norm by s_j ‖ψ‖, and the triangle inequality gives the probability bound (s₀ + s₁)²/4.

Equality is attained with trivial reference and ancilla, input |0⟩, and the unitary that, conditioned on B = j, acts on F by (1/s_j)[[t_j,−u_j],[u_j,t_j]]. Its two relevant entries are t_j/s_j and u_j/s_j, so their weighted sum is s_j. Thus the upper bound belongs to the set of strategy values and is its supremum.

Take t = (3/4,1/4), u = (1/2,1/2), and v = (1/4,3/4). The closed form gives p_s^coh(R_t,R_v) = 5/8 and p_s^coh(R_t,R_u) = p_s^coh(R_u,R_v) = (9 + √65)/32. Consequently d(R_t,R_v) = 1/8, whereas d(R_t,R_u) = d(R_u,R_v) = (√65 − 7)/32. Their sum (√65 − 7)/16 is strictly less than 1/8 because √65 < 9. These normalized Kraus families contradict claim and hence give a negative answer to the metric question in Section VI.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.coherentValue`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.extend`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.successProbability`
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation](OutputMaximalCoherenceTensorizationRefutation.md)
