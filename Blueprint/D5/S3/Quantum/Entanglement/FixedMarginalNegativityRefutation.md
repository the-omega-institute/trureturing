# The fixed-marginal candidate need not maximize two-qutrit negativity

## Abstract

At fixed two-qutrit marginals diag(49,47,4)/100 and diag(94,5,1)/100, a density matrix has greater negativity than the candidate of Baio, Chruscinski, Horodecki, Messina and Sarbicki.

The two factors are A and B, each with basis indexed by Fin 3 = {0,1,2}. Matrices act on their tensor product, with row and column indices in Fin 3 × Fin 3. The ket |ij⟩ is the basis vector |i⟩ ⊗ |j⟩, the dagger is conjugate transpose, and real coefficients of complex matrices are interpreted through the usual inclusion into C. All sums include every element of the indicated finite index set.

**Definition 1.1 (The ordered fixed marginal).**

$$\forall (x_{1} : \mathbb{R}), \forall (x_{2} : \mathbb{R}), \operatorname{orderedMarginal}\left(x_{1}, x_{2}\right) = \begin{pmatrix}1 - x_{1} - x_{2}&0&0\\0&x_{1}&0\\0&0&x_{2}\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.orderedMarginal` (`✓ std3`).

*Citation.* Giuseppe Baio; Dariusz Chruściński; Paweł Horodecki; Antonino Messina; Gniewomir Sarbicki (2019). *Bounds on the entanglement of two-qutrit systems from fixed marginals*. DOI: [10.1103/PhysRevA.99.062312](https://doi.org/10.1103/PhysRevA.99.062312). URL: <https://arxiv.org/abs/1904.07650v2>.

*Commentary.*

The two diagonal matrices ρ_A and ρ_B in Eq. (24) share this form, with parameters (λ₁, λ₂) for A and (μ₁, μ₂) for B. Its entries are 1 − x₁ − x₂, x₁ and x₂ in the basis order 0,1,2. This definition is made for all real parameters; the conjecture below imposes their ordering and positivity.

**Definition 1.2 (The candidate of Eq. (27)).**

$$\forall (\lambda_{1} : \mathbb{R}), \forall (\lambda_{2} : \mathbb{R}), \forall (\mu_{1} : \mathbb{R}), \forall (\mu_{2} : \mathbb{R}), \operatorname{let} \varphi = \sqrt{1 - \lambda_{1} - \lambda_{2}} \cdot |00\rangle + \sqrt{\mu_{1}} \cdot |11\rangle + \sqrt{\mu_{2}} \cdot |22\rangle \operatorname{in} \operatorname{candidate}\left(\lambda_{1}, \lambda_{2}, \mu_{1}, \mu_{2}\right) = (\varphi) \cdot (\varphi)^{\operatorname{dagger}} + (\lambda_{1} - \mu_{1}) \cdot (|10\rangle) \cdot (|10\rangle)^{\operatorname{dagger}} + (\lambda_{2} - \mu_{2}) \cdot (|20\rangle) \cdot (|20\rangle)^{\operatorname{dagger}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.candidate` (`✓ std3`).

*Citation.* Giuseppe Baio; Dariusz Chruściński; Paweł Horodecki; Antonino Messina; Gniewomir Sarbicki (2019). *Bounds on the entanglement of two-qutrit systems from fixed marginals*. DOI: [10.1103/PhysRevA.99.062312](https://doi.org/10.1103/PhysRevA.99.062312). URL: <https://arxiv.org/abs/1904.07650v2>.

*Commentary.*

The vector φ has amplitudes √(1 − λ₁ − λ₂), √μ₁ and √μ₂ on |00⟩, |11⟩ and |22⟩. Its outer product, together with the two displayed diagonal terms, is Eq. (27) in the matrix form of Eq. (30). The square roots are real square roots, with value zero on negative inputs, so the formula also specifies the definition outside the parameter region used below.

**Definition 1.3 (The maximizing conjecture in the region of Eq. (27)).**

$$\operatorname{claim} \Leftrightarrow (\forall (\lambda_{1} : \mathbb{R}), \forall (\lambda_{2} : \mathbb{R}), \forall (\mu_{1} : \mathbb{R}), \forall (\mu_{2} : \mathbb{R}), (\lambda_{2} \le \lambda_{1}) \Rightarrow \left((\lambda_{1} \le 1 - \lambda_{1} - \lambda_{2}) \Rightarrow \left((0 \le \lambda_{2}) \Rightarrow \left((\mu_{2} \le \mu_{1}) \Rightarrow \left((\mu_{1} \le 1 - \mu_{1} - \mu_{2}) \Rightarrow \left((0 \le \mu_{2}) \Rightarrow \left((\mu_{1} + \mu_{2} \le \lambda_{1} + \lambda_{2}) \Rightarrow \left((\mu_{1} < \lambda_{1}) \Rightarrow \left((\mu_{2} < \lambda_{2}) \Rightarrow \forall (R : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), ((0 \le R) \land (\operatorname{Tr}\left(R\right) = 1)) \Rightarrow \left((\left(\operatorname{Tr}_{B}\right)\left(R\right) = \operatorname{orderedMarginal}\left(\lambda_{1}, \lambda_{2}\right)) \Rightarrow \left((\left(\operatorname{Tr}_{A}\right)\left(R\right) = \operatorname{orderedMarginal}\left(\mu_{1}, \mu_{2}\right)) \Rightarrow \operatorname{negativity}\left(R\right) \le \operatorname{negativity}\left(\operatorname{candidate}\left(\lambda_{1}, \lambda_{2}, \mu_{1}, \mu_{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim` (`✓ std3`).

*Citation.* Giuseppe Baio; Dariusz Chruściński; Paweł Horodecki; Antonino Messina; Gniewomir Sarbicki (2019). *Bounds on the entanglement of two-qutrit systems from fixed marginals*. DOI: [10.1103/PhysRevA.99.062312](https://doi.org/10.1103/PhysRevA.99.062312). URL: <https://arxiv.org/abs/1904.07650v2>.

*Commentary.*

The negativity in this assertion is Eq. (4), $\forall (R : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), \operatorname{negativity}\left(R\right) = \frac{\left\lVert R^{\Gamma} \right\rVert_{1} - 1}{2}$, using the definition `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.negativity` with both factors indexed by Fin 3.

The trace norm used here is the real part of the trace of the positive square root:$\forall (X : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), \left\lVert X \right\rVert_{1} = \Re\left(\operatorname{Tr}\left(\sqrt{X^{\operatorname{dagger}} \cdot X}\right)\right)$.

Partial transposition acts on B alone, exchanging the second row and column indices:$\forall (R : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(3\right)), \forall (j : \operatorname{Fin}\left(3\right)), \forall (k : \operatorname{Fin}\left(3\right)), \forall (l : \operatorname{Fin}\left(3\right)), \left(R^{\Gamma}\right)\left((i, j), (k, l)\right) = R\left((i, l), (k, j)\right)$.

Section IV conjectures that the quasidistillable candidates maximize negativity at fixed marginals. Here this assertion is restricted to the region of Eq. (27): the two spectra are nonnegative and in decreasing order, μ₁ + μ₂ ≤ λ₁ + λ₂, μ₁ < λ₁ and μ₂ < λ₂. Every density matrix with the two prescribed marginals is asserted to have negativity at most that of the candidate. The condition R ≥ 0 means complex Hermitian positive semidefiniteness, and Tr(R) = 1 supplies normalization.

The two partial traces in the assertion are specified entrywise by $\forall (R : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(3\right)), \forall (k : \operatorname{Fin}\left(3\right)), \left(\operatorname{Tr}_{B}\right)\left(R\right)\left(i, k\right) = \sum_{(j : \operatorname{Fin}\left(3\right))} (R\left((i, j), (k, j)\right))$ and $\forall (R : \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), (\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right)), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(3\right)), \forall (k : \operatorname{Fin}\left(3\right)), \left(\operatorname{Tr}_{A}\right)\left(R\right)\left(i, k\right) = \sum_{(j : \operatorname{Fin}\left(3\right))} (R\left((j, i), (j, k)\right))$. Thus Tr_B removes the second factor and Tr_A removes the first.

**Theorem 1.4 (A state with the same marginals has strictly greater negativity).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/baio-chruscinski-horodecki-messina-sarbicki-2019-fixed-marginal-negativity-refutation` (refuted) by `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baio-chruscinski-horodecki-messina-sarbicki-2019-fixed-marginal-negativity-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giuseppe Baio; Dariusz Chruściński; Paweł Horodecki; Antonino Messina; Gniewomir Sarbicki (2019). *Bounds on the entanglement of two-qutrit systems from fixed marginals*. DOI: [10.1103/PhysRevA.99.062312](https://doi.org/10.1103/PhysRevA.99.062312). URL: <https://arxiv.org/abs/1904.07650v2>.

*Commentary.*

Take λ = (47,4)/100 and μ = (5,1)/100. Then ρ_A = diag(49,47,4)/100 and ρ_B = diag(94,5,1)/100 satisfy every parameter inequality above. Let χ = (7|00⟩ + |12⟩ + 2|21⟩)/10 and set ρ = (99/100)(χχ† + (45/100)|10⟩⟨10| + (1/100)|11⟩⟨11|) + (1/100)ρ_A ⊗ ρ_B. Each summand is positive semidefinite, the total trace is one, and the partial traces are ρ_A and ρ_B.

For a vector v write O(v) = vv†. Define 𝑲 = O(|01⟩ − |20⟩)/2 + O(7|02⟩ − |10⟩)/50 + O(|11⟩ − |22⟩)/2. These three rank-one terms are mutually orthogonal projections, so 𝑲† = 𝑲 and 𝑲² = 𝑲. The reflection 1 − 2𝑲 is unitary and Tr((1 − 2𝑲)ρ^Γ) = 1 + 2·8168881/50000000. The variational characterization of the trace norm therefore gives N(ρ) ≥ 8168881/50000000 > 7/50.

Let σ be the candidate at these parameters, so σ = φφ† + (42/100)|10⟩⟨10| + (3/100)|20⟩⟨20| with φ = (7|00⟩ + √5|11⟩ + |22⟩)/10. Its partial transpose is P − Q, where P = (49/100)|00⟩⟨00| + (5/100)|11⟩⟨11| + (1/100)|22⟩⟨22| + O(35|01⟩ + 47√5|10⟩)/26000 + O(35|02⟩ + 43|20⟩)/35500 + (√5/200)O(|12⟩ + |21⟩), and Q = O(7|01⟩ − √5|10⟩)/1040 + O(35|02⟩ − 28|20⟩)/35500 + (√5/200)O(|12⟩ − |21⟩). Both P and Q are positive semidefinite. Their traces are 1 + 100159/923000 + √5/100 and 100159/923000 + √5/100. The trace-norm triangle inequality yields N(σ) ≤ 100159/923000 + √5/100 < 7/50, using √5 < 5/2. Hence N(σ) < N(ρ) although their marginals agree, contradicting the conjecture. The coherences of χ join |00⟩, |12⟩ and |21⟩, rather than the three equally indexed basis vectors used by the candidate.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.candidate`
- Truth anchor: `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.orderedMarginal`
- Truth anchor: `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result`
- Truth anchor: `D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.negativity`
- Dependency: [D5/S3/QuantumBounds/NegativityReductionInclusionRefutation](../../QuantumBounds/NegativityReductionInclusionRefutation.md)
