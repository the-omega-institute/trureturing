# The Alsing–Birrittella logarithmic-negativity sandwich

## Abstract

Positive Hermitian amplitude matrices give an exact trace-norm formula, a logarithmic-negativity sandwich, and equality of the upper bound for real amplitudes.

**Definition 1.1 (The finite pure-state ensemble).**

$$\forall d \in \mathbb{N},\; \forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \mathbb{R},\; \forall C \in \operatorname{Fin}\left(K\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{ensembleState}\left(p, C\right) = \sum_{i: \operatorname{Fin}\left(K\right)} (\operatorname{Complex.ofReal}\left(p\left(i\right)\right)\cdot \operatorname{Matrix.vecMulVec}\left(\operatorname{Function.uncurry}\left(C\left(i\right)\right), \operatorname{star}\left(\operatorname{Function.uncurry}\left(C\left(i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.ensembleState` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Alsing and Birrittella, arXiv:2404.13725v1, p. 11: "when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|". Here d is the subsystem dimension and K is the ensemble size. Function.uncurry C maps (n,m) to C n m, so Matrix.vecMulVec forms the pure-state outer product. Each real weight is embedded in ℂ before scalar multiplication.

**Definition 1.2 (Exact logarithmic negativity in bits).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right),\; \operatorname{exactLogNegativity}\left(rho\right) = \operatorname{Real.logb}\left(2, \operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose}\left(rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.exactLogNegativity` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Introduction, p. 1: "A widely used “measure” of entanglement for both pure and mixed states, both discrete and continuous variable, is the Log Negativity (LN)", given by LN(ρ_ab) = log₂(1 + 2 N), "where the negativity N is given by the sum of the absolute values of the negative eigenvalues of the partial transpose of ρ_ab." Here the exact logarithmic negativity is expressed as log₂ ‖ρ^Γ‖₁. KickedIsingNegativityRefutation.partialTranspose transposes the second tensor factor: its (a,b),(c,e) entry is ρ(a,e),(c,b). FiniteTraceDistance.traceNorm is the real part of the trace of CFC.sqrt (X adjoint times X). Real.logb uses base two.

**Definition 1.3 (The pure-state determinant expression).**

$$\forall d \in \mathbb{N},\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{pureApproxNegativity}\left(C\right) = \frac{1}{2} \cdot \sum_{n: \operatorname{Fin}\left(d\right)} (\sum_{m: \operatorname{Fin}\left(d\right)} (\operatorname{ite}\left(m = n, 0, \left\lVert C\left(n, n\right) \cdot C\left(m, m\right) - C\left(n, m\right) \cdot C\left(m, n\right) \right\rVert\right)))$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.pureApproxNegativity` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Equation (11a), p. 4: N_a(|ψ⟩_ab) := ½ Σ_n Σ_(m≠n) |Det [[c_nn,c_nm],[c_mn,c_mm]]|. Both sums run over Fin d. The expression is half the sum over ordered unequal pairs; diagonal terms are zero. The complex norm is the absolute value of the displayed two-by-two determinant.

**Definition 1.4 (The pure-state logarithmic expression).**

$$\forall d \in \mathbb{N},\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{pureApproxLogNegativity}\left(C\right) = \operatorname{Real.logb}\left(2, 1 + 2 \cdot \operatorname{pureApproxNegativity}\left(C\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.pureApproxLogNegativity` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Equation (11b), p. 4: LN_a(|ψ⟩_ab) := log₂(1 + 2 N_a(|ψ⟩_ab)). The logarithm is applied after summing the determinant absolute values.

**Definition 1.5 (The mixed-state entry expression).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right),\; \operatorname{mixedApproxNegativity}\left(rho\right) = \frac{1}{2} \cdot \sum_{n: \operatorname{Fin}\left(d\right)} (\sum_{m: \operatorname{Fin}\left(d\right)} (\operatorname{ite}\left(m = n, 0, \left\lVert rho\left((n, n), (m, m)\right) - rho\left((n, m), (m, n)\right) \right\rVert\right)))$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.mixedApproxNegativity` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Equation (17b), p. 8: N_a → ½ Σ_(n,m≠n) |ρ_nn,mm − ρ_nm,mn|. The factor one half and ordered unequal-pair summation are retained, with zero on the diagonal.

**Definition 1.6 (The mixed-state logarithmic expression).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right)\times\operatorname{Fin}\left(d\right)), \mathbb{C}\right),\; \operatorname{mixedApproxLogNegativity}\left(rho\right) = \operatorname{Real.logb}\left(2, 1 + 2 \cdot \operatorname{mixedApproxNegativity}\left(rho\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.mixedApproxLogNegativity` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Equation (17c), p. 8: LN_a = log₂(1 + 2 N_a). This uses the mixed-state entry expression of Equation (17b).

**Definition 1.7 (The sandwich and its real-amplitude equality).**

$$claim \Leftrightarrow ((\forall d \in \mathbb{N},\; \forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \mathbb{R},\; \forall C \in \operatorname{Fin}\left(K\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(K\right),\; 0 \le p\left(i\right)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(K\right)} (p\left(i\right)) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(K\right),\; (\operatorname{Matrix.PosSemidef}\left(C\left(i\right)\right)) \land (\operatorname{Matrix.trace}\left(C\left(i\right) \cdot \operatorname{Matrix.conjTranspose}\left(C\left(i\right)\right)\right) = 1)) \Rightarrow (((\sum_{i: \operatorname{Fin}\left(K\right)} (p\left(i\right) \cdot \operatorname{pureApproxLogNegativity}\left(C\left(i\right)\right)) \le \operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right)) \land (\operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right) \le \operatorname{mixedApproxLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right))) \land ((\forall i \in \operatorname{Fin}\left(K\right),\; \operatorname{Matrix.transpose}\left(C\left(i\right)\right) = C\left(i\right)) \Rightarrow (\operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right) = \operatorname{mixedApproxLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.claim` (`✓ std3`).

*Citation.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Section IV, p. 11, Equation (22): "we have numerically found that 𝓛𝓝_a^avg(ρ_ab) ≤ LN_e(ρ_ab) ≤ LN_a(ρ_ab) when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|, and in addition the quantum amplitude matrix C_i of each pure state component |ψ_i⟩ = Σ_nm C_i,nm |n,m⟩ is uniformly generated (over the Haar measure) as a positive Hermitian matrix, C_i = C_i† ≥ 0." "Further, we find that the second inequality is surprisingly saturated, i.e. LN_e(ρ_ab) = LN_a(ρ_ab) in Eq.(22), if the uniformly randomly generated C_i matrices above are real, i.e. C_i = C_i^T." The quantifiers cover every finite dimension and finite ensemble, including zero weights and singular positive semidefinite amplitudes. Normalization is trace(C_i C_i adjoint) = 1 and Σ_i p_i = 1. Under Hermitian symmetry, transpose(C_i) = C_i expresses real entries. The average on the left is the weighted average of the pure-state logarithmic expression, rather than the logarithm of the averaged negativity. Universal quantification over the positive Hermitian class includes the source's randomly sampled class.

**Theorem 1.8 (The full sandwich holds).**

$$(\forall d \in \mathbb{N},\; \forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \mathbb{R},\; \forall C \in \operatorname{Fin}\left(K\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(K\right),\; 0 \le p\left(i\right)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(K\right)} (p\left(i\right)) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(K\right),\; (\operatorname{Matrix.PosSemidef}\left(C\left(i\right)\right)) \land (\operatorname{Matrix.trace}\left(C\left(i\right) \cdot \operatorname{Matrix.conjTranspose}\left(C\left(i\right)\right)\right) = 1)) \Rightarrow (((\sum_{i: \operatorname{Fin}\left(K\right)} (p\left(i\right) \cdot \operatorname{pureApproxLogNegativity}\left(C\left(i\right)\right)) \le \operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right)) \land (\operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right) \le \operatorname{mixedApproxLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right))) \land ((\forall i \in \operatorname{Fin}\left(K\right),\; \operatorname{Matrix.transpose}\left(C\left(i\right)\right) = C\left(i\right)) \Rightarrow (\operatorname{exactLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right) = \operatorname{mixedApproxLogNegativity}\left(\operatorname{ensembleState}\left(p, C\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. M. Alsing; R. J. Birrittella (2024). *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*. DOI: [10.3390/foundations5020019](https://doi.org/10.3390/foundations5020019). URL: <https://arxiv.org/abs/2404.13725v1>.

*Commentary.*

Let F be the swap and Q = Σ_i p_i (C_i tensor C_i). The partial transpose of the ensemble is QF; Q is positive semidefinite and commutes with F, and F is a self-adjoint involution. Consequently its trace norm is trace Q = Σ_i p_i (Re trace C_i)². Nonnegative principal two-by-two minors give 1 + 2 N_a(C_i) = (Re trace C_i)². Concavity of the base-two logarithm gives the lower bound. For the upper bound, the real part of each mixed entry difference dominates the weighted nonnegative principal minors, and the complex norm dominates its real part. For transpose-symmetric amplitudes, these comparisons become equalities. No commutativity between different C_i is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.claim`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.ensembleState`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.exactLogNegativity`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.mixedApproxLogNegativity`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.mixedApproxNegativity`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.pureApproxLogNegativity`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.pureApproxNegativity`
- Truth anchor: `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.result`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
