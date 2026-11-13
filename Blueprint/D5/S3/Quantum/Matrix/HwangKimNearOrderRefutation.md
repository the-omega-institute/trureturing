# The log-Euclidean mean and Wasserstein near order

## Abstract

Two positive definite complex matrices refute the proposed near-order comparison of the log-Euclidean and Wasserstein means.

**Definition 1.1 (Near order).**

$$\forall m: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\operatorname{NearOrder}\left(A, B\right)) \Leftrightarrow (1 \le \operatorname{geometricMean}\left(\frac{1}{2}, A^{-1}, B\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.NearOrder` (`✓ std3`).

*Citation.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Hwang and Kim, page 5, equation (3.5): “For A, B ∈ ℙ,” followed by “A ≼ B if and only if A⁻¹ # B ≥ I.” Here matrices have indices Fin m, inverse means Matrix nonsingular inverse, and geometricMean has weight 1/2. MatrixOrder is the positive semidefinite order.

**Definition 1.2 (The log-Euclidean mean).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, \forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \operatorname{logEuclidean}\left(w, A\right) = \operatorname{cfc}\left(\operatorname{Real}.\operatorname{exp}, \sum_{j: \operatorname{Fin}\left(n\right)} (w(j) \cdot \operatorname{cfc}\left(\operatorname{Real}.\operatorname{log}, A(j)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.logEuclidean` (`✓ std3`).

*Citation.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Page 9, equation (4.10), defines “exp [∑ⁿⱼ₌₁ wⱼ log Aⱼ] =: LE(ω; 𝔸).” The finite index Fin n enumerates the n inputs; cfc applies Real.log and Real.exp to the matrices.

**Definition 1.3 (The Bures–Wasserstein distance).**

$$\forall m: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \operatorname{buresWassersteinDistance}\left(A, B\right) = \operatorname{Real}.\operatorname{sqrt}(\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(A + B)) - 2 \cdot \operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(\operatorname{mpow}\left(\operatorname{mpow}\left(A, \frac{1}{2}\right) \cdot B \cdot \operatorname{mpow}\left(A, \frac{1}{2}\right), \frac{1}{2}\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.buresWassersteinDistance` (`✓ std3`).

*Citation.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Page 4, Section 2: “where dW(A, B) = [tr(A + B) − 2 tr(A¹ᐟ² B A¹ᐟ²)¹ᐟ²]¹ᐟ² is the Bures-Wasserstein distance of A, B ∈ ℙₘ.” SpectralPower.mpow is the real spectral power. Complex traces are read through Complex.re.

**Definition 1.4 (The Wasserstein barycenter).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, \forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \operatorname{wassersteinBarycenter}\left(w, A\right) = \operatorname{Classical}.\operatorname{epsilon}(\lambda X: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{PosDef}(X)) \land (\forall Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{PosDef}(Y)) \Rightarrow (\sum_{j: \operatorname{Fin}\left(n\right)} (w(j) \cdot \operatorname{buresWassersteinDistance}\left(X, A(j)\right)^{2}) \le \sum_{j: \operatorname{Fin}\left(n\right)} (w(j) \cdot \operatorname{buresWassersteinDistance}\left(Y, A(j)\right)^{2}))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.wassersteinBarycenter` (`✓ std3`).

*Citation.* Rajendra Bhatia; Tanvi Jain; Yongdo Lim (2018). *Inequalities for the Wasserstein mean of positive definite matrices*. URL: <https://arxiv.org/abs/1803.03357>.

*Commentary.*

Bhatia, Jain and Lim, arXiv:1803.03357, page 1, equation (2): “Let A₁, …, Aₘ be given positive definite matrices and let w = (w₁, …, wₘ) be a vector of weights; i.e., wⱼ ≥ 0 and ∑ⱼ₌₁ᵐ wⱼ = 1. Then the (weighted) Wasserstein mean, or the Wasserstein barycentre of A₁, …, Aₘ is defined as”. Equation (2) displays Ω as the argmin of the weighted squared distances. Here n counts the inputs and m is the matrix dimension; Fin n enumerates the inputs. Classical.epsilon selects that minimizer. The formula below includes both positive definiteness and comparison with every positive definite matrix.

**Definition 1.5 (The final open inequality).**

$$(claim) \Leftrightarrow (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < w(j)) \Rightarrow ((\sum_{j: \operatorname{Fin}\left(n\right)} (w(j)) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{Matrix}.\operatorname{PosDef}(A(j))) \Rightarrow (\operatorname{NearOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.claim` (`✓ std3`).

*Citation.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Hwang and Kim, arXiv:2407.07438v1, page 17, §6: “It would be an interesting problem to study whether the weak log-majorization relation generalizes to the near-order or entrywise eigenvalue relation. Note that (6.21) is a generalization of (4.14). From this point of view, we give an open question:” The following display is “LE(ω; 𝔸) ≼ Ω(ω; 𝔸).” Here m is the complex matrix dimension, n is the number of inputs, w gives strictly positive weights summing to one, and every A j is positive definite. Fin n replaces the source indices 1,…,n. The assertion retains all dimensions m ≥ 1 and all input counts n ≥ 2.

**Theorem 1.6 (A counterexample in dimension two).**

$$\neg (\forall m: \mathbb{N}, (1 \le m) \Rightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow (\forall w: \operatorname{Fin}\left(n\right) \to \mathbb{R}, (\forall j: \operatorname{Fin}\left(n\right), 0 < w(j)) \Rightarrow ((\sum_{j: \operatorname{Fin}\left(n\right)} (w(j)) = 1) \Rightarrow (\forall A: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (\forall j: \operatorname{Fin}\left(n\right), \operatorname{Matrix}.\operatorname{PosDef}(A(j))) \Rightarrow (\operatorname{NearOrder}\left(\operatorname{logEuclidean}\left(w, A\right), \operatorname{wassersteinBarycenter}\left(w, A\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hwang-kim-2024-near-order-log-euclidean-wasserstein` (refuted) by `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hwang-kim-2024-near-order-log-euclidean-wasserstein","declaration_gid":"D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jinmi Hwang; Sejong Kim (2024). *Near-order relation of power means*. DOI: [10.1007/s11117-024-01099-4](https://doi.org/10.1007/s11117-024-01099-4). URL: <https://arxiv.org/abs/2407.07438v1>.

*Commentary.*

Take A = diag(4,1) and B = [[19,−3√15],[−3√15,61]]/64, at weights (1/2,1/2). Both matrices are positive definite. Let L be their log-Euclidean mean and W their Wasserstein barycenter. Their explicit formulas give det L = 1 and det W = d² with d > 0. For C = geometricMean(1/2,L⁻¹,W), positivity and CLC = W imply det C = d. If I ≤ C, positive semidefiniteness of C−I forces tr C ≤ 1+d. Cayley–Hamilton trace identities then force (tr W+d tr L)² ≤ (1+d)²(tr(LW)+2d), whereas rational bounds for √√2 and √265 make the difference greater than 3/2500. The barycenter identity follows by minimizing the actual sum of squared distances, using a trace-norm inequality with its equality condition. The separate entrywise-eigenvalue question is not answered by this theorem.

## Complete revision2 companion scope

Complete revision2 source: Counterexamples beyond Bhatia–Jain–Lim (2018): Hwang–Kim's near-order question and its entrywise companion, Haobo Ma and Wenlin Zhang, 9 November 2026, CC BY 4.0. The complete revision2 TeX note contains these companion outcomes. Haobo Ma: ChronoAI Pte Ltd, Singapore only. Wenlin Zhang: National University of Singapore and ChronoAI Pte Ltd, Singapore. The manuscript's historical Lean reference is commit 6974dba01daa1a25cc74b87a86c191e95fe2c681; a source handoff or new formal package is not a new scientific discovery, publication or priority claim. The original result above remains the universal near-order refutation. The separate HwangKimStrictSpectralConverseRefutation.result proves that this same actual witness also has strict domination of both decreasingly ordered eigenvalues, so the spectral converse fails.

The finite dual lemma retains W,Aⱼ,Tⱼ positive definite, every wⱼ>0, Σwⱼ=1, TⱼWTⱼ=Aⱼ and ΣwⱼTⱼ=I. The original fidelity inequality 2F(X,A)≤tr(TX)+tr(T⁻¹A) has equality only if TXT=A. Summing the positive weighted gaps proves a global lower bound attained at W. Equality makes each gap zero and one invertible transport forces X=W. BuresWassersteinTransport.finite_barycenter_of_dual formalizes the lower bound for all X>0, uniqueness and the actual epsilon-selected argmin. The established optimality condition is due to Bhatia–Jain–Lim, arXiv:1712.01504v1 Theorem 8, (62)–(63), with Riccati equation (9). This finite formal inference reuses the original private fidelity proofs.

For arbitrary positive definite 2×2 L,W with det L=1, put d=√det W, s=tr W, t=tr L, r=tr(LW), E=(s+dt)²−(1+d)²(r+2d), using real traces and determinant. HwangKimTwoDimensionalCriterion.near_order_iff proves exactly NearOrder L W iff d≥1 and E≤0. For the actual positive transport C=L⁻¹#W, CLC=W and det C=d; Cayley–Hamilton gives s+dt=tr(LC)tr C and tr(LC)²=r+2d. Positivity gives tr(LC)>0, hence E≤0 iff tr C≤1+d. Together with det C≥1, the positive eigenvalues c₁,c₂ obey (c₁−1)(c₂−1)≥0 and must both be ≥1. The determinant condition and both positivity hypotheses are essential parts of the statement.

The second written witness uses weights (3/4,1/4), A*=diag(256,1), B*=[[13,3√3],[3√3,7]]/4. With h=√399, K*=[[9,2√3],[2√3,90]]/(4h) and M*=(3I+K*)/4, K*A*K*=B* and the transports M*⁻¹,K*M*⁻¹ identify W*=M*A*M*. Its trace is 1159/8+3591/(16h), and √det W*=73/8+297/(4h). The source proves λmin(W*)<107/100<λmin(L*), where λmin(L*)=2^((13−√157)/4). The exact bounds √157<63/5 and (107/100)^10<2 separate the logarithmic eigenvalue; 1997/100<h<999/50 makes the characteristic polynomial of W* at 107/100 smaller than −9/10. HwangKimWeightedSpectralRefutation.result supplies the separate actual-mean entrywise refutation, including both strict threshold bounds on its live proof path. A separate checked exact application also excludes near order for this same actual pair: C≥I implies C²≥I, so W−qI=C(L−qI)C+q(C²−I)≥0, contradicting its negative determinant. These are separate from the original result; the source's finite checker alone is not a formal proof of them.

The commuting finite-input outcome retains every strictly positive normalized weight. In a single common unitary eigenbasis, write the positive coordinates aⱼₖ and vₖ=Σⱼwⱼ√aⱼₖ. Then LE has coordinates ∏ⱼaⱼₖ^wⱼ and Ω has coordinates vₖ²; Tⱼ=diag(√aⱼₖ/vₖ) supplies the actual barycenter certificate. Scalar weighted AM–GM gives Loewner and near order; strict concavity of log makes equality equivalent to all inputs coinciding. Bhatia–Jain–Lim (2018), equations (18) and (22), already publishes the commuting formulas. An exact application check proves the displayed actual mean formulas, Loewner comparison and equality condition for arbitrary finite diagonal positive inputs by the finite transport certificate and existing scalar AM–GM. The full commuting-family application, simultaneous diagonalization, actual argmin identification and the strict-positive-weight equality condition remain full formal obligations; sorted spectra of individually diagonalized inputs do not supply a common basis.

Both written counterexample families quantify over every matrix size m≥2 and every input count n≥2, with suitable chosen strictly positive normalized weights, not every prescribed vector. Direct sums with Iₘ₋₂ must be identified for the actual log-Euclidean, geometric and argmin means. Repeat the first input n−1 times: assign weight 1/(2(n−1)) to each copy and 1/2 to the second input in the first example, or 3/(4(n−1)) and 1/4 in the second. Logarithmic sums and objectives then agree exactly with the two-input versions. Identity padding changes the full-size minimum eigenvalues. For the second example, use the count of eigenvalues above q=107/100: the L block has two and the W block has at most one; added identity eigenvalues lie below q. Thus the separated sorted index is the second largest, not a claimed full-size minimum separator. These direct-sum and repetition bridges are not consequences of merely negating a universal claim.

The remaining reverse consequences use their established premises with attribution. Bhatia–Jain–Lim (2018), Theorem 1 / (19), proves LE weakly log-majorized by Ω; combined with the second witness this separates weak log-majorization from entrywise order. Their (54) gives LE≤λQ₁/₂, where Q₁/₂=(ΣwⱼAⱼ¹/²)², and the same second witness obstructs the unposed stronger entrywise Q₁/₂≤λΩ reading. Q₁/₂ is not Ω. Their actual Conjecture 1 / (25) asks weak majorization, equivalently all unitarily invariant norms, and is not refuted. Hiai arXiv:2508.20309v2 Propositions 4.6–4.7 compares binary weighted LE with the quasi-arithmetic Aα,q; at q=1/2 the right side is Q₁/₂, not Ω. Gan–Huang's near-to-entrywise implication is distinct from its spectral-geometric-versus-Wasserstein comparison. For commuting X,Y, near and Loewner order agree coordinatewise in a common basis; X=diag(2,1), Y=diag(1,2) shows that identical sorted spectra are insufficient.

Source coverage is finite and exact: Hwang–Kim §6 p.17 final unnumbered question is the original settled target; (6.21) is a different proved arithmetic–LE–harmonic comparison. Their Theorem 6.1 and Corollary 6.2 Lie–Trotter assertions are prior results with no extension here. The all-r analytic small-rotation family and full reverse-implication classification remain open. The source's rational checker covers displayed identities and bounds for two specific witnesses; it does not establish those open families. Primary-source access and priority are bounded by the literature record in the source notes; unread journal/citing bodies and completeness of the priority search remain unverified. No cited comparison is installed as an axiom. The complete eight-group return is not certified by the original result, these exposition paragraphs, a scoped build or a push; remaining actual consumers, admissibility audits, independent review and final-head CI are separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.NearOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.buresWassersteinDistance`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.logEuclidean`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.wassersteinBarycenter`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Hiai/PsiMeanTraceConcavity](../Hiai/PsiMeanTraceConcavity.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](AlternativeMeanLinearization.md)
- Dependency: [D5/S3/Quantum/Matrix/GanKimConjectureRefutation](GanKimConjectureRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)
