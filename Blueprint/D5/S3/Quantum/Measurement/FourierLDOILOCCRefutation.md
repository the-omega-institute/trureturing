# The Fourier LDOI LOCC lower bound is not tight

## Abstract

Johnston and Russo ask whether their lower bound for the uniform Fourier LDOI ensemble is tight. In local dimension three a finite tree of complete local Kraus instruments has success probability 1/2, exceeding the proposed value 4/9. This refutes the universal tightness assertion.

**Definition 1.1 (Normalized Fourier entries).**

$$\forall n : \mathbb{N}, \forall i : \operatorname{Fin}\left(n\right), \forall k : \operatorname{Fin}\left(n\right), \operatorname{fourier}\left(n, i, k\right) = \frac{\operatorname{Complex}.\operatorname{exp}\left(\frac{2 \cdot \operatorname{Real}.\operatorname{pi} \cdot \operatorname{Complex}.\operatorname{I} \cdot (\operatorname{val}\left(i\right) : \mathbb{C}) \cdot (\operatorname{val}\left(k\right) : \mathbb{C})}{(n : \mathbb{C})}\right)}{(\operatorname{Real}.\operatorname{sqrt}\left((n : \mathbb{R})\right) : \mathbb{C})}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.fourier` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Example 17, p. 18: "Let n ≥ 3 and consider an orthonormal LDOI basis arising from Definition 6 with A = (1/√2)1ₙ (the all-ones matrix scaled by 1/√2) and U equal to the n-dimensional Fourier matrix." The entries use zero-based Fin n indices and the positive exponential convention. The square root is real; the exponent and the divisor are complex.

**Definition 1.2 (The Fourier LDOI vectors).**

$$\forall n : \mathbb{N}, \forall l : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \forall p : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \operatorname{phi}\left(l\right)\left(p\right) = \operatorname{if} (l.1 = l.2) \operatorname{then} (\operatorname{if} (p.1 = p.2) \operatorname{then} (\operatorname{fourier}\left(n, l.1, p.1\right)) \operatorname{else} (0)) \operatorname{else} (\operatorname{if} (l.1 < l.2) \operatorname{then} (\frac{\operatorname{Pi}.\operatorname{single}\left((l.1, l.2), 1, p\right) + \operatorname{Pi}.\operatorname{single}\left((l.2, l.1), 1, p\right)}{(\operatorname{Real}.\operatorname{sqrt}\left(2\right) : \mathbb{C})}) \operatorname{else} (\frac{\operatorname{Pi}.\operatorname{single}\left((l.2, l.1), 1, p\right) - \operatorname{Pi}.\operatorname{single}\left((l.1, l.2), 1, p\right)}{(\operatorname{Real}.\operatorname{sqrt}\left(2\right) : \mathbb{C})}))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.phi` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Definition 6, p. 9, Eq. (21), specialized as in Example 17: "Define the uniform ensemble E = {(1/n², |ϕᵢⱼ⟩⟨ϕᵢⱼ|) : 1 ≤ i, j ≤ n}, where |ϕᵢⱼ⟩ are the basis vectors." Diagonal labels give the Fourier superpositions of |kk⟩. For i < j the two ordered labels give (|ij⟩ + |ji⟩)/√2 and (|ij⟩ − |ji⟩)/√2. Pi.single is the coordinate basis vector. All functions below have carrier Fin n × Fin n → ℂ.

**Definition 1.3 (Finite-round local Kraus trees).**

$$\begin{aligned}\forall n : \mathbb{N}, \forall g : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \operatorname{Protocol}.\operatorname{leaf}\left(g\right) : \operatorname{Protocol}\left(n\right)\\\forall n : \mathbb{N}, \forall m : \mathbb{N}, \forall K : (\operatorname{Fin}\left(m\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall h : (\sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(a\right)\right) \cdot K\left(a\right) = 1), \forall next : (\operatorname{Fin}\left(m\right)) \to \operatorname{Protocol}\left(n\right), \operatorname{Protocol}.\operatorname{alice}\left(K, h, next\right) : \operatorname{Protocol}\left(n\right)\\\forall n : \mathbb{N}, \forall m : \mathbb{N}, \forall K : (\operatorname{Fin}\left(m\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall h : (\sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(a\right)\right) \cdot K\left(a\right) = 1), \forall next : (\operatorname{Fin}\left(m\right)) \to \operatorname{Protocol}\left(n\right), \operatorname{Protocol}.\operatorname{bob}\left(K, h, next\right) : \operatorname{Protocol}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.Protocol` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

The inductive type has precisely leaf, alice and bob constructors. A leaf reports an ordered label. Each internal node applies a complete square local Kraus instrument on its indicated side and chooses a child from the classical outcome. Instruments farther down a tree may depend on the entire preceding outcome history. The displayed constructor telescopes describe these generators; the carrier is the inductive type, with no additional constructors.

**Definition 1.4 (Alice's local action).**

$$\forall n : \mathbb{N}, \forall K : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \forall p : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \operatorname{actA}\left(K, v\right)\left(p\right) = \sum_{a : \operatorname{Fin}\left(n\right)} K\left(p.1, a\right) \cdot v\left((a, p.2)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.actA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Alice multiplies the first coordinate, leaving the second coordinate fixed. Vectors are unnormalized after an outcome, so their squared norm includes the branch probability.

**Definition 1.5 (Bob's local action).**

$$\forall n : \mathbb{N}, \forall K : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \forall p : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \operatorname{actB}\left(K, v\right)\left(p\right) = \sum_{a : \operatorname{Fin}\left(n\right)} K\left(p.2, a\right) \cdot v\left((p.1, a)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.actB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Bob multiplies the second coordinate, leaving the first coordinate fixed.

**Definition 1.6 (Squared Euclidean norm).**

$$\forall n : \mathbb{N}, \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \operatorname{mass}\left(v\right) = \sum_{p : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)} \operatorname{Complex}.\operatorname{normSq}\left(v\left(p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.mass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

The squared norm is the sum of Complex.normSq over every coordinate, rather than the norm of the product-space function with the supremum norm.

**Definition 1.7 (Correct-leaf mass).**

$$\begin{aligned}\forall n : \mathbb{N}, \forall l : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \forall g : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \operatorname{score}\left(l, \operatorname{Protocol}.\operatorname{leaf}\left(g\right), v\right) = \operatorname{if} (g = l) \operatorname{then} (\operatorname{mass}\left(v\right)) \operatorname{else} (0)\\\forall n : \mathbb{N}, \forall m : \mathbb{N}, \forall l : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \forall K : (\operatorname{Fin}\left(m\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall h : (\sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(a\right)\right) \cdot K\left(a\right) = 1), \forall next : (\operatorname{Fin}\left(m\right)) \to \operatorname{Protocol}\left(n\right), \operatorname{score}\left(l, \operatorname{Protocol}.\operatorname{alice}\left(K, h, next\right), v\right) = \sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{score}\left(l, next\left(a\right), \operatorname{actA}\left(K\left(a\right), v\right)\right)\\\forall n : \mathbb{N}, \forall m : \mathbb{N}, \forall l : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right), \forall v : (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{C}, \forall K : (\operatorname{Fin}\left(m\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall h : (\sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(a\right)\right) \cdot K\left(a\right) = 1), \forall next : (\operatorname{Fin}\left(m\right)) \to \operatorname{Protocol}\left(n\right), \operatorname{score}\left(l, \operatorname{Protocol}.\operatorname{bob}\left(K, h, next\right), v\right) = \sum_{a : \operatorname{Fin}\left(m\right)} \operatorname{score}\left(l, next\left(a\right), \operatorname{actB}\left(K\left(a\right), v\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.score` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

The recursion sums the squared norms of the leaves whose guesses equal the supplied label. At every internal node the unnormalized vector is passed through its local Kraus operator. Repeated recursion therefore applies the product of the operators on each path.

**Definition 1.8 (Uniform success probability).**

$$\forall n : \mathbb{N}, \forall T : \operatorname{Protocol}\left(n\right), \operatorname{success}\left(n, T\right) = \frac{1}{(n : \mathbb{R})^{2}} \cdot (\sum_{l : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)} \operatorname{score}\left(l, T, \operatorname{phi}\left(l\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.success` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Example 17, p. 18: "Define the uniform ensemble E = {(1/n², |ϕᵢⱼ⟩⟨ϕᵢⱼ|) : 1 ≤ i, j ≤ n}, where |ϕᵢⱼ⟩ are the basis vectors." Section 1, p. 4, defines the success probability as the prior-weighted probability of reporting the correct state. Here the prior is 1/n², and all n² labels are included, even though the counterexample never reports a diagonal label.

**Definition 1.9 (The LOCC optimization supremum).**

$$\forall n : \mathbb{N}, \operatorname{optLOCC}\left(n\right) = \operatorname{sSup}\left(\operatorname{Set}.\operatorname{range}\left(\operatorname{success}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.optLOCC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Acknowledgement.* Eric Chitambar, Debbie Leung, Laura Mančinska, Maris Ozols, Andreas Winter (2014). *Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask)*. DOI: [10.1007/s00220-014-1953-9](https://doi.org/10.1007/s00220-014-1953-9). URL: <https://arxiv.org/abs/1210.4583>.

*Commentary.*

Section 1, p. 4: "We use the notation optPPT(E) and optSEP(E) for the optimal success probabilities under PPT and separable measurements, and optLOCC(E) for the supremum over LOCC measurements (since LOCC is not topologically closed, the supremum may not be attained)." Here optLOCC is the supremum over finite-round LOCC (LOCC_ℕ) trees with dimension-preserving local Kraus instruments. Chitambar–Leung–Mančinska–Ozols–Winter, Section 2.2, gives LOCC_ℕ ⊆ LOCC ⊆ cl(LOCC_ℕ); success is a continuous linear functional of the measurement, so the supremum equals that over all LOCC measurements. Every finite-round LOCC measurement has this tree form, since each Kraus operator's output space pulls back by polar decomposition. These carrier correspondences are arguments on paper, not Lean theorems. The completeness of every local instrument bounds each tree's success probability by one.

**Definition 1.10 (The lower bound in Equation (61)).**

$$\forall n : \mathbb{N}, \operatorname{lower}\left(n\right) = \frac{1}{2} - \frac{(n : \mathbb{R}) - 2}{2 \cdot (n : \mathbb{R})^{2}}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.lower` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Example 17, p. 18, Eq. (61), gives this lower bound and the PPT upper bound 1/2. Every arithmetic operation displayed here takes place in ℝ, with n coerced from ℕ.

**Definition 1.11 (The tightness equality).**

$$claim \Leftrightarrow (\forall n : \mathbb{N}, (3 \le n) \Rightarrow (\operatorname{optLOCC}\left(n\right) = \operatorname{lower}\left(n\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.claim` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

Example 17, p. 19: "Whether the lower bound in Equation (61) is tight—that is, whether opt_LOCC(E) = 1/2 − (n − 2)/(2n²)—remains an open question." The encoding asserts this equality for every n ≥ 3, with optLOCC the supremum over finite-round LOCC trees with dimension-preserving local Kraus instruments. Every finite-round LOCC measurement has this form, since each Kraus operator's output space pulls back by polar decomposition.

**Theorem 1.12 (Tightness fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnston-russo-2026-fourier-ldoi-locc-tightness` (refuted) by `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnston-russo-2026-fourier-ldoi-locc-tightness","declaration_gid":"D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo (2026). *Distinguishability of locally diagonal orthogonally invariant quantum states*. URL: <https://arxiv.org/abs/2604.12808v1>.

*Commentary.*

At n = 3 Alice first selects an unordered pair with its diagonal projector divided by √2. Bob tests membership in that pair. Inside it a shared fair choice of X or Y measurements resolves the symmetric and antisymmetric labels; outside it computational outcomes and a fair sign guess are used. The X and Y instruments include the complementary level as a third outcome and reset measured factors using |0⟩⟨x|. A zero-probability branch receives the fixed label (0,1). All local instruments are complete. Each of the six off-diagonal states has correct-leaf mass 3/4, and all three diagonal states have correct-leaf mass zero. The uniform success is therefore (6 · 3/4)/9 = 1/2, while lower(3) = 4/9. Local completeness and induction on the tree bound every success probability by one, so the supremum is bounded and optLOCC(3) ≥ 1/2 > lower(3). Only this dimension-three refutation is asserted; an all-dimension family and the exact optimization value are separate statements.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.Protocol`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.actA`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.actB`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.fourier`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.lower`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.mass`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.optLOCC`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.phi`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.score`
- Truth anchor: `D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.success`
