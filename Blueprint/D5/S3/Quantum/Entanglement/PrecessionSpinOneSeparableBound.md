# Spin-1 tensor spin-K/2 precession separable bound

## Abstract

The spin-1 tensor spin-K/2 precession protocol has separable bound ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)] for every odd K ≥ 7. This is Conjecture 2, Eq. (32), of Huynh-Vu, Zaw and Scarani (arXiv:2311.00806v2).

**Definition 1.1 (Spin raising matrix).**

$$\forall n \in \mathbb{N},\; \operatorname{Jplus}\left(n\right) = (i: \operatorname{Fin}\left((n + 1)\right)) \mapsto (r: \operatorname{Fin}\left((n + 1)\right)) \mapsto \operatorname{if}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(r\right), \operatorname{ofReal}\left(\operatorname{Real.sqrt}\left(\frac{\operatorname{NatCast}\left(n\right)}{2} \cdot (\frac{\operatorname{NatCast}\left(n\right)}{2} + 1) - (\frac{\operatorname{NatCast}\left(n\right)}{2} - \operatorname{NatCast}\left(\operatorname{val}\left(r\right)\right)) \cdot (\frac{\operatorname{NatCast}\left(n\right)}{2} - \operatorname{NatCast}\left(\operatorname{val}\left(r\right)\right) + 1)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jplus` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

In the standard descending |j,m⟩ basis the raising matrix has entry √(j(j+1)−m(m+1)) on the one-step superdiagonal, with j = n/2, m = j−r and ℏ = 1.

**Definition 1.2 (Spin x matrix).**

$$\forall n \in \mathbb{N},\; \operatorname{Jx}\left(n\right) = \operatorname{smul}\left((\frac{1}{2}: \mathbb{C}), (\operatorname{Jplus}\left(n\right) + \operatorname{conjTranspose}\left(\operatorname{Jplus}\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jx` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

Jx is the Hermitian half-sum of the raising matrix and its conjugate transpose.

**Definition 1.3 (Spin y matrix).**

$$\forall n \in \mathbb{N},\; \operatorname{Jy}\left(n\right) = \operatorname{smul}\left((\frac{1}{2 \cdot I}: \mathbb{C}), (\operatorname{Jplus}\left(n\right) - \operatorname{conjTranspose}\left(\operatorname{Jplus}\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jy` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

Jy is the Hermitian y component obtained from the raising matrix and its conjugate transpose.

**Definition 1.4 (Spin z matrix).**

$$\forall n \in \mathbb{N},\; \operatorname{Jz}\left(n\right) = \operatorname{diagonal}\left((i: \operatorname{Fin}\left((n + 1)\right)) \mapsto \operatorname{ofReal}\left(\frac{\operatorname{NatCast}\left(n\right)}{2} - \operatorname{NatCast}\left(\operatorname{val}\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jz` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

Jz is diagonal in the standard basis with entries n/2 minus the descending index.

**Definition 1.5 (Total angular momentum).**

$$\forall K \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left((2 + 1)\right), \operatorname{Fin}\left((2 + 1)\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left((K + 1)\right), \operatorname{Fin}\left((K + 1)\right), \mathbb{C}\right),\; \operatorname{total}\left(K, A, B\right) = \operatorname{kronecker}\left(A, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left((K + 1)\right), \operatorname{Fin}\left((K + 1)\right), \mathbb{C}\right))\right) + \operatorname{kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left((2 + 1)\right), \operatorname{Fin}\left((2 + 1)\right), \mathbb{C}\right)), B\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.total` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The total operator is J on the tensor product, J^(1) ⊗ I + I ⊗ J^(K/2), represented by the Kronecker sum.

**Definition 1.6 (Precession angle).**

$$\forall K \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(K\right),\; \operatorname{theta}\left(K, k\right) = \frac{2 \cdot Real.pi \cdot \operatorname{NatCast}\left(\operatorname{val}\left(k\right)\right)}{\operatorname{NatCast}\left(K\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.theta` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The k-th protocol angle is 2πk/K for k in Fin K. NatCast is the natural-to-real cast; ofReal is the real-to-complex cast. val is the underlying natural index, and n is twice the spin.

**Definition 1.7 (Precessed observable).**

$$\forall K \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(K\right),\; \operatorname{Jk}\left(K, k\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{Real.cos}\left(\operatorname{theta}\left(K, k\right)\right)\right), \operatorname{total}\left(K, \operatorname{Jx}\left(2\right), \operatorname{Jx}\left(K\right)\right)\right) + \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{Real.sin}\left(\operatorname{theta}\left(K, k\right)\right)\right), \operatorname{total}\left(K, \operatorname{Jy}\left(2\right), \operatorname{Jy}\left(K\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jk` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The protocol uses J_k = cos(2πk/K)J_x + sin(2πk/K)J_y.

**Definition 1.8 (Positive spectral weight).**

$$\forall x \in \mathbb{R},\; \operatorname{positiveWeight}\left(x\right) = \operatorname{if}\left(0 < x, 1, \operatorname{if}\left(x = 0, \frac{1}{2}, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.positiveWeight` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The positive projector weights positive eigenvalues by one, zero by one half, and negative eigenvalues by zero.

**Definition 1.9 (Positive spectral projector).**

$$\forall T \in Type,\; [\operatorname{Fintype}\left(T\right)] [\operatorname{DecidableEq}\left(T\right)] \forall H \in \operatorname{Matrix}\left(T, T, \mathbb{C}\right),\; \operatorname{pos}\left(H\right) = if h: \operatorname{IsHermitian}\left(H\right) then \operatorname{h.cfc}\left(positiveWeight\right) else 0$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.pos` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

pos is the spectral positive projector of Eq. (3), including the source’s half weight at zero. In the Hermitian branch it is Mathlib’s Matrix.IsHermitian.cfc applied to positiveWeight. The finite spectrum requires no continuity hypothesis; its spectral expression is U diag(positiveWeight(eigenvalues)) Uᴴ. The proof h is bound only in that branch, and the non-Hermitian fallback is zero. All protocol observables are Hermitian.

**Definition 1.10 (Protocol average).**

$$\forall K \in \mathbb{N},\; \operatorname{Q}\left(K\right) = \operatorname{smul}\left((\frac{1}{(K: \mathbb{C})}: \mathbb{C}), \sum_{k: \operatorname{Fin}\left(K\right)} \operatorname{pos}\left(\operatorname{Jk}\left(K, k\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Q` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

Q_K is the average of the positive spectral projectors over k in Fin K.

**Definition 1.11 (Product vector).**

$$\forall K \in \mathbb{N},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left((2 + 1)\right)\right),\; \forall b \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left((K + 1)\right)\right),\; \operatorname{productVector}\left(K, a, b\right) = \operatorname{WithLp.toLp}\left(2, (i: \operatorname{Prod}\left(\operatorname{Fin}\left((2 + 1)\right), \operatorname{Fin}\left((K + 1)\right)\right)) \mapsto \operatorname{a}\left(\operatorname{fst}\left(i\right)\right) \cdot \operatorname{b}\left(\operatorname{snd}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.productVector` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The tensor product of a spin-1 vector and a spin-K/2 vector is represented in the product basis by pointwise multiplication of the two coordinates.

**Definition 1.12 (Separable score set).**

$$\forall K \in \mathbb{N},\; \operatorname{scores}\left(K\right) = \{t: \mathbb{R} \mid \exists a \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left((2 + 1)\right)\right),\; \exists b \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left((K + 1)\right)\right),\; (\left\lVert a \right\rVert = 1) \land \left((\left\lVert b \right\rVert = 1) \land (t = \operatorname{re}\left((\operatorname{dotProduct}\left(\operatorname{star}\left((\operatorname{productVector}\left(K, a, b\right)).ofLp\right), \operatorname{mulVec}\left(\operatorname{Q}\left(K\right), (\operatorname{productVector}\left(K, a, b\right)).ofLp\right)\right))\right))\right)\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.scores` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The score set consists of real quadratic expectations on unit product vectors in ℂ³ ⊗ ℂ^(K+1).

**Definition 1.13 (Central binomial coefficient).**

$$\forall K \in \mathbb{N},\; \operatorname{c}\left(K\right) = \frac{1}{2^{(K - 1)}} \operatorname{NatCast}\left(\operatorname{Nat.choose}\left((K - 1), \operatorname{Nat.div}\left((K - 1), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.c` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

c K is 2^{−(K−1)} times the central binomial coefficient. Both K−1 and Nat.div use natural arithmetic (Nat.div is floor division); NatCast casts the binomial coefficient into ℝ.

**Definition 1.14 (Huynh-Vu–Zaw–Scarani Conjecture 2).**

$$claim \Leftrightarrow (\forall K \in \mathbb{N},\; \operatorname{Odd}\left(K\right) \Rightarrow \left(K \ge 7 \Rightarrow \operatorname{IsGreatest}\left(\operatorname{scores}\left(K\right), \frac{1}{2} (1 + \operatorname{c}\left(K\right) \frac{\operatorname{NatCast}\left((K - 1)\right)}{\operatorname{NatCast}\left((K + 1)\right)})\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.claim` (`✓ std3`).

*Citation.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The source states: "The separable bound for {ȷ̃, ȷ̃′} = {1, K/2} with K ≥ 7 is Psep_K({1, K/2}) = ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)]." The source defines the precession protocol by "Jk := e^{−i(2πk/K)Jz/ℏ} Jx e^{i(2πk/K)Jz/ℏ} = cos(2πk/K)Jx + sin(2πk/K)Jy, where k ∈ {0, 1, . . . , K − 1}." Equations (2)–(3) state "PK := (1/K) Σ_{k=0}^{K−1} [Pr(Jk > 0) + ½ Pr(Jk = 0)], QK := (1/K) Σ_k pos(Jk)," and "Here, pos(Jk) is defined on the eigenstates |j, m⟩k of Jk, such that Jk|j, m⟩k = ℏm|j, m⟩k and 2 pos(Jk)|j, m⟩k = [1+sgn(m)]|j, m⟩k, with the usual convention sgn(0) = 0." Conjecture 2 and Eq. (32) are in arXiv v2, §III, PDF p. 8; Eqs. (1)–(3) are on PDF p. 2. The Lean statement binds the natural indices, casts them into ℝ for the final expression, and uses natural-number division in c.

**Theorem 1.15 (Proof of the separable bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/huynh-vu-zaw-scarani-2023-precession-separable-bound` (proved) by `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"huynh-vu-zaw-scarani-2023-precession-separable-bound","declaration_gid":"D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani (2024). *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*. URL: <https://arxiv.org/abs/2311.00806>.

*Commentary.*

The proof diagonalizes the spin-K/2 Jx operator with the binomial eigenbasis, evaluates the rotation average by the K-th root-of-unity filter, decomposes the half-integer sign spectrum, and compresses the product quadratic form to a six-index off-diagonal block. The squared Frobenius estimate is convex in |a₁|² for K ≥ 7 and is attained by the spin-1 middle state and an endpoint singular vector.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jk`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jplus`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jx`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jy`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Jz`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.Q`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.c`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.positiveWeight`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.productVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.scores`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.theta`
- Truth anchor: `D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.total`
