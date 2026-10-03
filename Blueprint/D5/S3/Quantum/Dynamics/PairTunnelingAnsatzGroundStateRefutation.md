# The pair-tunnelling ansatz fails at eight bosons

## Abstract

Volkoff's exact-ground-state conjecture for the two-mode pair-tunnelling ansatz fails in the eight-boson sector.

**Definition 1.1 (Quadratic factors).**

$$\forall c \in \mathbb{R},\; \forall s \in \operatorname{Bool},\; \operatorname{ansatzFactor}\left(c, s\right) = (\operatorname{X}\left(0\right))^{2} + ((\operatorname{C}\left(\operatorname{ite}\left(s, 0 - (((2) \cdot (i)) \cdot (\operatorname{ofReal}\left(c\right))), ((2) \cdot (i)) \cdot (\operatorname{ofReal}\left(c\right))\right)\right)) \cdot (\operatorname{X}\left(0\right))) \cdot (\operatorname{X}\left(1\right)) - (\operatorname{X}\left(1\right))^{2}$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.ansatzFactor` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

The variables X(0) and X(1) denote x and y in the complex polynomial ring on Fin 2; i is the complex imaginary unit. The Boolean s = false selects the +2icxy factor; s = true selects the -2icxy factor. Real parameters are embedded in the complex coefficients by ofReal. In each formula ite(s,a,b) selects a when s is true and b otherwise.

**Definition 1.2 (The source polynomial).**

$$\forall N \in \mathbb{N},\; \forall s \in \operatorname{Bool},\; \forall c \in \mathbb{R},\; \operatorname{ansatzPolynomial}\left(N, s, c\right) = (\operatorname{ansatzFactor}\left(c, false\right))^{\left\lfloor\frac{N}{2}\right\rfloor} + \operatorname{ite}\left(s, 0 - ((\operatorname{ansatzFactor}\left(c, true\right))^{\left\lfloor\frac{N}{2}\right\rfloor}), (\operatorname{ansatzFactor}\left(c, true\right))^{\left\lfloor\frac{N}{2}\right\rfloor}\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.ansatzPolynomial` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

Volkoff writes in Section V.A, pp. 6-7: "Presently, we focus on the case of N even" and defines Eq. (20): |ω_±(c)⟩ := 1/𝒩 [(a₀†² + 2ic a₀†a₁† − a₁†²)^M ± (a₀†² − 2ic a₀†a₁† − a₁†²)^M]|0,0⟩, where c ∈ ℝ, 𝒩 is a normalization factor, and M = N/2. Creation operators commute, so replacing them by x and y gives this polynomial. The displayed floor denotes natural-number division; only even N occurs in the conjecture. The Boolean s = false is the sum and s = true the difference.

**Definition 1.3 (Fock amplitudes).**

$$\forall N \in \mathbb{N},\; \forall s \in \operatorname{Bool},\; \forall c \in \mathbb{R},\; \forall k \in \operatorname{Fin}\left(N + 1\right),\; \operatorname{omega}\left(N, s, c, k\right) = (\operatorname{ofReal}\left(\sqrt{\operatorname{ofNat}\left((\operatorname{factorial}\left(\operatorname{tsub}\left(N, \operatorname{val}\left(k\right)\right)\right)) \cdot (\operatorname{factorial}\left(\operatorname{val}\left(k\right)\right))\right)}\right)) \cdot (\operatorname{coeff}\left(\operatorname{single}\left(0, \operatorname{tsub}\left(N, \operatorname{val}\left(k\right)\right)\right) + \operatorname{single}\left(1, \operatorname{val}\left(k\right)\right), \operatorname{ansatzPolynomial}\left(N, s, c\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.omega` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

The coefficient of x^(N-k)y^k is multiplied by √((N-k)!k!), because (a₀†)^(N-k)(a₁†)^k|0,0⟩ = √((N-k)!k!)|N-k,k⟩. The scalar normalization factor is omitted; nonzero scalar multiplication preserves membership of each eigenspace. Here coeff(m,P) is the coefficient of the exponent vector m in P, single(j,a) is the exponent vector supported at j with value a, and val(k) is the natural value of k : Fin(N+1). The operation tsub is truncated subtraction on natural numbers. Here ofNat denotes the natural-to-real embedding (Mathlib Nat.cast). All real square roots are embedded in ℂ by ofReal.

**Definition 1.4 (Pair tunnelling).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N + 1\right),\; \forall k \in \operatorname{Fin}\left(N + 1\right),\; \operatorname{pairTunnel}\left(N, j, k\right) = \operatorname{ite}\left(\operatorname{val}\left(j\right) + 2 = \operatorname{val}\left(k\right), \operatorname{ofReal}\left(\sqrt{\operatorname{ofNat}\left((((\operatorname{tsub}\left(\operatorname{tsub}\left(N, \operatorname{val}\left(j\right)\right), 1\right)) \cdot (\operatorname{tsub}\left(N, \operatorname{val}\left(j\right)\right))) \cdot (\operatorname{val}\left(j\right) + 1)) \cdot (\operatorname{val}\left(j\right) + 2)\right)}\right), \operatorname{ite}\left(\operatorname{val}\left(k\right) + 2 = \operatorname{val}\left(j\right), \operatorname{ofReal}\left(\sqrt{\operatorname{ofNat}\left((((\operatorname{tsub}\left(\operatorname{tsub}\left(N, \operatorname{val}\left(k\right)\right), 1\right)) \cdot (\operatorname{tsub}\left(N, \operatorname{val}\left(k\right)\right))) \cdot (\operatorname{val}\left(k\right) + 1)) \cdot (\operatorname{val}\left(k\right) + 2)\right)}\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.pairTunnel` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

The source studies "the ground state of a₀†²a₁² + h.c." (Section V.A, p. 7). On |N-k,k⟩, a₁² contributes √(k(k-1)) and a₀†² contributes √((N-k+1)(N-k+2)); thus the transition to |N-k+2,k-2⟩ has their product. Replacing k by k+2 gives √((N-k-1)(N-k)(k+1)(k+2)). The adjoint supplies the reverse entry. Other entries vanish. The resulting matrix is real symmetric and hence Hermitian. The index arithmetic uses natural numbers and tsub denotes their truncated subtraction. Here ofNat denotes the natural-to-real embedding (Mathlib Nat.cast).

**Definition 1.5 (Exact ground state).**

$$\forall N \in \mathbb{N},\; \forall H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right),\; \forall v \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; \operatorname{IsGroundState}\left(H, v\right) \Leftrightarrow ((\neg (v = 0)) \land (\exists eigen \in \mathbb{R},\; (\operatorname{mulVec}\left(H, v\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(eigen\right), v\right)) \land (\forall mu \in \mathbb{R},\; \forall w \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; ((\neg (w = 0)) \land (\operatorname{mulVec}\left(H, w\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(mu\right), w\right))) \Rightarrow (eigen \le mu))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.IsGroundState` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

An exact ground state is a nonzero vector in an eigenspace with the least eigenvalue of the Hermitian Hamiltonian. This formula quantifies a real eigenvalue and compares it with every real eigenvalue having a nonzero eigenvector. Hermitian matrices have only real eigenvalues, so this is precisely the minimal-eigenvalue condition. The symbols mulVec and smul denote matrix action and complex scalar multiplication, respectively; Vector(N) abbreviates Fin(N+1) → ℂ only in these displays.

**Definition 1.6 (Volkoff's conjecture).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; (\operatorname{Even}\left(N\right)) \Rightarrow ((4 \le N) \Rightarrow (\exists c \in \mathbb{R},\; \exists s \in \operatorname{Bool},\; (\neg (\operatorname{omega}\left(N, s, c\right) = 0)) \land (\operatorname{IsGroundState}\left(\operatorname{pairTunnel}\left(N\right), \operatorname{omega}\left(N, s, c\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.claim` (`✓ std3`).

*Citation.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

Volkoff writes in Section V.A, p. 7: "We conjecture that for each N ≥ 4 there exists a value c_N for which |ω_+(c_N)⟩ or |ω_−(c_N)⟩ is the exact ground state." The section fixes even N. The carrier is the full N-boson sector Fin(N+1) → ℂ; s = false/true encodes +/−, and the nonzero condition excludes the zero polynomial state.

**Theorem 1.7 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/volkoff-2016-pair-tunneling-ansatz-ground-state-refutation` (refuted) by `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"volkoff-2016-pair-tunneling-ansatz-ground-state-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. J. Volkoff (2016). *Optimal and near-optimal probe states for quantum metrology of number conserving two-mode bosonic Hamiltonians*. URL: <https://arxiv.org/abs/1610.05807v1>.

*Commentary.*

At N = 8, the positive factorial weights conjugate H to the coefficient action x²∂_y² + y²∂_x². For the sum state, its eigen-equations imply, with t = c², 10t² - 2t - 1 = 0 and 12t³ + 38t² - 12t - 3 = 0. Eliminating the cubic term forces 68t - 26 = 0, which contradicts the quadratic. For the difference state, c = 0 gives the zero vector; otherwise the eigen-equations force the eigenvalue -24t - 18 and 6t² + 4t - 3 = 0. Nonnegative t then satisfies t < 9/20, so the eigenvalue exceeds -144/5. The even and odd coefficient blocks satisfy the annihilating polynomials λ(λ² - 832)(λ² - 112) and λ⁴ - 904λ² + 63504, respectively. If λ < -8√13, then λ² > 832 and both polynomials are nonzero, forcing every eigenvector coordinate to vanish. Thus every real eigenvalue is at least -8√13. The coefficient vector (1,0,-4√13,0,30,0,-4√13,0,1), multiplied by the factorial weights, is a nonzero eigenvector at -8√13 < -144/5, so this is the exact ground energy. A ground-state ansatz would have to attain it. Both Boolean choices therefore fail.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.IsGroundState`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.ansatzFactor`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.ansatzPolynomial`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.omega`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.pairTunnel`
- Truth anchor: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result`
