# Zernike ladder factorization for every order

## Abstract

The generalized polynomial quantum Zernike Hamiltonian has ladders with the factorized structure function for every N.

**Definition 1.1 (The factorized ladder assertion).**

$$claim = \forall (N: \mathbb{N}), (1 \leq N) \implies (\forall (gamma: \mathbb{N} \to \mathbb{C}), \exists (I: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \exists (I': \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (\operatorname{IsSymmetry}\left(N, gamma, (\operatorname{p}\left(1\right))^{2}, I\right)) \land (\operatorname{IsSymmetry}\left(N, gamma, (\operatorname{p}\left(0\right))^{2}, I'\right)) \land (\exists (K: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (K \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (\exists (Kp: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (Kp \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (\exists (Km: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (Km \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (((K) * (Kp) - (Kp) * (K) = Kp) \land ((K) * (Km) - (Km) * (K) = -(Km)) \land ((Kp) * (Km) = \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K\right)) \land ((Km) * (Kp) - (Kp) * (Km) = \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K + 1\right) - \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K\right)))))))$$

*Formalization.* `D5/S3/Quantum/CampoamorStursbergZernikeLadder.claim` (`✓ std3`).

*Citation.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

The set (Ĉ, Î_N, Î'_N) leads to the quantum symmetries K̂₁, K̂₂, K̂₃ in (2.8) and, in consequence, it is possible to define the number and ladder operators K̂, K̂₊, K̂₋ verifying the commutation relations (2.9) with the structure function Φ = Φ₁Φ₂ (2.10), whose factorizing terms are given by Φ₁(Ĥ_N, K̂) = ¼ (Ĥ_N − Σ_{k=1}^N (2i)^k γ_k K̂^k), Φ₂(Ĥ_N, K̂) = Ĥ_N − Σ_{k=1}^N (−2i)^k γ_k (K̂ − Id)^k. (5.1)

The quotation is Conjecture 1(iii), page 19 of arXiv:2502.02491v2. The displayed proposition uses complex linear endomorphisms of MvPolynomial (Fin 2) Complex, source coordinates 1 and 2 indexed by Fin 2 values 0 and 1, every N at least 1, and every complex coefficient sequence gamma. Only coefficients 1 through N occur. IsSymmetry specifies the positive-degree, grading-zero span in (2.6) and commutation with the Hamiltonian. Membership in Algebra.adjoin expresses construction from the three operators of (2.8). angularMomentum is the source K1. Products are operator composition; a centered dot is scalar multiplication.

**Theorem 1.2 (Ladders with the factorization (5.1)).**

$$\forall (N: \mathbb{N}), (1 \leq N) \implies (\forall (gamma: \mathbb{N} \to \mathbb{C}), \exists (I: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), \exists (I': \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (\operatorname{IsSymmetry}\left(N, gamma, (\operatorname{p}\left(1\right))^{2}, I\right)) \land (\operatorname{IsSymmetry}\left(N, gamma, (\operatorname{p}\left(0\right))^{2}, I'\right)) \land (\exists (K: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (K \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (\exists (Kp: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (Kp \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (\exists (Km: \operatorname{Module}.\operatorname{End}(\mathbb{C}, \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right))), (Km \in \operatorname{Algebra}.\operatorname{adjoin}(\mathbb{C}, \{k1, \operatorname{k2}\left(I, I'\right), \operatorname{k3}\left(I, I'\right)\})) \land (((K) * (Kp) - (Kp) * (K) = Kp) \land ((K) * (Km) - (Km) * (K) = -(Km)) \land ((Kp) * (Km) = \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K\right)) \land ((Km) * (Kp) - (Kp) * (Km) = \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K + 1\right) - \operatorname{phi}\left(N, gamma, \operatorname{hamiltonian}\left(N, gamma\right), K\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CampoamorStursbergZernikeLadder.result` (`✓ std3`). ∎

*Resolves.* `Problems/campoamor-stursberg-et-al-2025-zernike-ladder-factorization` (proved) by `D5/S3/Quantum/CampoamorStursbergZernikeLadder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"campoamor-stursberg-et-al-2025-zernike-ladder-factorization","declaration_gid":"D5/S3/Quantum/CampoamorStursbergZernikeLadder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco (2026). *Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum*. DOI: [10.1088/1361-6544/ae64a2](https://doi.org/10.1088/1361-6544/ae64a2). URL: <https://arxiv.org/abs/2502.02491v2>.

*Commentary.*

Put x=p(0)+Complex.I times p(1), y=p(0)-Complex.I times p(1), qp=q(0)+Complex.I times q(1), and qm=q(0)-Complex.I times q(1). The raising operator is half the sum of x squared and x qp times divided(N,gamma,dot,Complex.I times (angularMomentum+2)); the lowering operator is half the sum of y squared and y qm times divided(N,gamma,dot,Complex.I times (2-angularMomentum)). Weyl shift relations and the geometric-sum identity give both ordered products and commutation with the Hamiltonian directly in the endomorphism ring.

The two symmetries are half the Hamiltonian minus or plus half the sum of the ladders. Normal ordering bounds each correction by total degree 2N with grading zero and positive degree. Their k2 is half the sum of the ladders, and k3 is their difference, so the ladders and half the angular momentum belong to the required generated algebra. The two ordered products are phi at half the angular momentum and at its shift by 1.

The conclusion holds for all complex coefficients, including zero coefficients. It gives the degree and momentum-order upper bound in (2.6). Exact order at degenerate coefficients, algebraic independence in Conjecture 1(ii), and analytic Hilbert-space or spectrum conclusions in Conjecture 2 are outside this proposition.

## References

- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadder.claim`
- Truth anchor: `D5/S3/Quantum/CampoamorStursbergZernikeLadder.result`
- Dependency: [D5/S3/Quantum/CampoamorStursbergZernikeLadderCore](CampoamorStursbergZernikeLadderCore.md)
