# Readout-Update Commutator Factorization

## Abstract

The readout-update commutator factors on its common domain and has the exact defect norm when bounded.

**Theorem 1.1 (The commutator factors and has the defect norm).**

$$\forall I : Type, tau : \operatorname{Perm}(I), f : I \to \mathbb{C},\\{}\operatorname{readoutUpdateCommutator}(tau, f) = \operatorname{factoredReadoutUpdateCommutator}(tau, f) \land\\{}\forall h : \operatorname{Finite}(I) \lor \operatorname{MemLp}(f, \infty), \Vert \operatorname{boundedReadoutUpdateCommutator}(tau, f, h) \Vert = \Vert \operatorname{boundedReadoutDefect}(tau, f, h) \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization.readout_update_commutator_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be an address type, tau a reversible address permutation, and f a complex readout coefficient. The first conjunct identifies the independently constructed commutator with multiplication by the update defect after the update, on their natural common domain.

For every proof that I is finite or f belongs to lp infinity, the second conjunct states that the norm of the bounded commutator is exactly the lp-infinity norm of the bundled update defect.

A consequence of the shift and multiplication operators is lower-norm localization for scalar complex tridiagonal operators. Let H be l2(Z; C), let e_j have coordinate one at j and zero elsewhere, and let A be an arbitrary bounded complex-linear operator on H. Assume only that (A e_j)_i is zero unless i is j-1, j, or j+1. Define its actual coefficient sequences by a_i = (A e_(i-1))_i, b_i = (A e_i)_i, and c_i = (A e_(i+1))_i. Each coordinate has modulus at most the operator norm of A, because e_j has norm one. Write Mminus for the supremum of the moduli of a_i and Mplus for the supremum of the moduli of c_i.

$A(x)_{i} = a_{i} x_{i - 1}+b_{i} x_{i}+c_{i} x_{i + 1}, i \in \mathbb{Z}$

Here the coefficient suprema are the lp-infinity norms of the bundled sequences. The identity follows first on each coordinate single from the matrix sparsity assumption, and then on all of H by lp.ext_continuousLinearMap. The operators diagonalOperator and updateLinearIsometryEquiv supply bounded coordinate multiplication and the bilateral shift U, where (U x)_i = x_(i-1). Their norm and isometry identities identify A with M_a U + M_b + M_c U inverse. Thus the coefficient representation is derived from the original A.

For every natural number n at least one and integer k, let E_(n,k) be the subspace of vectors whose coordinates vanish outside the integers k+1 through k+n. The restriction of A has domain E_(n,k) and codomain the full space H. In particular its image includes the possible outgoing coordinates k and k+n+1. For any such bounded map B, its lower norm nu(B) is the infimum of the norms of Bx over unit vectors in its domain. The unit spheres here are nonempty: e_(k+1) belongs to E_(n,k).

Put theta = pi/(n+1), set w_j = sin(j theta) for j from one through n, and set w_j = zero at every other integer. This gives a nonzero vector w in H. Let S be its squared norm and T the squared norm of U w - w. The endpoint terms are included in T, including both of them when n is one.

$S = \sum_{j=1}^{n} {w_{j}}^{2} > 0,\\{}T = \sum_{j=0}^{n} {w_{j + 1} - w_{j}}^{2}\\{}T = 2(1-\operatorname{cos}(\theta))S = 4{\operatorname{sin}(\frac{\theta}{2})}^{2}S,\\{}\Vert U(w) - w \Vert = 2\operatorname{sin}(\frac{\theta}{2})\Vert w \Vert$

The coordinate recurrence in `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector` gives the energy identity: multiply the recurrence by the central sine coordinate and sum. Equivalently, take the inner product of w with U w + U inverse w and expand the squared difference. The zero coordinates outside the interval remove the exterior recurrence terms. Since S is positive and sin(theta/2) is nonnegative, the identity yields the exact ratio of norms. It requires neither a closed expression for S nor a computation of the complete finite-path spectrum.

For x in H, define (D_k x)_i = w_(i-k) x_i. Each D_k x belongs to E_(n,k). The family F_x = (D_k x)_k belongs to l2(Z; H). Indeed, the nonnegative double series of squared coordinate moduli has column sum S times the squared modulus of x_i. Summability and reindexing therefore give the exact mass identity below, for arbitrary x of infinite support as well.

$\sum_{k \in \mathbb{Z}} {\Vert D_{k}(x) \Vert}^{2} = S{\Vert x \Vert}^{2}$

In the family of commutators A D_k x - D_k A x, the diagonal b_i cancels. The other two terms have coordinates a_i (w_(i-k-1) - w_(i-k)) x_(i-1) and c_i (w_(i-k+1) - w_(i-k)) x_(i+1). Multiplication has norm Mminus or Mplus, both shifts preserve norms, and the two translated differences of w have the same norm. Apply the triangle inequality in l2(Z; H) to obtain the image estimate. All output coordinates remain in this estimate.

$\Vert (A(D_{k}(x)))_{k} \Vert \leq \sqrt{S}\Vert A(x) \Vert+(M_{-}+M_{+})\sqrt{T}\Vert x \Vert$

Write delta_n for the error displayed below. Given any positive epsilon, choose a unit x with norm(Ax) less than nu(A) + epsilon/2. Set q = norm(Ax) + delta_n + epsilon/2. If every integer window satisfied norm(A D_k x) at least q times norm(D_k x), monotonicity of the l2 norm would give an image-family norm at least q times the square root of S. The image estimate instead bounds it by (q - epsilon/2) times the square root of S. Positivity of S and epsilon gives a contradiction. Consequently an actual integer k satisfies a strict inequality, and D_k x is nonzero. Normalize it to u by multiplying by the reciprocal of its norm. This supplies the unit vector and the strict bound for every positive epsilon. Taking infima gives the other conclusion.

$\delta_{n} = 2(M_{-}+M_{+})\operatorname{sin}(\frac{\pi}{2(n+1)}),\\{}\operatorname{inf}_{k \in \mathbb{Z}} \nu (A|_{E_{n,k}}) \leq \nu (A)+\delta_{n}$

$\forall \varepsilon > 0, \exists k \in \mathbb{Z}, u \in E_{n,k},\\{}\Vert u \Vert = 1 \land \Vert A(u) \Vert < \nu (A)+\delta_{n}+\varepsilon$

These conclusions apply to complex nonselfadjoint operators, to n equal to one, and to zero operators or zero off-diagonal sequences. They use approximate lower-norm vectors and positive epsilon; attainment of either infimum is unnecessary. This is the scalar complex Hilbert-space application of Chandler-Wilde, Chonchaiya and Lindner, On spectral inclusion sets and computing spectra and pseudospectra, Proposition 5.1 and Corollary 5.2, pages 765-766, with the sine choice on page 767, DOI 10.4171/JST/514. The conclusions stated here concern lower norms of input restrictions; spectral inclusion, optimality, and physical-gap assertions require their respective additional statements.

## References

- Truth anchor: `D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization.readout_update_commutator_factorization`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector`
- Dependency: [D5/S3/Quantum/ObserverCommutator](../../Quantum/ObserverCommutator.md)
