---
bibkey: krishna2021cstarnovak
authors: K. Mahesh Krishna
year: 2021
title: "C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture"
doi: 10.48550/arXiv.2108.06662
url: https://arxiv.org/abs/2108.06662v1
claim: "Conjecture 4.3 asserts positivity of the ordered cosine-product matrix over every unital C*-algebra; Theorem 4.4 proves the commutative case."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarNovak
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2108.06662

Source: https://arxiv.org/abs/2108.06662v1

Journal: *Journal of the Korean Mathematical Society* 59(4) (2022), 789–804,
DOI: https://doi.org/10.4134/JKMS.j210627.

## Source statements

All page numbers below refer to arXiv:2108.06662v1.

Section 2, p. 4, defines positivity of a matrix over \(\mathcal A\):

> Similar to the scalar case, \(A\coloneqq [a_{j,k}]_{1\leq j,k \leq n}\in M_n(\mathcal{A})\) is said to be positive if it is self-adjoint and \(\langle Ax, x \rangle \geq 0, \quad \forall x \in \mathcal{A}^n\), where \(\geq\) is the partial order on the set of all positive elements of \(\mathcal{A}\).

Section 4, Definition 4.1, p. 9:

> Define the **C*-algebraic cosine** function by \(\cos: \mathcal{A}\ni x \mapsto \cos x \coloneqq \frac{e^{ix}+e^{-ix}}{2}\in \mathcal{A}.\)

The preceding exponential map is
\(e:\mathcal A\ni x\mapsto e^x\coloneqq\sum_{n=0}^{\infty}x^n/n!\in\mathcal A\).

Conjecture 4.3, p. 10, **C*-algebraic Novak's conjecture**:

> Let \(\mathcal{A}\) be a unital C*-algebra. Then the matrix \(\begin{bmatrix}\prod_{l=1}^{d} \frac{1+\cos (x_{j,l}-x_{k,l})}{2}-\frac{1}{n}\end{bmatrix}_{1\leq j,k \leq n}\) is positive for all \(n,d\geq 2\) and all choices of \(x_j=(x_{j,1}, \dots, x_{j,d})\in \mathcal{A}_\text{sa}^d\), \(\forall 1\leq j \leq n\).

Theorem 4.4, p. 10, **Commutative C*-algebraic Novak's conjecture**:

> Let \(\mathcal{A}\) be a commutative unital C*-algebra. Then the matrix \(\begin{bmatrix}\prod_{l=1}^{d} \frac{1+\cos (x_{j,l}-x_{k,l})}{2}-\frac{1}{n}\end{bmatrix}_{1\leq j,k \leq n}\) is positive for all \(n,d\geq 2\) and all choices of \(x_j=(x_{j,1}, \dots, x_{j,d})\in \mathcal{A}_\text{sa}^d\), \(\forall 1\leq j \leq n\).

## Encoding and conclusion

The Lean definitions use `NormedSpace.exp`, whose complex exponential series is
`NormedSpace.exp_series_hasSum_exp'`, and multiply the factors in increasing
`Fin d` order through `List.ofFn` and `List.prod`. The scalar \(1/n\) is
`(n : ℂ)⁻¹ • 1`. Indices `Fin n` and `Fin d` correspond to the source's
indices by adding one. Self-adjointness is `IsSelfAdjoint`; matrix positivity
is the conjunction of star-transposed entry equality and nonnegativity of
\(\sum_j\sum_k M_{jk}v_kv_j^*\), the source's left-linear form.

`claim` quantifies `A : Type` with `CStarAlgebra`, `PartialOrder` and
`StarOrderedRing`. Mathlib's `CStarAlgebra` is unital. The restriction to `Type`
weakens the universe range of the source claim, so its negation refutes the
source statement. The compatible order on the counterexample is Mathlib's
matrix positive-semidefinite order.

The repository result refutes Conjecture 4.3 at \(n=3,d=2\) in
\(M_2(\mathbb C)\). It uses
\(A_1=3\pi I\), \(A_2=\pi\operatorname{diag}(5,1)\), and
\(A_3=(\pi/4)\begin{pmatrix}19&\sqrt{15}\\\sqrt{15}&5\end{pmatrix}\),
repeating each coordinate in both positions. Their squared differences are
\(4\pi^2I,4\pi^2I,\pi^2I\), and their cosines are \(I,I,-I\).
For \(v=(-2,1,1)I\), the quadratic form is \(-2I\).
The source's commutative Theorem 4.4 is unaffected.

## Literature boundary

The preregistration's source and literature checks found no published settlement
of Conjecture 4.3. The probe's inspected arXiv results also supplied none;
general-web and citation coverage was incomplete. Global absence of an earlier
settlement is ASSUMED-UNVERIFIED. This is separate from the kernel-checked
counterexample.
