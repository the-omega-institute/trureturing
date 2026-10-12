---
slug: krishna-2021-cstar-novak-conjecture
bibkey: krishna2021cstarnovak
doi: 10.48550/arXiv.2108.06662
url: https://arxiv.org/abs/2108.06662v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CStarNovak.result
---

# A matrix refutation of Krishna's C*-algebraic Novak conjecture

## Problem

K. Mahesh Krishna, *C*-algebraic Schur product theorem, Pólya-Szegő-Rudin question and Novak's conjecture*, arXiv:2108.06662v1, Conjecture 4.3, p. 10; journal DOI [10.4134/JKMS.j210627](https://doi.org/10.4134/JKMS.j210627), states:

> Let $\mathcal A$ be a unital C*-algebra. Then the matrix $[\prod_{l=1}^d(1+\cos(x_{j,l}-x_{k,l}))/2-1/n]_{1\le j,k\le n}$ is positive for all $n,d\ge2$ and all choices of $x_j=(x_{j,1},\ldots,x_{j,d})\in\mathcal A_{\rm sa}^d$.

The source defines $\cos X=(e^{iX}+e^{-iX})/2$ using the exponential series, and positivity means self-adjointness together with $\langle Mv,v\rangle\ge0$ for every $v\in\mathcal A^n$, where the source's left-linear form is $\sum_j\sum_k M_{jk}v_kv_j^*$.

## Motivation

The conjecture extends the commutative theorem to all unital C*-algebras. Three self-adjoint matrices in $M_2(\mathbb C)$ violate the quadratic-form condition already at $n=3,d=2$.

The Lean definition `claim` quantifies `A : Type` with `CStarAlgebra`, `PartialOrder` and `StarOrderedRing`. Mathlib's `CStarAlgebra` is unital; the compatible order is the positive-element order. Restricting the universes to `Type` weakens the claim, so its negation refutes the source statement. `Fin` indices correspond to the source indices by adding one. `List.ofFn` and `List.prod` keep the product ordered, and `(n : ℂ)⁻¹ • 1` is the source's $1/n$ term.

## Gap

[Issue #14974](https://github.com/the-omega-institute/trureturing/issues/14974) preregisters the Tier 1 named conjecture, its literal definitions, the witness, the literature screen and the refutation criterion. Its convention for `NormedSpace.exp` uses no explicit scalar argument. No earlier settlement was found in the literature scope recorded there; exhaustive publication priority is unverified.

## Route

Put $I=1_{M_2(\mathbb C)}$ and
$$
 A_1=3\pi I,\qquad A_2=\pi\operatorname{diag}(5,1),\qquad
 A_3=\frac\pi4\begin{pmatrix}19&\sqrt{15}\\\sqrt{15}&5\end{pmatrix}.
$$
Set $x_{j,l}=A_j$ for both positions. The squared differences are $4\pi^2I,4\pi^2I,\pi^2I$. Pairing even and odd terms in the exponential series gives $\cos X=\cos(c)I$ when $X^2=c^2I$. Thus the three cosines are $I,I,-I$, and each cosine factor is $I$ or $0$.

Consequently
$$
 N=\frac13\begin{pmatrix}2&2&2\\2&2&-1\\2&-1&2\end{pmatrix}\otimes I,
 \qquad v=(-2,1,1)I,\qquad \langle Nv,v\rangle=-2I.
$$
The matrix order identifies nonnegative matrices with positive-semidefinite matrices. A diagonal entry of a positive-semidefinite matrix is nonnegative, while the displayed value has diagonal entry $-2$.

## Falsifier

An incorrect source convention, an earlier published settlement, or a failed exact witness calculation invalidates the stated route. The Lean theorem checks the literal `claim` and proves `result : ¬ claim`; it does not infer positivity from numerical approximations.

## Evidence

The settling declaration is `D5/S3/Quantum/Algebra/CStarNovak.result`. Its only public companions are `ncos`, `novakEntry`, `IsPositiveMatrix` and `claim`. The private theorem helpers are consumed by the settling proof; their `proof_shape` and that of `result` are `bind-only`. The module's admission basis is `open-problem-resolution (#14974; Refuted)`, with `escape_witness: none` and certified-instance utility under `basis=refutes`.

The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

### What the settlement shows

- **Witness: proved, kernel-checked.** `a_selfAdjoint` establishes all three coordinates' self-adjointness; `square_diff` proves the squared differences $4\pi^2I,4\pi^2I,\pi^2I`; `cosine_diff` gives $I,I,-I`; `witness_entry` gives the coefficient matrix above; `witness_quadratic` gives $-2I$; and `negative_one_not_nonneg`, used by `result`, proves the violation of positivity. These helper declarations are private in the settling module.
- **Extension: proved by the following paper argument, not formalized.** Repeating the same coordinate in every position preserves factors $I$ or $0$ for every $d\ge2$. For every $n\ge3$, append copies of $A_1$ and extend $v$ by zeros. The leading three-by-three block differs from the $n=3$ block by $(1/3-1/n)J\otimes I$, where $J$ is the all-ones matrix. Since $-2+1+1=0$, this correction contributes zero to the quadratic form. Its value stays $-2I$.
- **Euclidean mechanism: proved by the following paper argument, not formalized.** For $u\in\mathbb R^3$, the self-adjoint matrix
  $$H(u)=\begin{pmatrix}u_3&u_1-iu_2\\u_1+iu_2&-u_3\end{pmatrix}$$
  satisfies $H(u)^2=|u|^2I$. Linearity then realizes Euclidean squared distances as scalar matrix squares. A universal positive Novak matrix would imply positive definiteness of the radial scalar kernel $\varphi_d(r)=((1+\cos r)/2)^d$, because adding $J/n$ preserves positivity. [Golinskii–Malamud–Oridoroga, arXiv:1403.2234v1, Theorem 1.2, formula (1.5)](https://arxiv.org/abs/1403.2234v1) states Schoenberg's representation on $\mathbb R^3$: $\varphi_d(r)=\int_0^\infty\operatorname{sinc}(rt)\,d\nu(t)$ for a probability measure $\nu$. For $t>0$, $\operatorname{sinc}(2\pi t)<1$; hence $\varphi_d(2\pi)=1$ forces $\nu=\delta_0$, contradicting $\varphi_d(\pi)=0$. This literature theorem explains the mechanism; it is not a dependency of the delivered Lean proof.
- **Triangle: proved by the following paper argument, not formalized.** The sides $2\pi,2\pi,\pi$ form a Euclidean triangle. They cannot be the distances of three collinear points: the largest distance of three collinear points is the sum of the other two, which these lengths do not satisfy. On $\mathbb R$, the source's commutative theorem applies.
- **What survives: proved in the source, not formalized here.** Theorem 4.4 proves the commutative unital C*-algebra case independently of Conjecture 4.3. This includes finite-dimensional abelian unital C*-algebras, so that subcase is already settled. The source's other proved results are not invalidated; its final question about improving the commutative Schur-product lower bound remains open in this delivery.
- **Readings: computed in the exact tested scope $n=3$ and $d=2,3,5$.** The [experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/5bfb4667c873a54ececb997ab51822e20f173426/docs/reports/krishna-2021-cstar-novak-conjecture/) contains `check.py`; command `python3 check.py`, exit 0, SHA-256 `fbd6153f6b485f05f2c1d7809a623bc49ebabf8b22a6fcfe99388595074d28e4`. It computes all nine squared differences and exponential cosines, and for each tested $d$ returns the scalar block $\frac13[[2,2,2],[2,2,-1],[2,-1,2]]$ and quadratic form $-2I$. Uniform extension to all $n\ge3,d\ge2$ is the paper argument above, not the scope of this computation.
- **Within-position commutation: open.** This delivery does not settle the case in which $x_{j,l}$ pairwise commute for each fixed $l$, with no joint commutation assumed between distinct positions. The witness fails that added hypothesis: $[A_2,A_3]=\pi^2\sqrt{15}\begin{pmatrix}0&1\\-1&0\end{pmatrix}\ne0$.
- **Two-dimensional scalar kernel: proved by the following paper argument, not formalized.** The points $(0,0),(2\pi,0),(7\pi/4,\sqrt{15}\pi/4)$ have squared distances $4\pi^2,4\pi^2,\pi^2$. Their scalar kernel matrix is $[[1,1,1],[1,1,0],[1,0,1]]$ for every positive integer $d$ and has quadratic value $-2$ at $(-2,1,1)$. Thus radial positive definiteness already fails on $\mathbb R^2$. The planar embedding uses noncommuting Pauli matrices; it does not produce commuting matrix pairs. The commuting-coordinate question remains open as stated above.

## ASSUMED-UNVERIFIED

Publication priority is bounded by the preregistration's literature screen: general-web and citation coverage were incomplete. The mathematical refutation does not assert exhaustive literature absence. The within-position commuting-coordinate extension and the source's final Schur-product-bound question are not settled here.
