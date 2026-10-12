---
bibkey: baekjonha2026maximalcoherence
authors: K. Baek; Y. Jo; H. Nha
year: 2026
title: "Maximal coherence of quantum measurement and the resource theory of sharpness"
doi: null
url: "https://arxiv.org/abs/2607.05847v1"
claim: 'Section III.C asks whether maximal distance-based measurement coherence is monotone under general CP unital maps for non-dichotomic POVMs.'
strata_touched:
  - D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2607.05847v1

## Definitions

Section II.A, p. 2:

> A quantum measurement on a $d$-dimensional Hilbert space with $n$ outcomes is described by a POVM, i.e., a tuple $\mathsf{A}=\{A_x\}_{x=1}^n$ of positive semidefinite operators satisfying the completeness relation $\sum_{x=1}^n A_x = I$.

> In the same spirit, a quantum measurement is called incoherent when all its elements are diagonal in the reference basis:

The defining expression is $A_x=\sum_{i=1}^d\lambda_{i|x}|i\rangle\langle i|$.
The set of these POVMs is $\mathcal I(d,n)$. Section II.B, pp. 3–4, defines trivial
POVMs as $\{p_x I\}_{x=1}^n$ with $\sum_xp_x=1$, denoted $\mathcal T(d,n)$.

Section II.A, p. 2, states:

> A natural family of coherence monotones for measurements arises from a distance $D$ between POVMs as

The coherence of Eq. (4), p. 2, and the maximal coherence of Section III.A, p. 4, are

$$C_D(\mathsf A)=\min_{\mathsf B\in\mathcal I(d,n)}D(\mathsf A,\mathsf B),
\qquad C_D^{\max}(\mathsf A)=\max_U C_D(U^\dagger\mathsf A U).$$

Section III.A, p. 4, states:

> Coherence is intrinsically basis dependent: rotating the reference basis by a unitary $U$ alters the off-diagonal structure of every POVM element. We define the maximal coherence of measurement of $\mathsf{A}$ as the basis-optimized value of any coherence monotone $C_D$,

The maximum is over all unitaries. Lean uses `sInf` and `sSup` of the corresponding
sets of real distances, with the spectral norm from `Matrix.Norms.L2Operator`.
The sharpness in Section II.B, p. 4, is
$S_D(\mathsf A)=\min_{\mathsf B\in\mathcal T(d,n)}D(\mathsf A,\mathsf B)$.

The element-additive distance of Eq. (32), p. 5, at $p=\infty$, is
$D_\infty(\mathsf A,\mathsf B)=\tfrac12\sum_x\|A_x-B_x\|_\infty$.
Section IV.A, p. 7, adopts it for the tetrahedral SIC qubit POVM. Its contractivity
under CP unital maps is the $p=\infty$ case of Theorem 5 of Tendick et al.,
[arXiv:2205.08546](https://arxiv.org/abs/2205.08546).

Fuzzifying operations, Eq. (12), p. 4, act as
$A_x\mapsto\alpha\mathcal E^\dagger(A_x)+(1-\alpha)q_xI_B$, with
$\alpha\in[0,1]$ and $q$ a probability distribution. The source says:

> By construction, fuzzifying operations preserve the number of outcomes $n$ but may change the Hilbert space dimension; in particular, dimension-preserving fuzzifying operations arise when $\mathcal{H}_{A}=\mathcal{H}_{B}$.

The CP unital dual has the finite-dimensional Kraus form
$\Phi(X)=\sum_jK_j^\dagger X K_j$, $\sum_jK_j^\dagger K_j=I$.

## Question

Section III.C, p. 7, states verbatim:

> For non-dichotomic POVMs, the equivalence with sharpness is generally unavailable, and monotonicity must be considered at the channel level: it holds under mixed-unitary channels (Theorem 5) and under unitarily covariant channels (Corollary 6), but whether $C_{D}^{\max}$ remains monotonic under general CP unital maps in this regime is left as an open problem.

Table I, p. 7, marks the non-dichotomic POVM row under "any fuzzifyng operations"
as "Open". The source's spelling is retained.

## Refutation and scope

The four tetrahedral SIC effects are
$A_i=(I+\vec n_i\cdot\vec\sigma)/4$, with
$\vec n_i=(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)$ divided by $\sqrt3$.
Adjoining an identity qubit is $J(X)=X\otimes I_2$, a CP unital dual of discarding
that qubit. Coordinates use `finProdFinEquiv`, $(i,j)\mapsto2i+j$, identifying
$\mathbb C^2\otimes\mathbb C^2$ with `Fin 4` in the order
$|00\rangle,|01\rangle,|10\rangle,|11\rangle$.

The module proves $C^{\max}_{D_\infty}(\mathsf M_{\rm SIC})\le\sqrt{2/3}/2$
and $C^{\max}_{D_\infty}(J(\mathsf M_{\rm SIC}))\ge1/2$.
Bell-diagonal effects have scalar normalized partial trace; applying the
Rayleigh bound with both signs gives the lower bound. The qubit upper bound
uses dephasing and the simultaneous tetrahedral off-diagonal square sum.
This refutes general monotonicity with four outcomes and a dimension-changing
operation. Dichotomic, mixed-unitary and covariant results retain their stated
hypotheses. Diamond distance and dimension-preserving failure remain open.

## Numerical reading

The independent numerical check is
[`check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/e79e3f95fef7b48c4474dbaf42991a0601a8dd05/docs/reports/baek-jo-nha-2026-maximal-coherence-ancilla-nonmonotone/check.py),
SHA256 `b0d07f99a84ffde3e5a0285f79184a2e0dfe8cf0dcf4ad2c8c151bc7d971d96c`.
Running `python3 check.py` exits 0 and reports `bad= 0`. The sampled dephasing
maximum is 0.408247, below the proved upper bound 0.408248. Sampling is computed
evidence; the exact upper and lower bounds are checked in Lean.
