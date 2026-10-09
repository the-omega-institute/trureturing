---
slug: mayumi-kimura-ohno-chruscinski-2024-weighted-bottcher-wenzel-ii
bibkey: mayumi2024weightedbw
doi: 10.1016/j.laa.2024.07.013
url: https://arxiv.org/abs/2403.04199v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result
---

# Weighted Böttcher–Wenzel inequality, case (ii)

## Problem

A. Mayumi, G. Kimura, H. Ohno and D. Chruściński, “Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics”, arXiv:2403.04199v2, Conjecture 1, equation (15), ask whether

$$\|[A,B]\|_\omega\leq\sqrt{\frac{\lambda_m+\lambda_M}{\lambda_m}}\,\|A\|_\omega\|B\|$$

holds for all $A,B\in M_n(\mathbb C)$ and every positive definite weight $\omega$. Here $[A,B]=AB-BA$, $\|A\|_\omega^2=\operatorname{tr}(A^*A\omega)$, $\|B\|^2=\operatorname{tr}(B^*B)$, and $\lambda_m,\lambda_M$ are the attained minimum and maximum eigenvalues of $\omega$. Issue #13715 preregisters this case as a tier-3 research line.

## Motivation

The frozen declaration `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result` proves the squared inequality in every positive dimension, for all complex matrices, with no normality, rank, commutation or trace-normalization restriction. The source applies this mixed weighted/unweighted bound to relaxation rates of quantum Markovian dynamics.

## Gap

The Semantic Scholar graph query

`https://api.semanticscholar.org/graph/v1/paper/ARXIV:2403.04199/citations?fields=title,externalIds,year,url&limit=1000`

returned six citing works with no next page, collected at 2026-10-08T05:32:31.119536+00:00:

| Work | Relevant scope |
| --- | --- |
| arXiv:2406.12280; DOI 10.1103/PhysRevA.110.062215 | State-dependent commutator norms and a doubly weighted bound; dimension two proved, general dimension conjectured. |
| Fang–Cheng; DOI 10.1016/j.laa.2025.03.015 | Weighted conjectures for pairs of rank-one matrices; scope from the indexed abstract. |
| arXiv:2504.20404; DOI 10.1038/s41534-026-01374-0 | A doubly weighted inequality with a normal factor. |
| arXiv:2506.17365; DOI 10.1016/j.laa.2025.07.005 | A different three-rectangular-matrix generalization. |
| arXiv:2609.23520 | Nobori's generalized inequality, a different statement. |
| arXiv:2608.03897; DOI 10.1016/j.laa.2026.08.001 | The q-deformed commutator. |

The scope checks recorded in #13715 and the lane source survey do not identify a general settlement of equation (15) in these works. This is a bounded `not-found-in-searched-scope` conclusion. The citation graph does not establish exhaustive coverage, priority or the absence of an unindexed independent proof.

## Route

Write $f(A)=\operatorname{tr}(A^*A)$ and $g(A)=2f(A)-\|\operatorname{ad}_A\|^2$, with the commutator acting on the Frobenius Hilbert space. Numerical-range convexity for compressions gives a pure state maximizing Cartesian variance. Its block frame yields $g(A)\geq0$ and

$$\|A-cI\|_{\mathrm{op}}^2\leq f(A)+2|c|^2+2|c|\sqrt{g(A)}.$$

A contraction is an average of two unitaries, using the frozen SVD owner. Pencil estimates give, for every orthogonal projection $P$ of any rank,

$$f([A,B]P)\leq\bigl(f(A)+2f(AP)+2\sqrt{f(AP)g(A)}\bigr)f(B).$$

For $\omega=I+sP$, $s\geq0$, the weighted defect is bounded below by

$$\bigl(\sqrt{g(A)}-s\sqrt{f(AP)}\bigr)^2 f(B)\geq0.$$

Spectral convex decomposition and affinity in the weight transfer the bound to every positive definite $\omega$, with coefficient $1+\lambda_M/\lambda_m$. The equal-eigenvalue case is handled directly.

## Falsifier

A counterexample would require the squared weighted commutator trace to exceed the right-hand side, with the endpoints equal to the actual spectral extrema. Testing a restricted matrix class cannot prove the universal claim. Cases (i) and (iv), singular weights and an equality classification are outside the delivered theorem.

## Evidence

The canonical Lean sources are `NumericalRange`, `CartesianVariance`, `CommutatorGap` and `WeightedBotcherWenzel` under `D5/S3/Quantum/Matrix/`. `result : claim` closes case (ii). `SpectralExtrema` requires all eigenvalues to lie between the endpoints and both endpoints to be attained. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The live assembly uses `sphere_image_eq_ball_image`, `pure_of_density_linear_max`, `maximizing_block_frame`, `translation_gap`, `projection_channel_from_translation` and `projection_gap`. Every module has `admission_basis: escape-witness`. Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 3; settlement Proved for case (ii). The Scribe records `OpenProblemResolutionClaim(Proved)` on `result`. The module's admission basis is `escape-witness`.

### What the settlement shows

- **Proved:** numerical-range convexity for compressions and the pure Cartesian variance maximizer give the block translation estimate. The rank-k projection channel uses two-unitary averages and handles arbitrary rank without a Halmos dilation. Evidence: `pure_variance_maximizer`, `translation_gap`, `projection_gap`, and `result`.
- **Proved by the source's matrix-unit argument:** for $n\geq2$, take orthonormal eigenvectors $v_m,v_M$ at the attained eigenvalues $\lambda_m,\lambda_M$ (choose two orthogonal vectors if the weight is scalar). Set $A=|v_M\rangle\langle v_m|$ and $B=A^*$. Then $\|A\|_\omega^2=\lambda_m$, $\|B\|^2=1$, and $\|[A,B]\|_\omega^2=\lambda_m+\lambda_M$. Thus equation (15)'s coefficient is attained. This is the source's page-7 equality example and a paper argument, not a delivered Lean equality theorem. For $n=1$, every commutator is zero.
- **Computed:** the exact instance $A=E_{21}$, $B=E_{12}$, $\omega=\operatorname{diag}(2,5)$ attains the squared coefficient $1+5/2$: both sides equal $7$. The command below checks exactly $n=2$, $\lambda_m=2$, $\lambda_M=5$; it does not test a uniform extension. A uniform kernel-checked equality classification is outside this delivery.
- **Open:** case (i), with squared coefficient $(\lambda_m+\lambda_{sm})/(\lambda_m\lambda_{sm})$, and case (iv), which the source derives from (i), remain unsettled here in general dimension. The normal-factor and rank-one-pair results have their stated restricted scopes. Extension of this method to those cases is open.
- **Proved, using the source's application:** for an $n$-level GKLS generator with a faithful stationary state $\omega$, normalized jump operators, the rate formula in equation (27), and the source identity $\sum_k\gamma_k=n^{-1}\sum_{\beta=1}^{n^2-1}\Gamma_\beta$, case (ii) supplies the conjectural premise of equation (28). Under those source assumptions the bound

  $$\Gamma_\alpha\leq\frac{1}{2n}\left(1+\frac{\lambda_M}{\lambda_m}\right)\sum_{\beta=1}^{n^2-1}\Gamma_\beta$$

  is unconditional on WBW-ii. Apply the inequality with each eigenoperator as the weighted factor and each normalized jump operator as the unweighted factor, use commutator antisymmetry, and sum with nonnegative jump rates. The GKLS identities and rate application are **open** as Lean formalizations in this delivery.

The finite sharpness computation uses Python's exact rational arithmetic:

```sh
python3 - <<'PY'
from fractions import Fraction as F
A = [[F(0), F(0)], [F(1), F(0)]]
B = [[F(0), F(1)], [F(0), F(0)]]
weights = [F(2), F(5)]
def mul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def sq(X, w):
    return sum(w[j] * X[i][j] ** 2 for i in range(2) for j in range(2))
AB, BA = mul(A, B), mul(B, A)
C = [[AB[i][j] - BA[i][j] for j in range(2)] for i in range(2)]
lhs = sq(C, weights)
rhs = (1 + max(weights) / min(weights)) * sq(A, weights) * sq(B, [F(1), F(1)])
assert lhs == rhs == 7
print("n=2 lo=2 hi=5 weighted_commutator_sq=7 rhs=7")
PY
```

Script SHA-256: `32765635b2710190c04d22e7c79686268fb87f951af6480771806c106e4033f9`. Exit: 0. Output: `n=2 lo=2 hi=5 weighted_commutator_sq=7 rhs=7`.

## ASSUMED-UNVERIFIED

The full Fang–Cheng publisher text was not opened; its rank-one-pair scope is from the indexed abstract. Literature scopes beyond the citation query are the source survey recorded in #13715. The bounded search does not certify exhaustive novelty or priority. The Lean kernel checks the encoded mathematics and does not authenticate publications, citation graphs or the GKLS interpretation.
