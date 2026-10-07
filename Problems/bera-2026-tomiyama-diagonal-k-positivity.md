---
slug: bera-2026-tomiyama-diagonal-k-positivity
bibkey: bera2026tomiyama
doi: 10.48550/arXiv.2604.18600
url: https://arxiv.org/abs/2604.18600v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result
---

# The k-positive region of the diagonal-perturbed Tomiyama maps

## Problem

A. Bera, B. Bhattacharya and D. Chruściński, *Tomiyama-type maps with a diagonal perturbation*,
arXiv:2604.18600v1, study $\Phi_{\alpha,\beta}=(1-\alpha-\beta)\,\mathrm{id}+\alpha\,\tau_0+\beta\,\Delta$
on $M_d$, where $\tau_0(X)=\mathrm{tr}(X)\,I/d$ and $\Delta$ keeps the diagonal. Conjecture 2.4
states that the $k$-positive maps of the family form the quadrilateral
$\mathcal P_k=\mathrm{conv}\{\Psi_0,\Psi_1,\Psi_2,\mathcal T_k\}$ with parameter points $(0,0)$,
$(0,\tfrac d{d-1})$, $(\tfrac d{d-1},-\tfrac1{d-1})$ and $(\tfrac{kd}{kd-1},0)$, and §4 states that
the full proof is missing. The verbatim statements are in
[the literature note](../Library/QuantumChannels/bera2026tomiyama.md).

Issue [#13894](https://github.com/the-omega-institute/trureturing/issues/13894) reads the
conjecture for $2\le k\le d$, with $k$-positivity of $\Phi$ meaning that $\mathrm{id}_k\otimes\Phi$
preserves positive semidefiniteness, and the convex hull taken in the $(\alpha,\beta)$ plane.

## Motivation

The family interpolates between the identity, the completely depolarizing map and the
completely dephasing map; its $k$-positivity hierarchy decides which members detect
Schmidt number above $k$. The paper proves the region for $\beta\le0$, for $k\mid d$ and for
$k=d-1$. `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.result` proves it for every
$2\le k\le d$.

## Gap

Issue #13894 records the literature check before any Lean: arXiv lists only v1; web searches
for the title and for the authors with "k-positive", "Tomiyama" and "diagonal perturbation"
return the paper and a review page with no proof; Zenodo queries return no record; the
repository had no result on $k$-positivity of this family. `not-found-in-searched-scope`.

## Route

With $\gamma=1-\alpha-\beta$ and $Q(X)=\tfrac\alpha d\|X\|_F^2+\beta\sum_i|X_{ii}|^2+\gamma|\mathrm{tr}X|^2$:

1. **Quadratic form.** For $u,w\in\mathbb C^k\otimes\mathbb C^d$ with coefficient matrices
   $U,W\in M_{k\times d}$, $\langle u,(\mathrm{id}_k\otimes\Phi)(ww^\dagger)u\rangle=Q(U^\dagger W)$;
   positive semidefinite matrices are sums of $ww^\dagger$, and $\mathrm{id}_k\otimes\Phi$ preserves
   Hermiticity, so $k$-positivity is $Q\ge0$ on all $U^\dagger W$.
2. **Necessity.** $X=E_{12}$ gives $\alpha\ge0$; $X=E_{11}-E_{22}$ gives $\alpha/d+\beta\ge0$;
   $X=\mathrm{diag}(I_k,0)$ gives $(kd-1)\alpha+d(k-1)\beta\le kd$; the Fourier projection
   $X=AA^\dagger$, $A_{ia}=\omega^{ia}/\sqrt d$ for $a<k$, has $A^\dagger A=I_k$ and every diagonal
   entry $k/d$, so $Q(X)=\tfrac kd[kd-(kd-1)\alpha-k(d-1)\beta]$ gives the last edge. The four
   half-planes cut out the quadrilateral.
3. **Sufficiency.** The $k$-positive set is convex and contains the four vertices: $Q\ge0$ there
   by $|\mathrm{tr}X|^2\ge0$, Cauchy–Schwarz on the diagonal, $\|X\|_F^2\ge\sum_i|X_{ii}|^2$, and
   $|\mathrm{tr}(U^\dagger W)|^2\le k\|U^\dagger W\|_F^2$ (the columns of $U^\dagger W$ lie in the range of
   $U^\dagger$, of dimension at most $k$; an orthonormal basis of it and Cauchy–Schwarz).

## Falsifier

The settlement would fail under a reading of $k$-positivity other than positivity of
$\mathrm{id}_k\otimes\Phi$, or of the quadrilateral other than the convex hull of the four
parameter points; at $k=1$ the printed quadrilateral is not the positive region (see Triage).

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.lean`. Its
public declarations are `phi`, `KPositive`, `quadrilateral`, `claim` and `result`. It reuses the
frozen `MatrixMap`, `MatrixMap.kron`, `MatrixMap.kron_def` and `MatrixMap.IsPositive` of
`D5/S3/Quantum/Foundation/FiniteKrausChannel`, and imports that module,
`Mathlib.Algebra.Order.Chebyshev` and `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`.
The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is
no `sorry`, `native_decide`, or new axiom.
The module statement is `sha256:2d64856dbf886a0a80ca7274373e9429f181ebec809e1fc0bb4b97524d6dd42f`,
the `result` statement `sha256:fe5ede95269f31ae04537a8c3fe45a3a0ccef061bd063510482c2c467acaaba4` and the
`claim` statement `sha256:b6acf96758a4f866eece1bea28c09c3608ef70fb1e5f0b44f4a0bf67d2be1c16`. The Freeze
event is `sha256:a018aaca0ced28e8878188c86eaa05328e63123d5944a36ee8111b95c98050be`; its project-level
prerequisite is the frozen `FiniteKrausChannel` module it imports.

## Triage

Tier 1 conjecture of an April 2026 paper, preregistered in issue #13894 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private theorems (`kron_phi_apply`, `kron_phi_rankone_form`, `kpositive_q`,
`kron_phi_hermitian`, `kpositive_iff_q`, `fourierRows_gram`, `fourierRows_diagonal`,
`fourier_boundary`, `offdiagonal_boundary`, `coordinate_boundary`, `ranktwo_boundary`,
`trace_rank_bound`, `halfplanes_mem_quadrilateral`, `quadrilateral_kpositive`) are bind-only and
used on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」); each has free dimension,
matrix or parameter arguments. Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $2\le k\le d$, $\Phi_{\alpha,\beta}$ is $k$-positive iff
$(\alpha,\beta)\in\mathrm{conv}\{(0,0),(0,\tfrac d{d-1}),(\tfrac d{d-1},-\tfrac1{d-1}),(\tfrac{kd}{kd-1},0)\}$.

**Established inside the proof.** $k$-positivity of the family is equivalent to $Q\ge0$ on
$\{U^\dagger W:U,W\in M_{k\times d}\}$ (`kpositive_iff_q`), and
$|\mathrm{tr}(U^\dagger W)|^2\le k\|U^\dagger W\|_F^2$ (`trace_rank_bound`).

**Argued, not formalized.**

- *Mechanism.* The paper's tests are coordinate projections, whose diagonal has $k$ ones and
  $d-k$ zeros, or block vectors that need $k\mid d$. The edge from $\Psi_1$ to $\mathcal T_k$ is
  attained by a rank-$k$ projection whose diagonal is constant, $k/d$, and the Fourier projection
  is such a projection for every $k\le d$; this removes the divisibility condition. Among
  rank-$k$ orthogonal projections $X$ (trace $k$, $\|X\|_F^2=k$), $\sum_i|X_{ii}|^2$ ranges from
  $k^2/d$ (constant diagonal) to $k$ (coordinate projections). For $\beta\ge0$ the constant
  diagonal minimizes $Q$ and gives the edge $(kd-1)\alpha+k(d-1)\beta\le kd$; for $\beta\le0$
  the coordinate projections do and give $(kd-1)\alpha+d(k-1)\beta\le kd$. The two edges meet
  at $\mathcal T_k$, where $\beta=0$.
- *The case $k=1$.* The printed sentence "For $k=1$ it reduces to Corollary 2.3" does not hold:
  $\mathcal P=(\tfrac d{d-1},-\tfrac2{d-1})$ is positive (Proposition 2.1) but violates
  $\alpha/d+\beta\ge0$, the edge from $\Psi_0$ to $\Psi_2$, which needs the rank-two test
  $E_{11}-E_{22}$. At $k=1$ the lower edge is $2\alpha+d\beta\ge0$ instead, as in the paper's
  Proposition 2.1.
- *The case $k\ge d$.* Every $X\in M_d$ is some $U^\dagger W$ with $k\ge d$ rows, so $k$-positivity
  is complete positivity, and $\mathcal T_k$ lies in the CP triangle $\mathrm{conv}\{\Psi_0,\Psi_1,\Psi_2\}$
  for $k\ge d$; the quadrilateral of Conjecture 2.4 then equals the CP triangle.

**Open.** The analogous classification for the transposition family $\Lambda_{\mu,\nu}$ of the
same paper is proved there; the Schwarz-inequality and $k$-entanglement-breaking questions of §4
are not addressed here.

**Effect on the paper.** Conjecture 2.4 holds for every $2\le k\le d$, and Figure 2's
quadrilaterals are the $k$-positive regions in every dimension.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
