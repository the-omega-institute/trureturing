---
slug: marquez-gonzalez-2026-positive-filter-transpose-refutation
bibkey: marquezgonzalez2026feasibility
doi: 10.48550/arXiv.2609.18803
url: https://arxiv.org/abs/2609.18803v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.result
---

# A qutrit obstruction to positive/CP factorization of the channel transpose

## Problem

Samuel A. Márquez González, *Feasibility Ordering of Entanglement-Source
Placement for Qubit Channels*, arXiv:2609.18803v1, Section VI, Eq. (48), states
the weak question:

> The weaker question, which is sufficient for the source-placement theorem,
> asks only whether there exist a positive map $\mathcal{F}$ and a completely
> positive map $\mathcal{E}$ such that
> $\Upsilon^T=\mathcal{F}\circ\Upsilon\circ\mathcal{E}$.

and adds that "failure of the weak condition would identify the precise
obstruction to this proof strategy". The channel transpose is Eq. (16),
$\Lambda^T(X)=\sum_iK_i^TX\overline{K_i}$. The verbatim statements are in
[the literature note](../Library/QuantumStates/marquezgonzalez2026feasibility.md).

Issue [#13926](https://github.com/the-omega-institute/trureturing/issues/13926)
reads Eq. (48) as the assertion that every unital qutrit channel admits the
weak factorization: for every completely positive, trace-preserving, unital
$\Upsilon$ on $M_3$ and every finite Kraus family of $\Upsilon$, there exist a
positive $\mathcal F$ and a completely positive $\mathcal E$ on $M_3$ with
$\Upsilon^T=\mathcal F\circ\Upsilon\circ\mathcal E$. Neither filter must
preserve trace, be unital or be invertible.

## Motivation

The source reduces the higher-dimensional extension of its midpoint-feasibility
theorem to the weak factorization; its strong companion, Eq. (47), is refuted
at dimension three by
`D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result`. A failure
of the weak condition locates where the qubit proof strategy stops.

## Gap

Issue #13926 records the literature check before any Lean: arXiv lists one
version of the source; web, arXiv full-text and Zenodo searches found no
settlement of Eq. (48); the repository settled Eq. (47) only.
`not-found-in-searched-scope`.

## Route

Let $U=\tfrac17\begin{bmatrix}3&-2&6\\6&3&-2\\-2&6&3\end{bmatrix}$ with columns
$u_j$, and $\rho_j=(e_je_j^{\mathsf T}+u_ju_j^{\mathsf T})/2$. The channel
$\Upsilon(X)=\sum_jX_{jj}\rho_j$ is unital, with twelve real Kraus matrices, and
$\Upsilon^T(X)=\mathrm{diag}(\mathrm{tr}\rho_0X,\mathrm{tr}\rho_1X,\mathrm{tr}\rho_2X)$.
A factorization gives positive semidefinite trace representatives $B_k$ of
$X\mapsto\mathcal F(X)_{kk}$ and $\sigma_j$ of $X\mapsto\mathcal E(X)_{jj}$, and
$\rho_k=\sum_jC_{kj}\sigma_j$ with $C_{kj}=\mathrm{tr}(B_k\rho_j)\ge0$. A zero
$C_{kj}$ makes $B_k$ annihilate $e_j$ and $u_j$, so each row of $C$ has at most
one zero. With the kernel vectors $v_0=(0,1,3)$, $v_1=(3,0,1)$, $v_2=(1,3,0)$ of
the $\rho_j$, this zero pattern forces $(V^\dagger\rho_kV)_{01}=0$ for every $k$;
summing gives $v_0^\dagger v_1=0$, while $v_0^\dagger v_1=3$.

## Falsifier

The refutation would fail if Eq. (48) were read for a restricted class of
channels, or if the filters were required only to make the identity hold on
some inputs; the claim asks for equality of maps on every complex matrix and
quantifies over every unital qutrit channel and every Kraus family.

## Evidence

The canonical source is
`D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.lean`, with
public `claim` and `result : ¬ claim`. It reuses the frozen
`CPFilterTransposeRefutation.UnitalChannel`, the frozen `FiniteKrausChannel`
declarations `MatrixMap`, `of_kraus`, `IsPositive`, `IsCompletelyPositive`,
`kron` and `kron_def`, and nine Physlib declarations transplanted into the same
module (`MatrixMap.dual`, `Dual.trace_eq`, `IsPositive.dual`,
`IsCompletelyPositive.IsPositive` and their closure, from
`leanprover-community/physlib` at commit `6a09b2d1761a0d4430083045a247eb121d8da260`,
Apache-2.0; see [the source note](../Library/QuantumChannels/meiburg2025physlibdual.md)). The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no
`sorry`, `native_decide`, or new axiom.
The module statement is `sha256:f7ae08c12b1b146cee0fb3003fd0d555300b667065c5c08f000b773b29ecd5ac`,
the `result` statement `sha256:a2f3243b5fd98ff1aa62b392b9703df2e352073c03a0e6e8f865fb954ef2d8bc` and the
`claim` statement `sha256:945a8bfb85d6285e2ea39d8310558c156fd17a0ca0694b18730d89a75e1af251`. The Freeze
event is `sha256:22f70a5bc4d8752ab22ae9d3d504f9b1466e37cf233917488c33a849e56f4b0b`; its project-level
prerequisite is the frozen `CPFilterTransposeRefutation` module.

## Triage

Tier 1 question of a September 2026 paper, preregistered in issue #13926 before
any Lean. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | the coefficient relation and the zero-pattern obstruction | open-problem-resolution |

The two private theorems `positive_functional` (for every positive map and
index; it applies the transplanted `IsPositive.dual` and `Dual.trace_eq`) and
`zero_pattern_obstruction` (for every family of states, filters, coefficients
and kernel matrix) lie on the proof path of `result`, as do the transplanted
Physlib declarations. Utility is
`kind=certified-instance; basis=refutes` (the claim and its refutation). There
is no digestion atom.

### What the refutation shows

**Proved by `result`:** the universal claim fails: for the unital qutrit
measure-and-prepare channel $\Upsilon$ with its twelve-matrix Kraus family $K$, no
positive $\mathcal F$ and completely positive $\mathcal E$ satisfy
$\Upsilon_K^T=\mathcal F\circ\Upsilon\circ\mathcal E$, where $\Upsilon_K^T$ is the transpose
computed from $K$.

**Argued, not formalized here:** the channel transpose does not depend on the
Kraus family (trace duality; proved inside the proof of
`CPFilterTransposeRefutation.result`), so the same $\Upsilon$ fails Eq. (48) for every
Kraus family; `result` itself certifies the one family above.

**Proved inside the proof, for general data:** a positive map's diagonal
functionals have positive semidefinite trace representatives; and three states
that are nonnegative combinations of positive semidefinite matrices, sum to the
identity, have a nonsingular diagonal matrix and have kernel vectors $v_k$ forming
an invertible matrix $V$, with at most one zero coefficient per row, force
$v_0^\dagger v_1=0$.

**Argued, not formalized.**

- *Mechanism.* The channel reads only the diagonal of $\mathcal E(X)$, and the
  diagonal entries of $\mathcal E(X)$ are $\mathrm{tr}(\sigma_jX)$; the $k$-th diagonal
  entry of $\mathcal F$ applied to $\sum_j\mathrm{tr}(\sigma_jX)\rho_j$ is
  $\sum_jC_{kj}\mathrm{tr}(\sigma_jX)$ with $C_{kj}=\mathcal F(\rho_j)_{kk}\ge0$. Matching it with
  $\mathrm{tr}(\rho_kX)$ makes each $\rho_k$ a nonnegative combination of the $\sigma_j$.
  Such a decomposition always exists without further constraints ($\sigma_j=\rho_j$,
  $C=I$); the obstruction comes from the extra structure the factorization forces:
  each row of $C$ has at most one zero (a zero $C_{kj}$ makes the trace representative
  of the $k$-th diagonal functional of $\mathcal F$ annihilate $e_j$ and $u_j$), the
  matrix of diagonal entries of the $\rho_k$ is nonsingular, and the kernel vectors
  $v_k$ form an invertible matrix with $v_0^\dagger v_1\ne0$.
- *What survives.* The source's qubit results are unaffected (qubit unital
  channels satisfy the strong condition). The obstruction does not apply to
  measure-and-prepare channels whose state kernels are pairwise orthogonal, and
  it says nothing about channels outside the measure-and-prepare class.

**Open.** Whether the weak factorization holds for a natural restricted class of
unital qudit channels, and whether the counterexample lifts to every dimension
$d\ge3$, are not determined here.

**Effect on the paper.** The universal unital-qutrit premise proposed in Eq. (48)
is false. The witness channel is not strictly positive: it maps the diagonal
projector $e_je_j^{\mathsf T}$ to $\rho_j$, which has the nonzero kernel vector $v_j$.
The result therefore does not determine whether a factorization for a restricted
class such as strictly positive channels, followed by the source's regularization
argument, can establish midpoint feasibility in higher dimensions; that statement
is neither proved nor refuted here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
