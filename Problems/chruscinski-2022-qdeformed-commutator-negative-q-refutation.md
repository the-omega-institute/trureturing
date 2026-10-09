---
slug: chruscinski-2022-qdeformed-commutator-negative-q-refutation
bibkey: chruscinski2022qdeformed
doi: 10.48550/arXiv.2202.11520
url: https://arxiv.org/abs/2202.11520v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result
---

# A rank-one partner breaks the negative-q bound for a traceless matrix

## Problem

D. Chruściński, G. Kimura, H. Ohno and T. Singal, *Bounding the Frobenius norm of a q-deformed
commutator*, arXiv:2202.11520v2, state Conjecture 2: "For any $q\le 0$, if $A$ or $B$ is traceless,
the sharp bound is $\|[A,B]_q\|_F^2\le\max[g(n)(1-q)^2,1+q^2]\,\|A\|_F^2\|B\|_F^2$", with
$[A,B]_q=AB-qBA$ and $g(n)=(n^2-3n+3)/(n(n-1))$. Their Proposition 3 proves the case $n=2$ with
$\mathrm{tr}A=0$ for every real $q$. The verbatim statements are in
[the literature note](../Library/QuantumBounds/chruscinski2022qdeformed.md).

Issue [#14632](https://github.com/the-omega-institute/trureturing/issues/14632) reads the inequality
clause for every $n\ge2$, every $q\le0$ and all $A,B\in M_n(\mathbb C)$ with $\mathrm{tr}A=0$ or
$\mathrm{tr}B=0$.

## Motivation

The conjecture proposes the optimal Frobenius-norm constant for deformed commutators with $q\le0$,
which include the anticommutator ($q=-1$), under the trace condition of the companion Conjecture 1.
The value $g(n)(1-q)^2$ is attained by the source's pair $A=B=\operatorname{diag}(n-1,-1,\dots,-1)$.

## Gap

Issue #14632 records the literature check before any Lean: the citing works arXiv:2208.10005,
arXiv:2403.04199, arXiv:2402.01085 and arXiv:2608.03897 do not treat Conjecture 2 or a trace-constrained
bound for $q\le0$; Crossref, DataCite and the formal-conjectures repository show no settlement;
`not-found-in-searched-scope`.

## Route

At $n=3$ and $q=-1$, take $A=\operatorname{diag}(2,-1,-1)$ (trace $0$) and $B=E_{11}$. Then
$AB=BA=\operatorname{diag}(2,0,0)$, $\|[A,B]_{-1}\|_F^2=\|\operatorname{diag}(4,0,0)\|_F^2=16$,
$\|A\|_F^2=6$, $\|B\|_F^2=1$ and $\max[g(3)\cdot4,2]=2$, so the bound would give $16\le12$.

## Falsifier

The refutation would fail under a reading that requires both matrices to be traceless. The source
writes "$A$ or $B$" and proves the case $n=2$ under the single condition $\mathrm{tr}A=0$.

## Evidence

The canonical source is `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.lean`, with
public `g`, `claim` and `result : ¬ claim`. The squared Frobenius norm is the existing `mass` of
`D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation`, the only import. The
axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no
`sorry`, `native_decide`, or new axiom.
The module statement is `sha256:c4768e9ee56732b9fb335ec0fb91f42875bee81e6ae90d3057cc7462ae850dbd`,
the `result` statement `sha256:b90da19082989d186deda8bfef7665cefa24100982255e14bc9ebf26b8d192ee`, the
`claim` statement `sha256:99b3f8e7af1534e05327c07cc3146099a5c8d5fbb58e8797479f0a486dff6ba2` and the `g`
statement `sha256:277f2af201e07ae642d464db8465b0e9eb1eebab7cdfef5e945e0fcc3a03aa0a`. The Freeze event is
`sha256:b8101b6f547af29e2c37d9770e9b6d191f33ce473a542da74d00c0bc5f6bae73`; its project-level prerequisite is
the Moreau–Yosida module (`sha256:8acf232e43275fdfb443d70e0636ddf93b58a9a9635be8c8810b087f0de9d860`).

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #14632 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** Conjecture 2 fails at $n=3$, $q=-1$ for a traceless $A$ and a rank-one,
non-traceless $B$ commuting with it.

**Argued, not formalized.**

- *Every $n\ge3$.* For $A=\operatorname{diag}(n-1,-1,\dots,-1)$ and $B=E_{11}$,
  $\|[A,B]_q\|_F^2/(\|A\|_F^2\|B\|_F^2)=(1-q)^2(n-1)/n$. Since $(n-1)/n-g(n)=(n-2)/(n(n-1))>0$, this
  exceeds $g(n)(1-q)^2$ for every $n\ge3$ and $q<1$; at $q=-1$ it is $4(n-1)/n>2$, so the conjecture
  fails at $q=-1$ in every dimension $n\ge3$ (exact rational check in #14632).
- *Mechanism.* The source's extremal family has both traces zero. A partner with nonzero trace
  concentrated on the large eigenvalue of $A$ raises the ratio, and the single trace condition does
  not prevent it.
- *What survives (bounded numerics, not proof).* At $n=3$, $q=-1$, numerical maximization over random
  complex pairs found ratios approaching $2$, the conjectured coefficient, when both matrices are
  traceless, and approaching $8/3$ when only $A$ is traceless; the witness above attains $8/3$. These
  readings certify neither a supremum nor an upper bound.

**Open.** Whether the conjectured bound holds when both $A$ and $B$ are traceless, and the optimal
constant under a single trace condition for $n\ge3$.

**Effect on the paper.** Conjecture 2 as printed is false for $n\ge3$; the case $n=2$ remains
proved by Proposition 3.

## ASSUMED-UNVERIFIED

Fang–Cheng, *On some conjectures concerning the Böttcher–Wenzel inequality for weighted Frobenius
norms*, Linear Algebra Appl. (2025), DOI 10.1016/j.laa.2025.03.015, cites the source; its abstract and
text could not be read, and by its title it concerns the weighted-norm conjectures of
arXiv:2403.04199. That it does not settle Conjecture 2 is not verified firsthand. The journal version
of the source was not compared with arXiv v2. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent refutation.
