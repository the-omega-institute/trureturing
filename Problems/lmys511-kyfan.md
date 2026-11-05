---
slug: lmys511-kyfan
bibkey: lin2022kyfanli
doi: 10.13001/ela.2022.5943
url: https://arxiv.org/abs/2012.11162v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result
---

# Lin–Miao–Yu–Sheng Conjecture 5.11: second-norm uniqueness

## Problem

Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng, *On the Ky Fan k-norm of the
LI-matrix of graphs*, Electronic Journal of Linear Algebra 38 (2022), 680–696,
Conjecture 5.11 (page 694), states:

> Among all connected graphs with n and m edges n ≤ m ≤ 2n−3, the Gₘ,ₙ is the unique graph with maximal value of ‖LI(G)‖F₂ and ‖LI(G)‖F₃.

Here $n$ is the number of vertices, $m$ the number of unordered edges,
$L(G)=D(G)-A(G)$, $LI(G)=L(G)-(2m/n)I_n$, and the Ky Fan $k$-norm is the sum
of the $k$ largest singular values, with multiplicity. The assertion is read as a
separate maximum and equality characterization for each of $k=2$ and $k=3$.
The interpretation involving a unique simultaneous maximizer is outside the claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite simple undirected graphs of order $n$ | `SimpleGraph (Fin n)` | Every finite labelled graph of that order is represented. |
| Connected, with $m$ edges | `G.Connected`, `Nat.card G.edgeSet = m` | Mathlib connectivity and unordered edges. |
| $n\le m\le2n-3$ | The two range hypotheses in `claim` | `m + 3 ≤ 2 * n` avoids truncated subtraction; together the hypotheses force $n\ge3$. |
| $LI(G)=L(G)-(2m/n)I_n$ | `LI` | Literal source-specific shift of Mathlib's Laplacian. |
| $G_{m,n}$ in Figure 2.1 | `Gmn n m` | Vertex $0$ is universal; vertex $1$ meets $2,\ldots,m-n+2$. Argument order is $n,m$. |
| Separate assertions for $F_2$ and $F_3$ | `claim` quantifies over $k=2$ or $k=3$ | Both the upper bound and the equality iff isomorphism are retained. |
| Refutation | `result` | The public theorem proves the negation of that whole claim using its $k=2$ equality clause. |

Section 2 prints $2n-m+3$ pendant edges. That count conflicts with the stated
order, size and figure; the figure's construction has $2n-m-3$ pendant vertices.
The definition uses the figure and order/size convention fixed in #21801.
There is no additional mathematical hypothesis in the public result.

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result`
refutes the uniqueness assertion by an admissible six-vertex, seven-edge graph.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

Preregistration [#21801](https://github.com/the-omega-institute/trureturing/issues/21801)
records the verbatim source, complete quantifiers, Tier 1 classification, binding
conventions and bounded literature screen. No earlier settlement was identified
in the works read. Literature completeness is `ASSUMED-UNVERIFIED`; the citation
screen and downstream dependence screen are not exhaustive.

## Route

Let $H$ have all edges $\{0,i\}$ for $1\le i\le5$, together with
$\{1,2\}$ and $\{3,4\}$. The comparison graph $G_{7,6}$ has the same star,
with additional edges $\{1,2\}$ and $\{1,3\}$. Both are connected and have
seven edges. The degree lists are $(5,2,2,2,2,1)$ and $(5,3,2,2,1,1)$,
so an isomorphism is impossible.

The private proofs `h_norm` and `b_norm` verify exact rational inverse and
intertwining matrices. The consumed helper `kyFan_two_diagonalized` applies
Mathlib's characteristic-polynomial, ordered-eigenvalue and singular-value
identities to those certificates. It uses the existing
`D5.S3.Combinatorics.Graph.KyFanGap.kyFan` definition rather than defining
another norm. The two leading singular values are $11/3$ and $7/3$, giving
second norm $6$ for both graphs. Specializing the equality characterization of
`claim` at $n=6,m=7,k=2$ yields the contradiction.

Every theorem is classified `bind-only` after expansion of same-module helpers;
no escape witness is asserted. Admission is `open-problem-resolution (#21801; Refuted)`.
Only definitions, the designated result and consumed private helpers are delivered.

## Falsifier

A failure of the graph cardinality, connectivity, degree obstruction, rational
inverse certificate, intertwining certificate or singular-value ordering would
invalidate this witness. Each is checked in the proof of `result` through the
private helpers. The refutation does not assert a third-norm tie or use a global
maximality theorem as a premise.

## Evidence

The kernel-checked public statement is `result : ¬ claim` in
`D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.lean`.
Private `h_edges`, `h_connected`, `h_not_iso`, `h_norm` and `b_norm` provide the
admissible graph, nonisomorphism and exact second-norm identities used there.
The comparison graph is connected because its vertex $0$ is universal; this is
also immediate from its adjacency relation and is a prose observation.

The exact finite computation is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5ac15f4345d6fc41f30913cce150a4b5f46cc64b/docs/reports/lmys-kyfan-c511)
at revision `5ac15f4345d6fc41f30913cce150a4b5f46cc64b`.
Command: `python3 docs/reports/lmys-kyfan-c511/check.py`, run from that revision
(or with that exact blob extracted to a scratch file); exit $0$, final line
`ALL_CHECKS_OK`. Script SHA-256:
`8506853201bc6073cd6ff13e7678ebeba3ab62286d067cbaef321bfc4b894507`.
It checks the graph definitions for all $28$ admissible pairs with $3\le n\le9$,
regular-graph identities for $3\le n\le10$, and the two counterexample families
for $6\le n\le18$. The latter checks include connectivity, degree multisets,
characteristic polynomials and exact second and third norms. These finite
computations do not establish an unbounded-order theorem or extremal classification.

## Triage

### What the settlement shows

1. **Proved (kernel-checked finite settlement).** At $n=6,m=7,k=2$, $H$ and
   `Gmn 6 7` are nonisomorphic and have equal second norm $6$; $H$ is connected
   and has seven edges. Evidence: private `h_edges`, `h_connected`, `h_not_iso`,
   `h_norm`, `b_norm`, consumed by `result`. The comparison graph's connectivity
   follows from its universal vertex, as explained in Evidence. Thus the
   separate-maxima claim is false. The same witness refutes the equality-only
   assertion of source Theorem 5.9, whose bicyclic edge count is $m=n+1$.
2. **Proved in prose (finite spectral mechanism from checked certificates).** The
   rational diagonalization certificates in `h_norm` and `b_norm`, read by
   `kyFan_two_diagonalized`, give largest singular values $11/3$ and $7/3$.
   The corresponding common centered eigenvalues are $11/3$ and $-7/3$.
   In spectral terms, replacing Laplacian eigenvalues $4,2$ by $3,3$ changes
   only smaller singular values at order six. Both sums remain $6$.
   Evidence: the complete inverse, intertwining and squared-value-ordering
   certificates inside those private proofs. The explanation is not an
   additional public spectrum theorem. For each certificate, $PR=I$ and
   $LI\,P=P\operatorname{diag}(d)$ imply that $P$ is invertible and
   $LI=P\operatorname{diag}(d)P^{-1}$. Thus the eigenvalues are precisely the
   entries of $d$. For $H$ these are $11/3,-7/3,-4/3,-4/3,2/3,2/3$; for the
   comparison graph they are $11/3,-7/3,5/3,-4/3,-4/3,-1/3$. Symmetry makes
   their absolute values the singular values. Every remaining modulus is at
   most $5/3<7/3$, so their two largest moduli have sum $6$. This derivation
   explains the checked norm identities without asserting a separate Lean
   spectrum theorem.
3. **Computed (exact finite experiment).** For every $6\le n\le18$, the
   checker in Evidence verifies both second norms equal $n$. The third norm is
   $n+2-2/n$ for `Gmn n (n+1)` and $n+1+2/n$ for the universal-star graph
   with the two disjoint extra edges. It exits $0$ with `ALL_CHECKS_OK` for the pinned
   script and SHA-256 above. The third norms differ by $1-4/n>0$ on that scope.
   No statement for all $n$ is inferred from this computation.
4. **Open (formal and extremal extensions).** No all-order Lean family theorem,
   replacement extremal classification, global upper bound, third-norm
   uniqueness theorem or result for other $m$ is delivered. The finite tie
   leaves the source's global bound and its third-norm assertion unresolved
   here. A maximum of several spectral branches can retain equality even
   when one branch has a strict estimate; this explains why strictness in
   the upper-eigenvalue branch alone cannot certify the claimed uniqueness.
5. **Open (literature and downstream completeness).** Exhaustive downstream
   dependence and exhaustive absence of an earlier settlement are unverified.
   No independent downstream theorem relying on this exact conjecture was
   identified in the screened work. The second-norm equality assertion of
   Theorem 5.9 is contradicted; this alone does not refute its upper bound or
   any theorem whose proof avoids that equality assertion.

## ASSUMED-UNVERIFIED

Literature completeness and exhaustive downstream dependence remain unverified.
The screen in #21801 covers the arXiv versions, journal source and named nearby
works; OpenAlex and Semantic Scholar citation enumeration returned HTTP $429$.
Some later graph papers were screened only at title/abstract level, and two
related full texts were inaccessible. The family computation is finite and
supplies no uniform Lean theorem or replacement classification.
