---
slug: grandjean-liang-bancal-brunner-gisin-2012-sliwa-seven-local-bound
bibkey: grandjean2012threesystems
doi: 10.1103/PhysRevA.85.052113
url: https://arxiv.org/abs/1204.3829v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result
---

# The local-bound clause of the Grandjean et al. conjecture on (B1)

## Problem

B. Grandjean, Y.-C. Liang, J.-D. Bancal, N. Brunner and N. Gisin,
“Bell inequalities for three systems and arbitrarily many measurement
outcomes”, *Physical Review A* 85, 052113 (2012), arXiv:1204.3829v2,
Appendix B, pp. 5–6, gives the arbitrary-output Sliwa seventh inequality
(B1). It states that its local bound is numerically $6(K-1)$, attained by
the all-zero deterministic strategy, and conjectures that both the local
bound and the facet-defining property hold for every $K$. The settled
statement is the local-bound clause:

$$
\forall K\ge 2,\quad
\min\{J_K(a,b,c,A,B,C):a,b,c,A,B,C\in\mathbb Z/K\mathbb Z\}=6(K-1).
$$

where $J_K$ is the twelve-term deterministic expression, with each
bracket interpreted as the least nonnegative residue.

## Motivation

The frozen declaration
`D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result`
proves the local-bound clause for every natural $K\ge 2$. The source's fact
that deterministic strategies suffice reduces the local-theory minimum to
this finite residue expression. The facet-defining clause is a separate
question and remains outside this settlement.

## Gap

Preregistration issue [#12317](https://github.com/the-omega-institute/trureturing/issues/12317)
classified this as a Tier 1 published conjecture and recorded the source
quotation and quantified target before Lean work. The paper's arXiv v2 is
the latest version. Bounded searches of the paper, its INSPIRE citing list,
selected citing arXiv papers, MathDB, and the repository found no
settlement in the searched scope. The unread citing literature and the
completeness of those searches remain `ASSUMED-UNVERIFIED`; no worldwide
priority claim is made.

## Route

Write $s=[a+b+c]_K$, $t=[A+B+C]_K$, and
$(u_1,u_2,u_3)=([-A+b+c]_K,[-B+a+c]_K,[-C+a+b]_K)$. The remaining mixed residues
are $v_i=[u_i+t-s]_K$. Their integer sum has the form
$u_1+u_2+u_3=2s-t+Kq$. Splitting on $t\ge s$ or $s>t$, and on which
residues wrap, gives the lower bounds for the mixed sum, including the
strengthened $s=0<t$ case. The exact residue identity then yields
$J_K\ge 6(K-1)$. The all-zero assignment gives equality.

## Falsifier

A counterexample would be a natural $K\ge 2$ and six values in
$\mathbb Z/K\mathbb Z$ whose twelve-term value is below $6(K-1)$.
Changing the residue convention, the six mixed permutation terms, or the
quantifier $K\ge 2$ would define a different question.

## Evidence

The complete kernel-checked proof is the public declaration `result` in
`D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.lean`.
The public surface contains the expression definition `J`, the claim
definition `claim`, and the settling theorem `result`; no helper theorem
is exported. The frozen statement identity is
`sha256:9f25c437c0f4db64a7b4695d203db1692f60a2fbb9ddaf714a67cd5a0af3dded`.
The Freeze event is
`sha256:b15faf9038569a21ae48d8ff2f1e6d69a7a89c9f50cf070262fd7f5df7c4b3b7`.
The event has no project-level frozen prerequisites. The proof uses only
`propext`, `Classical.choice`, and `Quot.sound`; it introduces no
axiom, `sorry`, or `native_decide`.

## Triage

Tier 1 published conjecture; resolution `Proved` for the local-bound clause
of (B1), via
`D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result`.
The facet-defining property, quantum optimum, and visibility optimum are
outside the result. The theorem is `bind-only` after the private residue
helper is inlined; its admission basis is
`open-problem-resolution` (#12317; Proved). Escape registration is paused
under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the deterministic minimum of (B1) is exactly
  $6(K-1)$ for every $K\ge 2$, uniformly in $K$.
- **Mechanism:** the residue decomposition controls all six mixed terms and
  handles the only negative correction in the exact identity; the all-zero
  strategy is sharp.
- **Scope that remains open:** whether (B1) is facet-defining for every $K$,
  and any quantum or visibility optimization, are not settled here.
- **Source consequences:** the paper's local-theory comparison for (B1) may
  use $6(K-1)$ for all $K$; claims depending on the separate facet
  conjecture remain conditional.

### Computed attaining strategies for small K

Exact integer enumeration of all $K^6$ ordered deterministic strategies
$(a,b,c,A,B,C)\in\{0,\ldots,K-1\}^6$ for each $K=2,\ldots,7$ gives the
following **computed, not proved** readings. Each of the twelve terms of
$J_K$ is evaluated using the least nonnegative integer remainder; every
strategy is visited, without symmetry reduction.

| $K$ | Strategies enumerated (computed) | Minimum $J_K$ (computed) | Attaining strategies (computed) | Attaining $(S,T)$ classes (computed) |
| --- | --- | --- | --- | --- |
| 2 | 64 | 6 | 32 | 3 |
| 3 | 729 | 12 | 189 | 7 |
| 4 | 4096 | 18 | 704 | 11 |
| 5 | 15625 | 24 | 2050 | 17 |
| 6 | 46656 | 30 | 5076 | 23 |
| 7 | 117649 | 36 | 11172 | 31 |

Thus the computed minimum equals $6(K-1)$ throughout this computation
range. These finite readings are separate from the module's all-$K$
proof of the minimum.

To describe which enumerated strategies attain it, write
$S=[a+b+c]_K$, $T=[A+B+C]_K$,
$(u_1,u_2,u_3)=([-A+b+c]_K,[-B+a+c]_K,[-C+a+b]_K)$, and
$L=\sum_{i=1}^3\bigl(u_i+[u_i+T-S]_K\bigr)$. In the enumeration,
attainment agrees exactly with

$$
L=S+T+K\bigl(\mathbf{1}_{S=0}-\mathbf{1}_{T=0}\bigr).
$$

This is a **computed classification for $K=2,\ldots,7$**, checked against
the direct twelve-term evaluation for every strategy, not a new proved
classification theorem. In that range the attaining strategies occupy
three regimes: $S=T=0$ with $L=0$; $S=0<T$ with $L=T+K$; and $S,T>0$
with $L=S+T$. No enumerated attaining strategy has $T=0<S$.
For every enumerated $K$, computed representatives of the three regimes
are respectively $(0,0,0,0,0,0)$, $(0,0,0,0,0,1)$, and
$(0,0,1,0,1,0)$. At $K=2$, the computed $(S,T)$ class counts are
$(0,0):4$, $(0,1):16$, and $(1,1):12$. Attainment in the computed range
is therefore not confined to $S=T=0$ or to the all-zero assignment.

The **computed count pattern for $K=2,\ldots,7$** is

$$
N_K=K^2\left(\binom{K+3}{4}+3(K-1)\right).
$$

Fitting the normalized counts $N_K/K^2$ for $K=2,\ldots,6$ gives the
quartic $K^4/24+K^3/4+11K^2/24+13K/4-3$, equal to the parenthesized
expression. That fit predicts $11172$ attaining strategies at the held-out
$K=7$, matching its exact enumeration. The count formula is **open in
general**; the finite agreement is computed evidence, not a theorem.

## ASSUMED-UNVERIFIED

The literature search was bounded to the sources and queries recorded in
issue #12317. Several citing papers were not read in full, and no
exhaustive literature or priority claim is made. The Lean kernel verifies
the encoded residue statement and its axiom closure; the correspondence to
the paper's full probabilistic notation uses the source's deterministic
strategy reduction.
