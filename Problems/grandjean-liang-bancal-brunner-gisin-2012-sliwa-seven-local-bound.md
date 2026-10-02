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
(B1). It states that its local bound is numerically (6(K-1)), attained by
the all-zero deterministic strategy, and conjectures that both the local
bound and the facet-defining property hold for every (K). The settled
statement is the local-bound clause:

[
orall Kge 2,quad
min{J_K(a,b,c,A,B,C):a,b,c,A,B,C:mathbb Z/Kmathbb Z}=6(K-1),
]

where (J_K) is the twelve-term deterministic expression, with each
bracket interpreted as the least nonnegative residue.

## Motivation

The frozen declaration
`D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result`
proves the local-bound clause for every natural (Kge2). The source's fact
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

Write (s=[a+b+c]_K), (t=[A+B+C]_K), and
(u_i=[-A+b+c]_K,[-B+a+c]_K,[-C+a+b]_K). The remaining mixed residues
are (v_i=[u_i+t-s]_K). Their integer sum has the form
(u_1+u_2+u_3=2s-t+Kq). Splitting on (tge s) or (s>t), and on which
residues wrap, gives the lower bounds for the mixed sum, including the
strengthened (s=0<t) case. The exact residue identity then yields
(J_Kge6(K-1)). The all-zero assignment gives equality.

## Falsifier

A counterexample would be a natural (Kge2) and six values in
(mathbb Z/Kmathbb Z) whose twelve-term value is below (6(K-1)).
Changing the residue convention, the six mixed permutation terms, or the
quantifier (Kge2) would define a different question.

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
  (6(K-1)) for every (Kge2), uniformly in (K).
- **Mechanism:** the residue decomposition controls all six mixed terms and
  handles the only negative correction in the exact identity; the all-zero
  strategy is sharp.
- **Scope that remains open:** whether (B1) is facet-defining for every (K),
  and any quantum or visibility optimization, are not settled here.
- **Source consequences:** the paper's local-theory comparison for (B1) may
  use (6(K-1)) for all (K); claims depending on the separate facet
  conjecture remain conditional.

## ASSUMED-UNVERIFIED

The literature search was bounded to the sources and queries recorded in
issue #12317. Several citing papers were not read in full, and no
exhaustive literature or priority claim is made. The Lean kernel verifies
the encoded residue statement and its axiom closure; the correspondence to
the paper's full probabilistic notation uses the source's deterministic
strategy reduction.
