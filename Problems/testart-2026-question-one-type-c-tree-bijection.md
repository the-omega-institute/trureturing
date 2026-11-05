---
slug: testart-2026-question-one-type-c-tree-bijection
bibkey: testart2026minimal
doi: null
url: https://arxiv.org/abs/2602.12130v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result
---

# Testart Question 1: the native tree side and a type-C permutation model

## Problem

Benjamin Testart, *On minimal pattern-containing inversion sequences*,
arXiv:2602.12130v2, Section 7, Question 1, printed page 17, asks:

> Find bijections between the families $\mathrm{IP}_{n,k}$ or $\mathcal T_{n,k}$ of Section 6 and other families of combinatorial objects known to be counted by the poly-Bernoulli numbers of type C.

The question offers an IP-side or a T-side answer. The target here is the
entire T-side family, rather than the source's already published IP/T
correspondence. Section 6 defines unordered rooted increasing trees.
For every pair of integers $a,b\ge1$, write $N=a+b-1$. The source $T(a,b)$
consists of trees on distinct labels $0,\ldots,N$, rooted at zero, whose
internal labels are exactly $0,\ldots,a-1$ and whose leaves are exactly
$a,\ldots,N$. Every parent label is smaller than its child label.
The target $P(a,b)$ consists of permutations of $[N]$ whose strict
excedance-position set is exactly $[b-1]$, allowing fixed points.
Here $[0]=\varnothing$.

The fixed forward map deletes zero, reads each component root-first by DFS
with decreasing child-root labels, and makes each word a directed cycle,
sending each letter to the next and the last to the first. If the resulting
permutation is $\sigma$, the output is $F(t)=D_N(\sigma)$, where

$$
D_N(\sigma)(i)=N+1-\sigma(N-i)\quad(1\le i<N),\qquad
D_N(\sigma)(N)=N+1-\sigma(N).
$$

The fixed reverse map applies $D_N$, starts each directed cycle at its
minimum without reversing direction, attaches every later letter to the
rightmost preceding smaller letter, and attaches each cycle minimum to a
restored zero root. Forgetting traversal order gives $H$.
The target is both landings and both identities
$H(F(t))=t$ and $F(H(\pi))=\pi$, for every source tree and target
permutation and every positive $a,b$. There is no bound on $N$, no plane or
binary restriction, and no omission of $a=1$, $b=1$, $N=1$ or singleton cycles.
The unchanged fixed-map statement is specified in [#22578](https://github.com/the-omega-institute/trureturing/issues/22578).

## Motivation

`D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result` supplies the
whole-family operational specifications, landings and inverse identities.
The source uses the existing parent-only native increasing-tree carrier;
positive label $i+1$ is represented by `i : Fin N`. Its unrestricted
parent-function equivalence is
`D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.treeEquivCode`.

Bényi and Hajnal, *Combinatorial properties of poly-Bernoulli relatives*,
arXiv:1602.08684v1, Section 3.2, Theorem 12(ii), identify $P(a,b)$ as a
family counted by $C_{a,b-1}$, with their parameters $n=a$, $k=b-1$.
This is the singly starred strict-excedance family. The doubly starred
fixed-point-free family is different. The published count is attribution,
not an additional Lean counting theorem or a new axiom.

## Gap

An unrestricted tree/cycle correspondence or an equality of cardinalities
does not identify the individual internal labels with the prescribed
strict-excedance positions. It also does not certify the fixed decreasing-child
DFS and rightmost-smaller reconstruction conventions. The six conjuncts of
`TestartTraversal.result` retain these operational and native-incidence
requirements as well as the two restricted inverse laws.

The bounded literature reading in #22578 covers the versioned source,
its thesis repetition, the relevant Abreu–Nigro, Stanley,
Ehrenborg–Steingrímsson and Bényi–Hajnal passages, Knuth's *Parades and
Poly-Bernoulli Bijections* revised 25 August 2024, and Stappers's follow-up.
No complete published individual-label/strict-excedance contract was
established in that scope. This is not a worldwide priority or
non-settlement certificate. The source question is Tier 1: an explicit
2026 end-of-paper question.

## Route

Maximum-label insertion places the new label immediately after its parent
in the corresponding directed cycle, or creates a singleton when the parent
is zero. Induction identifies the insertion words with root-first DFS in
decreasing child-root order. The component words partition all positive
labels and certify the actual next/last-to-first permutation values.

The same induction identifies the reconstructed native parent at every
positive label with its rightmost preceding smaller letter. Every cycle
minimum receives zero. This gives the literal reconstruction and its equality
to inverse insertion. The individual-label statistic and the involution $D_N$
then give the required strict-excedance prefix and both restricted landings.

The result's six conjuncts are, in order: the forward operational certificate
for every native tree; the reverse operational certificate for every
permutation; the forward landing; the reverse landing; $H\circ F$ on
$T(a,b)$; and $F\circ H$ on $P(a,b)$. The first two certificates hold for
all native trees and all permutations of the indicated size, beyond the
restricted source and target classes.

## Falsifier

A falsifier for the fixed-map event would be a positive parameter pair and
a native tree or target permutation violating a specified traversal,
directed cycle, parent attachment, landing or inverse identity. The theorem
excludes all such cases in its stated domains. Finite agreement alone would
not exclude them. Failure of these particular maps would not by itself
refute the original existence question.

## Evidence

The mathematical sources are `TestartTreeCode.lean` and
`TestartTraversal.lean` under `D5/S3/Combinatorics/PriorityLattice/`, with
their matching Blueprint Scribe documents. `TestartTraversal.result` is the
single resolving theorem. Its axiom closure is contained in
`Classical.choice`, `Quot.sound` and `propext`; no `sorry` or new axiom is used.
The substantive constructions are unbounded structural proofs with
`utility: none`, not numerical certification. The admission basis for the
external endpoint is `open-problem-resolution`; supporting consumed
constructions also contain substantive escape content.

The mirrored Reg sources retain validated registrations for `result`,
`insert_apply` and `native_parent_code`. The faithful `dual_formula`
registration remains `declared_unresolved`, with a null certificate and
`IE-C050 ClosedTruthReadout / forbidden_dependency /
source.unsafe_or_external / Nat.decLt`, documented in
[#22609](https://github.com/the-omega-institute/trureturing/issues/22609).
This is an unfinished audit under the explicit linked-issue exception;
it is not a validated certificate or a mathematical refutation.

## Triage

### What the settlement shows

- **Proved:** `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result`
  establishes the entire positive-parameter fixed-map T-side answer, including
  the literal operational certificates and both inverse identities. The
  decisive mechanism is maximum insertion together with its individual-label
  statistic and exact reconstruction, rather than cardinality comparison.
- **Proved:** the first two conjuncts of that same theorem certify the
  operations for every native increasing tree and every permutation of the
  indicated size, before restriction to $T(a,b)$ and $P(a,b)$. Its last four
  conjuncts supply the source question's required restricted equivalence.
  The boundary pairs $a=1$ and $b=1$ and the singleton case are included.
- **Literature-attested:** Bényi–Hajnal Theorem 12(ii), with $n=a$ and
  $k=b-1$, supplies the type-C count interpretation. A separate Lean proof
  of that finite count is **unresolved in this delivery**. No numerical
  computation is used as evidence for the unbounded theorem.
- **Unresolved:** other type-C models, other fixed maps and Testart's other
  questions are outside the conclusion. The source's existing IP/T
  correspondence is preserved and receives no second resolution claim.
  This T-side answer fulfills the offered disjunction; it does not assert a
  new independent IP-side bijection or strengthen unrelated source results.
- **Unresolved:** worldwide priority, exhaustive duplicate absence and the
  unfinished `dual_formula` audit are not consequences of the theorem.
  The resolution binding records this formal mathematical answer; merge,
  required CI and delivery credit are separate obligations.

## ASSUMED-UNVERIFIED

Literature non-settlement is bounded to the identified sources and readings;
no global novelty claim follows. The type-C cardinality theorem is cited,
not newly formalized. The `dual_formula` audit has the unresolved disposition
and linked issue stated above. A resolution claim does not certify delivery
or add a completed resolution to an external KPI while integration and its
required checks remain pending.
