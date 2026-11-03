---
slug: oeis-a115770-carryless-seven-five-equivalence
bibkey: oeis2025a115770
doi: null
url: https://oeis.org/A115770
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence
---

# Seven and five versus binary carryless multiplication

## Problem

[OEIS A115770](https://oeis.org/A115770) defines the nonnegative integers
$k$ satisfying $7k=\operatorname{A048720}(11,k)$ and conjectures that they
are exactly the integers satisfying $5k=\operatorname{A048720}(13,k)$.
The exact assertion is

$$
\forall k\in\mathbb{N},\qquad
7k=C(11,k)\ \Longleftrightarrow\ 5k=C(13,k).
$$

The same $k$ occurs on both sides, $\mathbb{N}$ includes zero, and there is
no upper bound on $k$. Multiplication outside $C$ is ordinary multiplication.
The operation $C$ is binary coefficient convolution over $\mathrm{GF}(2)$,
as defined by [OEIS A048720](https://oeis.org/A048720):

$$
\operatorname{bit}(C(u,k),t)
=\left(\sum_{i=0}^{t}
\operatorname{bit}(u,i)\operatorname{bit}(k,t-i)\right)\bmod 2.
$$

Digits are indexed from zero at the least significant bit and have value
zero or one. The row-five/row-seven conjecture in A115872 expresses this
same question.

## Motivation

The source compares sets defined by different pairs of ordinary and
carryless multipliers. Their agreement on a finite interval does not
establish equality of the full sets. The target requires both implications
for every natural input.

## Gap

[The Library note](../Library/Digit/oeis2025a115770.md) retains A115770
revision 22: NAME gives the first equation, and COMMENTS conjectures the
second description, reporting a check through $2^{25}$. A048720 revision 62
identifies the operation as binary polynomial multiplication over
$\mathrm{GF}(2)$. These source readings specify the question and operation;
the finite check supplies no universal proof.

The source qualification belongs to
[issue 23261](https://github.com/the-omega-institute/trureturing/issues/23261).
The bounded literature scope includes those original entries, a lexical
search of repository sources including private declarations and pinned
mathlib, two AI-OEIS papers, 492 pinned metadata samples and their mapping,
and 38 published APN files. No exact answer was found within that scope.
The Library note records the inaccessible code-search boundary and excluded
material. This is no claim of exhaustive coverage or worldwide priority.

## Route

Reuse the binary product $P$ and its coefficient-convolution identification
from `CarrylessMultiplierEquivalence`. Its recurrences are
$P(u,0)=0$, $P(u,2n)=2P(u,n)$, and
$P(u,2n+1)=(2P(u,n))\mathbin{\mathrm{xor}}u$.
The convolution identification proves $P(u,k)=C(u,k)$ for every input.

A state is either rejection or a pair $(c,d)$ expressing
$mk+c=P(u,k)\mathbin{\mathrm{xor}}d$.
Reading a low binary digit $b\in\{0,1\}$ sets
$v=mb+c$ and $e=(bu)\mathbin{\mathrm{xor}}d$.
Different parities reject; equal parities give the next state
$(\lfloor v/2\rfloor,\lfloor e/2\rfloor)$.
The reused digit-step theorem proves equivalence between the original
state at input $2n+b$ and the next state at input $n$.

For $(u,m)=(11,7)$ and $(13,5)$, the explicit relation `related` has
15 paired states. It contains the pair of initial zero-carry, zero-mask
states. At every related pair, the two terminal conditions agree when the
remaining input is zero. Both binary digits preserve the relation, giving
30 checked transitions. Binary induction propagates terminal agreement
through inputs of every binary length. The initial pair and
$P(u,k)=C(u,k)$ give the exact equivalence above, including $k=0$.

## Falsifier

A natural number $k$ for which exactly one equation holds would refute the
question's assertion. A terminal mismatch, a digit transition leaving the
15-state relation, or a failure of the convolution identification would
invalidate this proof mechanism. The finite state checks support an
unbounded induction; they do not replace it with a bound on $k$.

## Evidence

- Exact theorem:
  `D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.result`, with type
  `∀ k : Nat, 7*k = carryless 11 k ↔ 5*k = carryless 13 k`.
- The new mathematical source retains the 15 paired states, terminal
  agreement, closure under both digits, and unbounded binary induction.
- The consumed product, coefficient identification, state interpretation,
  and digit-step theorem are reused from
  `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.lean`.
- The result's axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.
- The proof is repository-derived, with acknowledgement of the externally
  authored question and the known operation in `oeis2025a115770`.
- The retained typed Reg mirror compiles. Its audit remains
  `declared_unresolved`: `IE-C050 ClosedTruthReadout`,
  `reason=unclassified_form`, rule `source.residual_requires_open`, empty
  site and readout, null certificate, and no registration errors.
  The linked exception is
  [issue 23261, audit gap](https://github.com/the-omega-institute/trureturing/issues/23261#issuecomment-6477366786).
  This is no validated registration and supplies no substitute for kernel,
  axiom, or frozen-state checks.

## Triage

`theorem`. The substantive mechanism is a relation of 15 paired carry
states, agreement of terminal conditions, closure under both binary digits,
and induction over every natural input. It reuses the coefficient and
transition interface without reproving the known operation or the older
A115801 equivalence. At zero both equations are $0=0$.

The transition interface can support further comparisons once an appropriate
relation, terminal agreement, and digit closure are proved. This result
asserts no uniform classification or completeness theorem for multiplier
pairs. A general finite-carry-relation characterization remains an
unresolved internal candidate. Neither that candidate, the A115872 alias,
nor any neighboring question is an additional resolution here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and worldwide publication priority are
unverified. The bounded search does not exclude unindexed, private, or
semantically equivalent answers. The Reg readout classification remains
unresolved under the linked issue. No uniform classification, converse
completeness claim about the method, or neighboring equivalence is asserted.
