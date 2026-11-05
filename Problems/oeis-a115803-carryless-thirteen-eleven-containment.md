---
slug: oeis-a115803-carryless-thirteen-eleven-containment
bibkey: oeis2026a115803
doi: null
url: https://oeis.org/A115803
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment
---

# The A115805 to A115803 carryless containment question

## Problem

OEIS A115805 revision 14 defines the natural numbers k satisfying
13*k = A048720(29,k), and its cross-reference conjectures containment in
A115803. A115803 revision 13 defines the natural numbers k satisfying
11*k = A048720(31,k). Both sequences include zero. The exact question is

$$
\forall k\in\mathbb N,\qquad 13k=C(29,k)\ \Longrightarrow\ 11k=C(31,k).
$$

Here C is the binary carryless product of A048720 revision 62. If a_i and
b_i are the binary digits of a and b, the t-th binary digit of C(a,b) is
the sum of a_i*b_(t-i) over 0 <= i <= t, reduced modulo two. Thus C is
coefficient convolution over GF(2). Multiplication outside C is ordinary
natural-number multiplication. Every occurrence of k denotes the same
natural number, with no positivity or size restriction.

## Motivation

The question compares solution sets for two different pairs of ordinary
and carryless multipliers. Antti Karttunen authored the multiplier entries
in 2006 and the operation entry in 1999. The OEIS Foundation citation year
2026 is an institutional database citation, not the question's original
publication date. The proof is repository-derived and acknowledges both
the externally authored question and its operation.

## Gap

The qualified source scope is A115805 revision 14 and its containment
cross-reference, A115803 revision 13, A048720 revision 62, and their inspected
OEIS internal pages and revision histories. The source containment is
labelled conjectural in that scope. The associated bounded literature
qualification is identified by issue 23302. No published resolution was
identified within that qualification; this does not establish worldwide
priority or rule out private or unindexed proofs. A finite list of sequence
terms alone cannot establish the all-natural-number implication.

## Route

The shared owner CarrylessMultiplierEquivalence defines genuine binary
coefficient convolution and proves its equality to binaryProduct, the XOR
recursion. Its holds predicate records an ordinary-multiplication carry
and a carryless-output residue; holds_step relates reading one binary digit
to the residual input.

The new relation contains 50 pairs of these states. Kernel-checked finite
certificates establish initial membership, the implication at residual
input zero, and closure under each Boolean input digit, giving 100
pair-digit transition obligations. Nat.evenOddRec then proves the state
implication for every natural input. Applying it to the initial pair gives
the exact source implication; the finite certificate is an invariant for
the universal induction.

## Falsifier

A natural number k, including zero, for which ordinary 13*k equals
C(29,k) but ordinary 11*k differs from C(31,k) would refute the question's
implication. The operation must use the full GF(2) convolution definition.

## Evidence

The theorem is
`D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result`.
Its compiled type quantifies over every natural k with exactly the stated
premise and conclusion. Its axiom closure is propext, Classical.choice
and Quot.sound. The 50-pair certificate and the Nat.evenOddRec induction
are retained in the same Lean module. The shared semantic bridge is
`D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.carryless_eq`.

The source-linked Library note uses bibkey oeis2026a115803. Source locators
are https://oeis.org/A115805/internal, https://oeis.org/A115803/internal
and https://oeis.org/A048720/internal. OEIS source material is licensed
CC-BY-SA-4.0; citation-only describes this note's usage, not that license.

The retained typed Reg mirror has audit status declared_unresolved with
IE-C050/source.residual_requires_open. The unfinished audit is disclosed at
https://github.com/the-omega-institute/trureturing/issues/23302#issuecomment-6480201651.
This disclosure does not assert declared_validated or waive kernel,
axiom, sorry or frozen-state checks.

## Triage

Proved: the exact universal containment implication is the result theorem
above. Its Scribe carries one Proved binding for this one external question.
No converse, classification of either solution set, or other question is
claimed. A finite carry characterization remains an unresolved internal
candidate and supplies no additional resolution.

### What the settlement shows

The source solution set A115805 is contained in A115803 for every natural
input, by the result theorem. No dependent theorem or separate follow-up
question relying on this conjecture was identified in the retained source
scope. Questions beyond this implication remain outside the result.

## ASSUMED-UNVERIFIED

First-publication priority and exhaustive absence of an earlier proof are
unverified because the literature qualification is bounded. The source to
Lean interpretation is documentary and independently reviewed; the kernel
checks the stated convolution and implication. The Reg audit remains
unfinished at the linked issue and is not reported as validated.
