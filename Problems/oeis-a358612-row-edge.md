---
slug: oeis-a358612-row-edge
bibkey: kurkov2024a358612
doi: null
url: https://oeis.org/A358612
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge.result
---

# Kurkov's complete A358612 row-edge question

## Problem

Mikhail Kurkov's A358612 Conjectured formulas block asks, verbatim:

> T(n, A000120(n) + 2) = A341392(n) for n >= 0.

A341392 NAME is, verbatim:

> a(n) = A284005(n) / (1 + A000120(n))!.

The question is quoted from [A358612 revision 52](https://raw.githubusercontent.com/oeis/oeisdata/d8ad22d9b98d2c427be8c6cd9f2672c600b8e3ae/seq/A358/A358612.seq).
The [source note](../Library/Digit/kurkov2024a358612.md) gives the immutable
primary sources, attribution and exact scalar-program correspondence.
Write w=A000120 and P=A284005, with w(0)=0, P(0)=1, P(1)=2 and
P(n)=(1+w(n))*P(floor(n/2)) for n>1. The literal rational array has
natural rows and positive columns. Its boundaries are T(n,1)=1,
T(0,2)=1 and T(0,k)=0 for k>=3. Its recurrences are

\[
T(2h+1,k)=kT(h,k)+T(h,k-1)\quad(h\ge0,\ k\ge2),
\]
\[
T(2h,k)=kT(h,k)+T(h,k-1)-\frac{T(2h,k-1)+T(h,k-1)}{k-1}
\quad(h\ge1,\ k\ge2).
\]

The full event is T(n,w(n)+2)=P(n)/(1+w(n))! for every natural n,
including zero, with no row bound or restriction on binary patterns.

| Source clause | Lean counterpart |
| --- | --- |
| Literal scalar rational array, positive columns | Original-owner Block.T; its zero-column extension is unused |
| Binary weight including w(0)=0 | Original-owner DyadicRowPolynomialRecurrence.wt |
| P recurrence and data at zero and one | Existing KurkovWeightProductBinomial.a |
| Every natural row, rational quotient | Edge.result (n : Nat), casts of a and factorial into Q |
| No support assumption | Edge.support is proved and consumed by Edge.result |

## Motivation

The source labels this complete unbounded identity conjectural. The target
is this single row-edge question. Neither a finite check nor the separate
dyadic-block conjecture supplies another settlement credited here.

## Gap

The bounded screen recorded in [#31020](https://github.com/the-omega-institute/trureturing/issues/31020)
and [#31124](https://github.com/the-omega-institute/trureturing/issues/31124)
identified no matching full theorem in the inspected repository, pinned
Mathlib or named literature. Exact arXiv identifier metadata searches were
reported to return no records; that is not a global absence-of-proof claim.
The screen includes Ehrenborg--Steingrimsson, DOI 10.1006/aama.1999.0671,
Alekseyev's published A329369 formulas and archived MO answers 470752 and
446656. Known word recurrences and two-block formulas are reused results,
not asserted new here. MO answer 474668, current MO 486535, exhaustive
citation coverage, MathDB and access-limited OpenAlex results remain
unverified. Archived MO 483753 status is not a current no-answer certificate.
A demonstrated matching published solution would change eligibility.

## Route

Use the live original-owner block law and n=2^g(n)*(2*h(n)+1).
The parent is smaller and w(n)=w(h(n))+1. Strong induction proves
T(n,k)=0 when w(n)+2<k, independently of the edge formula. At the edge,
the upper-parent term vanishes. The existing original-owner identity
P(2^r*(2h+1))=(w(h)+2)^(r+1)*P(h), with factorial recursion, completes
the induction, with row zero handled separately. No alternate T or P,
assumed support, coefficient bridge or integrality premise is introduced.

## Falsifier

A natural row at which the literal scalar recursion violates the displayed
quotient refutes this event. A mismatch in any boundary, rational division
or source-to-Lean object correspondence invalidates the proposed settlement.

## Evidence

The kernel-checked result and its support prerequisite are in
`D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge`; their canonical Scribe
states the same all-natural-row event. The full Lean result is proved and
canonically frozen. Admission basis is the external open-problem-resolution
route; independent source/form and mirror reviews are approved.
The source-owner product helper is consumed both by its binomial theorem
and this edge result. The exposed dyadic index is consumed by the block
law and edge induction. The edge, support, block law and odd-parent
product proofs use induction. The dyadic index proof specializes
Mathlib's maximal-power decomposition and normalizes the odd quotient.
The §3.9 audit remains unfinished under the linked-issue exception in
[#31124](https://github.com/the-omega-institute/trureturing/issues/31124#issuecomment-6906238478);
none of these targets is reported declared_validated.

## Triage

- Proved, formal statement: the complete rational edge identity and support
  theorem have scoped kernel evidence; no finite-case substitute is used.
- Unresolved, delivery: the final review triplet, required CI, MERGED status
  and containing dev-push verification are pending. The §3.9 audit remains
  unfinished under the linked-issue exception above.
- Unresolved, other questions: integrality, the A329369 transform and a
  separate block-problem settlement are outside this result. No downstream
  external-question or KPI credit is claimed.

Resolution kind: proved and canonically frozen for the formal edge statement;
delivery incomplete.
Preregistration/source records:
[#31020](https://github.com/the-omega-institute/trureturing/issues/31020),
[#31118](https://github.com/the-omega-institute/trureturing/issues/31118),
[#31124](https://github.com/the-omega-institute/trureturing/issues/31124).
Publication record:
[#31138](https://github.com/the-omega-institute/trureturing/issues/31138).

## ASSUMED-UNVERIFIED

The bounded literature screen does not establish worldwide novelty or
priority; the access gaps above remain. Final delivery remains incomplete
as specified in Triage.
