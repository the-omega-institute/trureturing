---
slug: mathar-2012-a081124-recurrence
bibkey: mathar2012a081124
doi: null
url: https://oeis.org/A081124
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA081124.result
---

# Mathar's recurrence for OEIS A081124

## Problem

The official OEIS FORMULA field defines

> a(n) = Sum_{k=0..n} C(n, k)*floor(k/2)!.

Its named conjecture is

> Conjecture: 2*a(n) -4*a(n-1) +(-n+2)*a(n-2) +(n-1)*a(n-3)=0. - _R. J. Mathar_, Nov 24 2012

The precise target, preregistered in
[unit #27174](https://github.com/the-omega-institute/trureturing/issues/27174), is

$$
\forall n\in\mathbb N,\quad n\ge3\Longrightarrow
2a(n)-4a(n-1)+(2-n)a(n-2)+(n-1)a(n-3)=0.
$$

The sequence is the literal inclusive finite natural sum, with natural
binomial coefficients and factorials. Every signed operation in the recurrence
is in the integers after casting `n` and the sequence values. The source does
not specify an onset: `n>=3` is the disclosed interpretation keeping all four
indices nonnegative. No negative-index convention is asserted.

## Motivation

The recurrence determines an exact relation between four consecutive values
of the entire sequence defined by the source sum. Its last coefficient is
`n-1`; the separate A084261 conjecture has a different defining sum and is
outside this assertion.

## Gap

The current official revision 20 retains the conjecture label. The bounded
source/supplier readings in #27161, reconciled in #27174, did not find an exact
published settlement. Goyt–Pudwell's JIS 15 Article 12.6.2 Theorem 14 and Table 2
class 5 give the same-sum counting interpretation; Mathar arXiv:2109.02112v1
provides general generating-function machinery. Neither is assumed to supply
this recurrence. Current jOEIS code implements the sum. These findings do not
establish global absence or priority.

## Route

Let $b(k)=\lfloor k/2\rfloor!$ and
$T(c,n)=\sum_{k=0}^n\binom nk c(k)$ in the integers. The pinned Pascal-sum
identity gives $T(c,n+1)=T(c,n)+T(k\mapsto c(k+1),n)$. Factorial successor and
the even/odd decomposition of $k$ give

$$
2b(k+3)+2b(k+2)-3b(k+1)-b(k)=k b(k+1)+k b(k).
$$

For the right side, the binomial identity
$\binom n{k+1}(k+1)=\binom nk(n-k)$ and a finite-range shift with both endpoint
terms zero give

$$
n T(k\mapsto b(k+1),n)
=\sum_{k=0}^n\binom nk k b(k+1)+\sum_{k=0}^n\binom nk k b(k).
$$

Applying the transform to the parity relation and eliminating shifted
transforms yields

$$
2T(b,n+3)-4T(b,n+2)-(n+1)T(b,n+1)+(n+2)T(b,n)=0.
$$

Casting through the complete finite sum identifies $T(b,n)$ with $a(n)$.
Replacing the forward index by `n-3` gives the entire target domain.

## Falsifier

A natural `n>=3` for which the original inclusive sum has nonzero signed
recurrence residual would contradict `result`.

## Evidence

The mathematical source is `D5/S1/Recurrence/MatharA081124.lean`; its included
surface is exactly `a : Nat -> Nat`, `claim : Prop`, and `result : claim`.
All mathematical auxiliary propositions are local to `result` and used in its
proof. The corresponding canonical Scribe displays the inclusive sum, complete
claim, all integer casts, and the `Proved` resolution claim.

## Triage

Tier 1 named external conjecture. Intended admission is
`open-problem-resolution` under CLAUDE 3.2(a)-(d), with independent assessment
pending. Provisional proof shape is `bind-only`: the argument composes pinned
binomial/factorial identities with parity decomposition, finite-sum shifts,
and algebraic normalization. It claims no independent escape witness.
Utility is `none`: this is an unbounded symbolic recurrence proof, not a
finite certified instance or enumeration.

The entire recurrence is kernel checked. The source's generating-function
and asymptotic formulas remain outside this delivery, and no implication
from the recurrence to them is asserted. An extension below index three
requires a convention for negative sequence indices and is not proved.
The parity and weighted-transform relations describe the mechanism of this
proof; no additional exported theorem or neighboring conjecture is claimed.

The previous probe #27161 remains unresolved under its original controls;
this fresh formal continuation does not alter that timed outcome.
Independent assessment, freeze, required CI and integration remain separate
from the mathematical proof.

## ASSUMED-UNVERIFIED

Worldwide novelty, priority and absence of a settlement outside the bounded
source searches are unverified. The information-escape registration requires
its own source-bound validation and is not certified by mathematical
compilation alone.
