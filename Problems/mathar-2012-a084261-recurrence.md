---
slug: mathar-2012-a084261-recurrence
bibkey: mathar2012a084261
doi: null
url: https://oeis.org/A084261
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA084261.result
---

# Mathar's recurrence for OEIS A084261

## Problem

The official OEIS FORMULA field defines

> a(n) = Sum_{k=0..floor(n/2)} C(n, 2k)*k!.

Its named conjecture is

> Conjecture: 2*a(n) -4*a(n-1) +(-n+2)*a(n-2) +(n-2)*a(n-3)=0. - _R. J. Mathar_, Nov 30 2012

[Issue #27208](https://github.com/the-omega-institute/trureturing/issues/27208)
fixes the complete event: for every natural `n >= 3`,

$$
2a(n)-4a(n-1)+(2-n)a(n-2)+(n-2)a(n-3)=0.
$$

The sequence is natural-valued and is defined by the literal inclusive sum.
Its Lean range is `Finset.range (n/2+1)`, including both endpoints from zero
through `floor(n/2)`. Indices use natural subtraction; signed arithmetic uses
integer casts of `n` and each sequence value. The source specifies no onset:
`n>=3` is the disclosed interpretation keeping all predecessor indices
nonnegative. There is no analytic premise or finite upper bound.

## Motivation

The statement supplies an exact relation between four consecutive values of
the entire literal sequence. A081124 has a different sum and final coefficient;
its result is neither imported nor substituted for this conjecture.

## Gap

The bounded source qualification in #27208 found no exact recurrence settlement
in its arXiv and Crossref identifier searches, the inspected A084261 passage of
Fang–Hamaker–Troyka (arXiv:2009.00079v3), or the pinned jOEIS sum implementation.
These searches support only absence in those inspected scopes. They establish
neither worldwide openness nor priority. The named source assertion is from
2012; it is treated as a tier-1 external symbolic conjecture under that bounded
qualification.

## Route

Let `b(k)=(k/2)!` when `k` is even and zero otherwise, and let
`T(c,n)=sum_{k=0..n} C(n,k)c(k)` in the integers. The pinned Pascal-sum identity
relates `T(c,n+1)` to `T(c,n)` and `T(k -> c(k+1),n)`. Parity and factorial
succession supply the local relation

$$
2b(k+3)+2b(k+2)-3b(k+1)-2b(k)=k b(k+1)+k b(k).
$$

The weighted binomial identity and a finite-range shift with vanishing
endpoint terms transform its right side. Eliminating the shifted transforms
gives the forward recurrence. The nonzero-summand bijection `k -> k/2`
identifies `T(b,n)` with the exact defining sum, including odd-term vanishing,
both endpoints, injectivity and surjectivity. Substituting `n=m+3` proves the
whole target domain. All auxiliary propositions are local to `result`.

## Falsifier

A natural `n>=3` for which the original inclusive sum has nonzero integer
recurrence residual would contradict `D5/S1/Recurrence/MatharA084261.result`.

## Evidence

The mathematical source is `D5/S1/Recurrence/MatharA084261.lean`; its included
surface is exactly `a : Nat -> Nat`, `claim : Prop`, and `result : claim`.
The canonical frozen member is
`Golden/Frozen/state/D5/S1/Recurrence/MatharA084261.lean.json`, with module
`statement_id`
`sha256:798d087a84b5ccc3ad4470867f70703fc3bb499d0d876d04337f2c066a6011ae`.
The result declaration has `statement_id`
`sha256:5a76ce4a0fcb38093dc87d56a7d95cea1b2eedf9281fb3433dfd49da991dec09`.
The corresponding Blueprint displays the literal sum, the complete universal
integer recurrence and its typed `Proved` resolution claim.

## Triage

Admission basis is `open-problem-resolution` under #27208 and CLAUDE §3.2(a)–(d).
The result's proof shape is `bind-only`: pinned Mathlib identities, parity,
finite-sum reindexing, casts and normalization. There is no escape witness or
direct frozen project GID predecessor. The definitions `a` and `claim` are
necessary to state the event; no companion result is exported. Utility is
`none`, since this is an unbounded symbolic recurrence rather than a finite
certified instance.

### What the settlement shows

- **Proved in `D5/S1/Recurrence/MatharA084261.result`:** the exact source-sum
  recurrence holds at every natural `n>=3`, without an added hypothesis.
- **Proved locally inside that result:** the parity relation, weighted
  transform elimination and nonzero-summand identification are the mechanism
  connecting the literal sum to the recurrence. These are proof components,
  not additional exported or independently registered resolutions.
- **Open in this delivery:** generating-function, asymptotic and neighboring
  conjecture consequences require their own statements and proofs. No
  dependency from this recurrence to another source assertion is established.
- **Open:** extension below index three requires a convention for negative
  sequence indices; no such extension is asserted.

## ASSUMED-UNVERIFIED

Worldwide novelty, priority and absence of a settlement outside the bounded
source searches remain unverified. The information-escape audit is unfinished
under [the disclosed source-role gap](https://github.com/the-omega-institute/trureturing/issues/27208#issuecomment-6678688974).
The retained typed Reg client compiles, but its record is `declared_unresolved`:
`IE-C050 ClosedTruthReadout`, `unclassified_form`, `source.roles`. A classified
source-role binding and its full certificate are missing. Neither mathematical
compilation nor the resolution claim asserts `declared_validated`.
