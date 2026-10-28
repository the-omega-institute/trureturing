---
slug: tebni341724-row-divisibility
bibkey: tebni2023a341724
doi: null
url: https://oeis.org/A341724
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.result
---

# Tebni's prime and dyadic row-divisibility conjectures for A341724

## Problem

The Comments block of [OEIS A341724](https://oeis.org/A341724), revision 26,
attributes these conjectures to Mélika Tebni in 2023:

> For 0 < k < p and p prime, T(p,k) == 0 (mod p).
>
> For 0 <= k < n and n = 2^m (m natural number), T(n,k) == 0 (mod n).

The Formula block specifies the column EGF as
$x^k/(k!(1-2\sinh(-x)))$. The conjectures concern
$T(n,k)=n![x^n]x^k/(k!(1-2\sinh(-x)))$ over the rationals.
The 2021 Shannon–Ollerton paper describes the array, rather than stating
these 2023 conjectures.

## Motivation

This is a tier-one external open-problem settlement under
[preregistration #23158](https://github.com/the-omega-institute/trureturing/issues/23158).
The source EGF and both full domains, including p=2, m=0 and dyadic k=0,
are preserved. Integrality is a conclusion, supplied before the integer
numerator is used as the witness. There is no finite row bound.

## Gap

No exact prior settlement was found in the bounded source and library
screen in #23158. Repository searches include public and private D5
statements and theory/digestion correspondence. The pinned Mathlib and
GitHub Lean-code searches have no exact A341724 settlement in the searched
scope. These negative searches do not establish exhaustive originality.

## Route

Set $H=1-2\sinh(-X)=1+2\sinh X$ and $C_k=X^k/(k!H)$.
Then $C_k H=X^k/k!$, and the factorial-normalized convolution gives

$$
T(n,k)=\mathbf{1}_{n=k}
 -2\sum_{\substack{1\le j\le n\\j\text{ odd}}}
       \binom nj T(n-j,k).
$$

The forcing term is present for all n and k. The column support gives
$T(n,k)=0$ for n<k and the diagonal is one. Strong induction proves all
coefficients integral. The recurrence is transferred to integers only
after this bridge is established.

For n>k the forcing term vanishes. At a prime row, the interior binomial
coefficients are divisible by p. The j=p endpoint is zero because
$k>0$ implies $T(0,k)=0$. At a dyadic row, every odd-index binomial
coefficient is divisible by $2^m$; this includes m=0 without an extra
hypothesis. The original suppliers are
`IntegralEGFComposition.eCoeff_mul`, `TebniA364822.eCoeff_sinh`,
`TebniA364822PowerOfTwo.pow_two_dvd_choose_odd`, and
`Nat.Prime.dvd_choose_self`.

## Falsifier

A nonintegral original-array coefficient at an allowed row and column,
or an allowed integer coefficient not divisible by its row modulus,
would refute the corresponding assertion. A recurrence with reversed
sign or without the exact EGF correspondence is a different object.

## Evidence

The [Lean result](../D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.lean)
proves both integer-witness clauses in one `result : claim`.
The [Blueprint](../Blueprint/D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.md)
contains the complete formulas, and the
[source note](../Library/RecurrenceComposition/tebni2023a341724.md)
records the source attribution and locator. The proof has only the
standard axiom closure; no finite table is a premise.

## Triage

- **Proved:** both original divisibility assertions for every prime and
  every dyadic exponent, within their exact column ranges.
- **Proved internally:** integrality for all natural n,k, zero support
  for n<k, diagonal value one, and the complete delta-forced recurrence.
  These are proof ingredients of the single public result.
- **Mechanism:** denominator cancellation gives the binomial recurrence;
  integrality makes integer divisibility meaningful; prime interior
  binomials and odd-index dyadic binomials make the relevant terms vanish.
- **Nearest retained ranges:** the prime case includes two and requires
  positive k; the dyadic case includes exponent zero and column zero.
  Both require k strictly below the row. The diagonal value one explains
  the exclusion for row modulus greater than one.
- **Unresolved boundary:** the public result does not settle arbitrary
  composite rows, exact valuations, or any stronger modulus. The
  recurrence suggests further statements, but no such public theorem
  is claimed here.
- **Literature:** the source definitions are literature-attested; the
  settlement is repo-derived with status not-found-in-searched-scope.
  Global novelty and exhaustive search completeness remain unverified.
