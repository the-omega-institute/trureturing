---
slug: oeis-a284005-kurkov-weight-product-binomial
bibkey: karttunen2017a284005
doi: null
url: https://oeis.org/A284005
triage: theorem
motivation_gids:
  - D5/S1/Digit/KurkovWeightProductBinomial
---

# Kurkov's binomial identity for binary-weight products

## Problem

OEIS A284005, NAME (`%N`, verbatim):

> a(0) = 1, and for n > 1, a(n) = (1 + A000120(n))*a(floor(n/2)); also a(n) = A000005(A283477(n)).

The settled FORMULA (`%F`, verbatim):

> Conjecture: a(2^m*(2n+1)) = Sum_{k=0..m+1} binomial(m+1, k)*a(2^k*n) for m >= 0, n >= 0 with a(0) = 1. - _Mikhail Kurkov_, Apr 24 2023

AUTHOR (`%A`, verbatim):

> _Antti Karttunen_, Mar 18 2017

Here `wt(n)=A000120(n)` counts ones in the binary expansion, represented
by `(Nat.digits 2 n).sum`. The NAME specifies the recurrence for `n>1`;
the entry's data fixes `a(1)=2`. Accordingly, the formal definition is
`a(0)=1` and `a(n+1)=(1+wt(n+1))*a((n+1)/2)` for every natural `n`,
where `/` is natural floor division. This reproduces the initial terms
`1,2,4,6,8,12,18,24,16,24,36,48,54,72,96,120`.

The exact Lean statement is:

```lean
theorem result (m n : ℕ) :
    a (2 ^ m * (2 * n + 1)) =
      ∑ k ∈ Finset.range (m + 2), Nat.choose (m + 1) k * a (2 ^ k * n)
```

Both quantifiers include zero. The sum runs from `k=0` through `k=m+1`,
and every quantity is a natural number. Only the quoted binomial
conjecture is asserted: the 2019 bit-flip recursion, the 2023 mod-2
binomial-transform conjecture for A329369, and the representation
`A000005(A283477(n))` are not claimed.

## Motivation

Successive binary shifts define a product whose factors depend on digit
weight. A power of two contributes repeated equal factors. The identity
expresses every shifted odd index as a binomial combination of shifted
values, uniformly in both unbounded natural parameters.

## Gap

Readings of 2026-09-15: OEIS still labels this line "Conjecture". OpenAlex search `A284005` returned no result; the
Math.SE API and formal-conjectures each returned zero hits. The arXiv
API returned HTTP 429/503, so arXiv was not searched.

The supplied repository prior-art reading at
`c287435f932b9bb0a1a23370e1a60377e0a0dc8f` found no A284005/A283477
declaration in D5, Library, or Problems. Pinned Mathlib supplies
`Nat.digits`, `Nat.digits_base_pow_mul`, `add_pow`, and `Nat.choose`,
but no theorem for this sequence was found in the searched scope.
The prior-art conclusion is `not-found-in-searched-scope`, without a
completeness claim.

Pre-registration issue #8071 was created at `2026-09-15T10:20:12Z`,
before the probe started, according to the supplied registration reading.
The assigned tier is the small external-conjecture lane. Registration
timing and historical openness have not been independently checked here.

## Route

The binary-weight definition is reused by import from the frozen
`D5/S1/Digit/DyadicRowPolynomialRecurrence.wt`, with declaration
`statement_id sha256:97e8780c8f32b7d18f85865017f8f6cd93a28ef09cc8d352835df20fa177420b`
and module pin
`sha256:727c60fc4a516853688eec83ce3eebfdc232ba5ef95962e48de94bbbb346c3b7`.
Its module has generality G.

The proof step `wt(2^k*n)=wt(n)` follows from Mathlib
`Nat.digits_base_pow_mul` at positive `n`, followed by
`List.sum_append` and `List.sum_replicate`; at zero it is immediate.
This derivation is a local `have` in each product induction.
Induction on `k` gives the first product identity, including the
separate zero case:

```text
a(2^k*n) = (1+wt(n))^k*a(n).
```

The odd recurrence and induction on `m` give the second identity:

```text
a(2^m*(2*n+1)) = (wt(n)+2)^(m+1)*a(n).
```

Apply the binomial theorem to `((1+wt(n))+1)^(m+1)`, distribute the
factor `a(n)` through the sum, and replace every term using the first
product identity. The zero endpoints require no additional hypothesis.

The public theorem has `proof_shape: bind-only` and
`admission_basis: open-problem-resolution` (pre-registration #8071). The
two product identities `a(2^k n) = (1+wt(n))^k a(n)` and
`a(2^m(2n+1)) = (wt(n)+2)^(m+1) a(n)` are established as `have` steps
inside `result` by explicit inductions on `k` and on `m`. The
judgement-form review classified both as bind-only: each is the iteration
specialization (`Function.Semiconj.iterate_right`) of a one-step equation
obtained by unfolding `a` and `Nat.digits_base_pow_mul`, followed by
normalization, so neither is an escape witness. The weight-invariance, elementary digit,
and recurrence steps are likewise local `have` terms. The only direct
frozen-project declaration dependency is the `wt` definition above.
The named external-conjecture resolution is also recorded in Scribe
as `OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

`utility: none` applies to all declarations: the definition `a`,
unbounded symbolic inductions, and universal identity are not bounded
enumerations, checkers, numeric reductions, or certified finite instances.
The numeric check is not a premise of any formal proof.

## Falsifier

A pair of naturals `(m,n)` for which the displayed left-hand value
differs from the binomial sum would refute the identity. A mismatch
between the recurrence and the entry's initial terms, including
`a(0)=1` and `a(1)=2`, would invalidate the sequence interpretation.

## Evidence

- `lake env lean D5/S1/Digit/KurkovWeightProductBinomial.lean`:
  exit 0, zero warnings, under pinned Lean 4.33.0.
- `tools/scripts/agent/header-check.sh` on the final module: exit 0;
  135 lines, 43 Lean files in the immediate directory, generality G
  compliant. The public source declarations are exactly `a` and
  `result`; the module has no other declarations.
- The axiom audit of the final source: exit 0. The definition `a` and
  `result` each have exactly
  `[propext, Classical.choice, Quot.sound]`. The final source contains
  no `sorry`, `native_decide`, or new axiom.
- The elaborated-proof dependency check: exit 0. The proof value of
  `result` contains both product identities as local `have` terms, and
  each uses Mathlib `Nat.digits_base_pow_mul` as a local proof step. The sole
  direct frozen-project declaration dependency is the reused
  `D5/S1/Digit/DyadicRowPolynomialRecurrence.wt`, with the declaration
  statement identity and module pin recorded in Route.
- Direct Lean execution of the final definitions: exit 0; 22000 pairs
  with `0 <= m <= 10` and `0 <= n < 2000`; zero conjecture,
  product-identity, or weight-invariance exceptions; all 16 displayed
  initial terms match. This bounded check supplies no proof premise.

The final direct-import deletion check is:

| Deleted import | Lean exit | Failure |
| --- | ---: | --- |
| `D5.S1.Digit.DyadicRowPolynomialRecurrence` | 1 | Unknown frozen namespace and `wt` |

The digit and binomial APIs are available through that import;
`Mathlib.Data.Nat.Digits.Defs` and `Mathlib.Data.Nat.Choose.Sum` are
not separate direct imports.

## Triage

`theorem`; resolution `proved` for the quoted Kurkov binomial identity
on all natural `m,n`, with the sequence interpretation and scope wall
stated above.

## ASSUMED-UNVERIFIED

The arXiv search was not performed (HTTP 429/503 at query time).
Historical openness outside the searched surfaces (OEIS text, OpenAlex,
Math.SE, formal-conjectures, repository prior art) is unverified, and no
exhaustive literature search or priority claim is made. Bounded numerical
checks do not establish the universal identity; the Lean theorem does.
