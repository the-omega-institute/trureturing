---
slug: oeis-a322026-sequence-machine-dirichlet-inverse-identity
bibkey: oeis2024a322026
doi: null
url: https://oeis.org/A322026
triage: theorem
motivation_gids:
  - D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity
---

# Sequence Machine's A322026 Dirichlet-inverse identity

## Problem

OEIS A322026's final FORMULA conjecture (revision 41, September 8, 2024) is:

> `a(n) = A323884(25*n). [Conjectured by Sequence Machine]`

The source formula is `a(n)=A071521(A065331(n))`. Equivalently, for a positive
integer `m`, let `v_2(m)` and `v_3(m)` be its 2- and 3-adic valuations, put
`c(m)=2^v_2(m)3^v_3(m)`, and let `a(m)` count all pairs of nonnegative integers
`(i,j)` with `2^i3^j ≤ c(m)`. Let `b` be the integer-valued Dirichlet inverse
of `a`, so `b(1)=1` and the positive-index convolution is zero away from one.
A323884 is the pointwise sum `a+b`. The formal carrier sets both functions to
zero at index zero and proves the identity for all natural indices, which
contains the published positive-index statement.

### Statement echo

The target is `∀ n, a n = a (25*n) + b (25*n)` under the explicit A071521/A065331
rank and Dirichlet-inverse conventions above.

## Motivation

The conjecture relates the A322026 rank sequence to its Dirichlet inverse at a
uniform square factor. A proof supplies the complete published identity and
isolates the arithmetic mechanism behind the factor 25.

## Gap

The source gives the formula as a conjecture. The formal gap is to prove the
rank formula's invariance under multiplication by 5 and then control the
Dirichlet inverse at multiples of 25 without restricting to a finite prefix or
to a special family of indices.

## Route

1. Define the rank function from the finite lattice count of exponent pairs for
   the 2- and 3-adic factorization powers.
2. Prove `a (5*n) = a n` using the natural-number factorization product API.
3. For a unit-headed arithmetic function `f` with `f (5*n)=f n`, subtract the
   prime shift, convolve with the Dirichlet inverse, and use strong induction on
   multiples of 25 to prove the inverse vanishes there.
4. Apply the general support lemma to A322026 and rewrite the resulting equality
   into the published A323884 form.

## Falsifier

A formal counterexample would need an index `n` for which the explicit rank and
Dirichlet-inverse definitions satisfy all hypotheses but
`a n ≠ a (25*n) + b (25*n)`. A finite numerical mismatch is sufficient to refute
this universal statement, while a numerical agreement on a finite prefix is not
a proof.

## Evidence

The source snapshot is the immutable `oeis/oeisdata` pin
`f151d82acb28766e6034a902ed9fd0632b16f986`, A322026 revision 41. The
preregistration is [issue #26072](https://github.com/the-omega-institute/trureturing/issues/26072).

The canonical source is
`D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.lean`.
The frozen declaration state is
`Golden/Frozen/state/D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.lean.json`.
The public declaration is
`D5.S3.Arith.DirichletInverse.OeisA322026DirichletInverseIdentity.result`.
Its axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

Tier 1 OEIS conjecture, preregistered before formalization; resolution `proved`.
The public result is kernel-checked and has no `sorry`, `native_decide`, finite-prefix
replacement, or additional axiom.

### What the settlement shows

**Proved by `result`:** For every natural index, the explicit A322026 rank equals
the sum of the rank and its integer-valued Dirichlet inverse evaluated at 25 times
the index.

**Computed, not formalized:** None.

**Argued, not formalized:** The source's restricted-growth-label construction is
used as the external interpretation of the published rank formula; the Lean
statement formalizes the explicit A071521/A065331 expression. No analytic
Dirichlet-series claim or assertion about other OEIS transforms is made.

The four-slot §3.9 registration audit for the public result remains unfinished
and is tracked in [#26181](https://github.com/the-omega-institute/trureturing/issues/26181);
no `declared_validated` status is claimed.

## ASSUMED-UNVERIFIED

The literature and OEIS reading is bounded to the cited snapshot and the source
pin above; it does not establish an exhaustive novelty or priority result. The
external restricted-growth-label interpretation, analytic Dirichlet-series
properties, and identities for other OEIS transforms remain outside the formal
statement.
