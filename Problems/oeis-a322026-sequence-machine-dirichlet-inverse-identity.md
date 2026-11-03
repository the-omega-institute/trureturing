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

The preregistration is [issue #26072](https://github.com/the-omega-institute/trureturing/issues/26072). The source snapshot is the immutable `oeis/oeisdata` pin
`f151d82acb28766e6034a902ed9fd0632b16f986`, A322026 revision 41.

## Result

`D5.S3.Arith.DirichletInverse.OeisA322026DirichletInverseIdentity.result` proves
`∀ n, a n = a (25*n) + b (25*n)`.

The proof first verifies the source rank formula is unchanged by multiplication
by 5. For a unit-headed arithmetic function `f` satisfying `f(5n)=f(n)`, it
forms the difference between `f` and the 5-shift. Its Dirichlet inverse equation
is `h * f⁻¹ = 1 - δ₅`; the difference is supported away from multiples of 5.
Strong induction on a multiple of `25` then forces `f⁻¹(25n)=0`. Applying this
to the A322026 function gives `a(25n)=a(n)` and the stated identity.

The theorem is kernel-checked with the pinned Mathlib arithmetic-function
Dirichlet inverse and natural factorization/divisor APIs. No additional axiom,
`sorry`, finite-prefix replacement or prime-support restriction is used.

## Judgement form

| declaration | proof_shape | escape_witness | direct consumers | admission_basis |
| --- | --- | --- | --- | --- |
| `a` | bind-only | none | `result` | open-problem-resolution |
| `b` | bind-only | none | `result` | open-problem-resolution |
| `result` | content | `inverse_prime_square_support` on its live proof path | none | open-problem-resolution (#26072; Proved) |

The helper declarations are private and consumed on the live path of `result`.
The four-slot source audit for the public result remains unfinished and is
tracked in [#26181](https://github.com/the-omega-institute/trureturing/issues/26181); no `declared_validated` status is claimed.

## Boundary

The identity settles the preregistered whole formula under the source's rank and
Dirichlet-inverse conventions. The source's restricted-growth-label construction
is used as the external definition of the published rank formula; the Lean
statement formalizes the explicit A071521/A065331 formula quoted by the source.
No assertion about other OEIS transforms or analytic Dirichlet series is made.
