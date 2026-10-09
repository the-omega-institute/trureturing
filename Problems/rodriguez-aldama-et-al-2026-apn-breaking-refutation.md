---
slug: rodriguez-aldama-et-al-2026-apn-breaking-refutation
bibkey: rodriguezaldama2026apnbreaking
doi: 10.48550/arXiv.2609.22394
url: https://arxiv.org/abs/2609.22394v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/APNBreakingRefutation.result
---

# Conjecture 3.1: APN functions and large binary flats

## Problem

Rodríguez-Aldama–Šehović–Pasalic–Kudin, arXiv:2609.22394v2, §3.1:

> Definition 3.1. We say that a mapping F : F_{2^n} → F_{2^n} breaks a flat A of F_{2^n} if F(A) is not a flat of F_{2^n}. If F breaks all k-dimensional flats, F is said to be k-breaking.

> Conjecture 3.1. Any APN function F over F_{2^n} is k-breaking for ⌊n/2⌋ + 1 ≤ k ≤ n − 1.

A k-flat is a coset a+V of a k-dimensional binary subspace. APN means
that F(x+a)+F(x)=b has at most two solutions for every nonzero a and every b.
The Lean `claim : Prop` quantifies over all finite fields K of characteristic
two and cardinality 2^n, every such APN function, every permitted k,
every offset and every submodule of binary dimension k. Its conclusion
excludes an image equal to a coset of a subspace of any dimension.
Characteristic two provides the canonical `ZMod 2`-algebra and module.
A decidable equality instance enables finite fiber counting and places
no restriction on the mathematical fields.

## Motivation

The conjecture connects differential nonlinearity to the destruction of
large affine subspaces. APN bounds individual derivative fibers; the
asserted conclusion would constrain entire image sets independently of
whether the function is injective.

## Gap

Version 2 of the source still states this assertion as a conjecture.
Its settlement is scoped to the quoted statement, including arbitrary
non-injective APN functions and images of arbitrary dimension.
No exhaustive literature-priority determination is asserted.

## Route

Let W be the binary vector space with four coordinates, labeled
(a₀,a₁,a₂,a₃) by a₀+2a₁+4a₂+8a₃. Define G by the values

```
0, 9, 4, 11, 0, 14, 1, 9, 15, 2, 6, 13, 1, 11, 13, 1.
```

Its origin is x³+L(x) in the polynomial field model
F₂[x]/(x⁴+x+1), with linear column labels 8,12,12,5.
The Lean argument uses the explicit table, without asserting that
polynomial representation.

For every nonzero direction, each derivative fiber has at most two
points. The input subspace A is defined by a₂=0, with labels
{0,1,2,3,8,9,10,11}. Its image is
B={0,2,4,6,9,11,13,15}, defined by a₀=a₃, or span{2,4,9}.
In particular B itself is linear; 9+B=B.
The eight elements of A give binary dimension three.

Mathlib's `GaloisField 2 4` has cardinality sixteen and binary dimension
four. A binary linear isomorphism e from W to this field transports
G to F=e∘G∘e⁻¹. The APN condition is invariant under an additive
isomorphism, because corresponding derivative fibers are bijective.
Linear isomorphisms transport cosets and preserve their dimensions.
Thus F is APN and sends the three-flat e(A) to the flat e(B).
At n=4 the allowed interval is 3≤k≤3, so k=3 refutes the conjecture.
Field multiplication is not needed by this construction.

## Falsifier

The conclusion would fail to refute the conjecture if a derivative fiber
had more than two elements, if the input were not three-dimensional,
if its full image differed from B, if B were not a binary subspace,
or if the vector-space example were not transported to an actual
field of the required order. The proof of `result` discharges all
these obligations, including both numerical bounds on k.

## Evidence

`D5/S3/Arith/APNBreakingRefutation.result` has the closed Lean type
`¬ claim`. The finite table, APN bounds and full image equality are
checked by kernel reduction. The field and dimension facts come from
pinned Mathlib; both coordinate-transport statements are proved in the
module and used by `result`. No new axiom, `sorry` or `native_decide`
is used.

## Triage

- [proved: D5/S3/Arith/APNBreakingRefutation.result] The stated universal
  conjecture is false at n=4, k=3. This example preserves a full
  three-dimensional image, so the failure is not solely a dimension drop.
  APN bounds on derivative fibers do not force the image of each large
  flat to lose its affine structure.
- [computed: exact binary polynomial arithmetic modulo x³+x+1]
  At n=3, k=2, x³+x² has values [0,0,7,1,3,1,5,1] and maximum
  derivative fiber size two. The affine two-flat {1,3,5,7} maps to
  {0,1}, a one-flat. By the paper's Corollary 3.1, an APN map with a fibre of
  at least three points has unbroken two-flats, and k = 2 lies in the
  conjectured range only for n = 3; this corollary-based statement is not
  separately formalized here.
- [computed: exact binary polynomial arithmetic modulo x⁵+x²+1]
  A dimension-five example x³+L(x) has linear column labels
  [13,27,24,0,26]. Its derivative fibers have maximum size two.
  The three-flat {1,4,9,12,18,23,26,31} has image
  {9,10,12,15,17,18,20,23}, a three-flat. These facts are finite
  computations, not Lean theorems in this module.
- [computed: exact binary polynomial arithmetic modulo x⁶+x+1]
  Forty random linear perturbations of x³ gave no flat image among
  any four-flat or five-flat. Each function was checked against all
  651 binary four-subspaces and all 63 binary five-subspaces, including
  all their cosets. The reproducible sampling convention is
  `random.Random(14556)`, with two dimension-five column lists drawn
  before the forty dimension-six lists. This finite sample does not
  establish a universal assertion.
- [open] Whether the conjecture holds for APN permutations, or for
  all APN functions when n≥6, is not settled by these examples.
  Those restrictions require separate statements and arguments.
- [open] Any downstream conclusion using unrestricted Conjecture 3.1
  must establish an appropriate replacement hypothesis. No further
  theorem of the source paper is refuted by this module.

## ASSUMED-UNVERIFIED

The arXiv history of 2609.22394 shows versions 1 and 2; version 2 still states
Conjecture 3.1, and its revision comments concern Proposition 3.3. Searches by
title, identifier, "k-breaking" and author names, MathDB title and author
searches, and the formal-conjectures repository returned no settlement.
Citation indexes (Google Scholar, Semantic Scholar) were not reachable, so
forward citations were not screened exhaustively.
