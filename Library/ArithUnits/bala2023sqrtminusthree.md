---
bibkey: bala2023sqrtminusthree
authors: P. Bala
year: 2023
title: OEIS A363411 and A363412 — quadratic integer product coordinates
doi: null
url: https://oeis.org/A363411
claim: The entries conjecture the five-adic real-coordinate formula, the initial type-one prime list, and two three-adic imaginary-coordinate properties.
strata_touched:
  - D5/S3/Arith/Congruence/BalaA363411
  - D5/S3/Arith/Congruence/BalaA363411TypeOne
  - D5/S3/Arith/Congruence/BalaA363412
  - D5/S3/Arith/Congruence/BalaA363412Valuation
license: citation-only
triage: anchor
---

# Bala's quadratic integer products

## Verified locator

url: https://oeis.org/A363411

doi: null

Companion entry: https://oeis.org/A363412

Characteristic sequence: https://oeis.org/A079998

The source is OEIS A363411 revision 18 and A363412 revision 19, as
quoted in issues #18633, #18634, #18635 and #18636. OEIS has no page numbers.

## Source statements

A363411 NAME: “a(n) = the real part of Product_{k = 0..n} 1 + k*sqrt(-3).”

A363411 FORMULA: “Conjecture: the 5-adic valuation v_5(a(n+2)) = A079998(n) (checked up to n = 5000).”

A079998 NAME: “The characteristic function of the multiples of five.”

A363411 COMMENTS: “Type 1: primes that do not divide any element of the sequence {a(n)}.”
“We conjecture that the set of type 1 primes begins {3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101, ...}.”

A363412 NAME: “a(n) = 1/sqrt(3) * the imaginary part of Product_{k = 0..n} 1 + k*sqrt(-3).”

A363412 FORMULA: “Conjectures: 3 does not divide a(3*n+1) for all n; the 3-adic valuation v_3(a(3*n)) = v_3(a(3*n-1)) for all n.”

## Mathematical scope

In the integer quadratic algebra with t squared equal to -3, let
P(n) be the product of 1+kt for k from 0 through n. Its coordinates are
called a(n) and b(n). They start with [1, 1, -5, -32, 112] and
[0, 1, 3, -12, -140]. The second sequence is the source's imaginary part
divided by sqrt(3).

The five-adic formula holds at every natural index. The type-one
classification concerns exactly the primes at most 101 and every term
index, without an upper bound on the latter. Nondivisibility by three
holds at 3n+1 for every natural n. The paired three-adic equality starts
at n=1, so both sequence arguments belong to the source's domain.

The proofs use scalar blocks of the coordinate recurrence, finite
residue certificates and two reflection congruences. The scalar-two
block argument requires an odd prime: at p=2 the block is (1,1).
Neither a classification of all inert primes nor a general-d triangular
valuation formula is asserted.

## Computation and literature boundary

The experiment is in the private repository
the-omega-institute/trureturing-experiments, at commit
f06c1e206be09aec0c8733382cae1a6219690f92, under
docs/reports/oeis-a363411-a363412-bala-sqrt-minus-three-products/.
The check.py SHA-256 is
88fcd4332f9c0f65e7ebd18a256f8cde079f8713bf85f142845a9f627d18b992.
The reported command `python3 check.py 3000 300` exits 0 with RESULT PASS.
This computation is separate from the unbounded Lean statements.

The literature screen in #18633 includes the OEIS entries and V. H.
Moll's “An arithmetic conjecture on a sequence of arctangent sums” (2012),
which treats the analogous product with i. No proof of the present
conjectures was found in that screen. Completeness of the external
literature screen is ASSUMED-UNVERIFIED.
