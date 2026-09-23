---
bibkey: parisse2024hypersequences
authors: Daniele Parisse
year: 2024
title: "On Hypersequences of an Arbitrary Sequence and Their Weighted Sums"
doi: 10.5281/zenodo.13331499
url: https://math.colgate.edu/~integers/y70/y70.pdf
claim: "Section 4 states two conjectures: the alternating factorial-Stirling weighted sum of the even-index Fibonacci numbers equals the signed plain weighted sum of the preceding Stirling row, and the same identity with the Lucas numbers in place of the Fibonacci numbers."
strata_touched:
  - D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum
license: citation-only
triage: anchor
---

# Parisse, hypersequences of an arbitrary sequence and their weighted sums

## Verified locator

DOI: 10.5281/zenodo.13331499

URL: https://math.colgate.edu/~integers/y70/y70.pdf

*Integers* **24** (2024), Article A70, received 8/28/23, revised 9/28/23, accepted
7/22/24, published 8/16/24. The author is Daniele Parisse, Airbus Defence and
Space GmbH, Manching, Germany. The volume index at
https://math.colgate.edu/~integers/vol24.html carries the same author, title and
article number, and the DOI printed on page 2 of the article resolves to the same
record.

## Definitions

For a sequence `(a_n)` the article writes `a_n^{(r)}` for the hypersequence of the
`r`-th generation, defined by `a_n^{(r)} = ∑_{k=0}^{n} a_k^{(r-1)}` with
`a_n^{(0)} = a_n`, and studies the weighted sums
`t_ℓ^{(r)}(n) = ∑_{k=0}^{n} k^ℓ a_k^{(r)}`. Theorem 9 expresses these through the
coefficients

    c_{ℓ,m}(n) = ∑_{k=0}^{m} (-1)^k C(m, k) (k + n + 1)^ℓ ,

which do not depend on `r`. Section 3 writes `S(j, m)` for the Stirling numbers of
the second kind, defined there as the number of partitions of a set of `j`
elements into exactly `m` nonempty blocks, and Equation (3.14) evaluates the
constant term

    c_{ℓ,m}(0) = (-1)^m m! S(ℓ + 1, m + 1) .

`F` denotes the Fibonacci numbers with `F_1 = F_2 = 1` and `L` the Lucas numbers
with `L_0 = 2`, `L_1 = 1`.

## The statements in question

Section 4 applies Theorem 9 to the Fibonacci sequence, obtaining Equation (4.7),
and then states:

> Conjecture 1. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) F_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) F_{m+2} .

The remark immediately after reads: "Note that the unsigned sum on the
right-hand side (the sequence A000557 in [21]) is exactly the sequence `M_{2,j}`."
That remark fixes the reading of the stacked bracket symbols as Stirling numbers
of the second kind rather than binomial coefficients, because A000557 is recorded
as `a(n) = ∑_{k=0..n} k! Stirling2(n, k) Fibonacci(k+2)`.

The Lucas analogue follows the same pattern. After Equation (4.9) the article
states:

> Conjecture 2. For all ℓ ∈ N_0, we have
>
>     ∑_{m=0}^{ℓ} (-1)^m m! S(ℓ+1, m+1) L_{2(m+1)} = (-1)^ℓ ∑_{m=0}^{ℓ} m! S(ℓ, m) L_{m+2} .

with the remark that multiplying the right-hand side by `-1` gives A263968, whose
recorded formula is `a(n) = (-1)^{n+1} ∑_{k=0..n} k! Lucas(k+2) Stirling2(n, k)`.

## Scope of the recorded answer

Both identities hold, and they hold for the same reason: neither depends on the
initial values of the sequence, only on the recurrence `u_{n+2} = u_n + u_{n+1}`.
The recorded result establishes the common generalisation for an arbitrary
integer sequence satisfying that recurrence and reads off the two conjectures as
the Fibonacci and Lucas instances.

## Bounded prior-resolution evidence

The author's own sequel, *On Hypersequences of an Arbitrary Sequence and Their
Weighted Sums II*, *Integers* **26** (2026), Article A36, published 2/20/26, was
opened in full: it contains no occurrence of the word conjecture and does not
return to either statement. The OEIS entries A000557 and A263968 were opened; both
link this article and neither records the alternating identity among its formulas
or any proof of it. A web pass over the two sequence numbers and the article title
returned no proof; the nearest recent item, arXiv:2511.10797 on weighted sums of
Lucas sequences, mentions neither Parisse nor Stirling numbers. Citation-index
result pages were not exhaustively reachable, so this is a bounded negative
finding and no worldwide priority claim is made.
