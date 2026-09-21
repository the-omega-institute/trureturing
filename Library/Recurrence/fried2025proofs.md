---
bibkey: fried2025proofs
authors: Sela Fried
year: 2025
title: "Proofs of Several Conjectures From the OEIS"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf
claim: "The end of Section 6 conjectures that for every n in N the number F(n+2) + 2nF(n+1) is not a Fibonacci number."
strata_touched:
  - D5/S3/Arith/FriedFibonacciShiftNonFibonacci
license: citation-only
triage: anchor
---

# Fried, proofs of several conjectures from the OEIS

## Verified locator

DOI: none assigned

URL: https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf

*Journal of Integer Sequences* **28** (2025), Article 25.4.3. The author is Sela
Fried, Department of Computer Science, Israel Academic College in Ramat Gan. The
abstract page at
https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.html carries the same
author, title and article number.

## Definitions

The article writes `F` for the Fibonacci numbers with `F(1) = F(2) = 1`, the
indexing used throughout its Section 6. Sequence A248982 is defined there as the
sequence of distinct least positive numbers such that the average of the first
`n` terms is a Fibonacci number; the article writes `(a_n)` for it, indexed from
one.

## The statement in question

Section 6 refines the closed-form conjecture recorded at A248982 to the assertion
that, for `n` at least ten,

> `a_n = nF(n/2 + 3) − (n − 1)F(n/2 + 2)` if `n` is even, and
> `a_n = F((n+1)/2 + 2)` otherwise.

It then states:

> A proof of this likely proceeds along similar lines as the previous theorem.
> Nevertheless, we were not able to show that the two sets
> `{ nF(n/2 + 3) − (n − 1)F(n/2 + 2) : n ≥ 1 is even }`,
> `{ F((n+1)/2 + 2) : n ≥ 1 is odd }`
> are disjoint, or, equivalently, that for every `n ∈ N`, the number
> `F(n + 2) + 2nF(n + 1)` is not a Fibonacci number. We conjecture that this is
> so. Notice that a similar sequence is the Les Marvin sequence
> `A007502(n) = F(n) + (n − 1)F(n − 1)`.

Both displayed sets are indexed by `n ≥ 1`, so the `N` of the equivalent form
starts at one. That is forced: at `n = 0` the number `F(2) + 0` equals one, which
is a Fibonacci number, while the two sets are unaffected.

## The equivalence recorded by the source

Writing the even index as `n = 2j` turns the first set into the values

`2jF(j + 3) − (2j − 1)F(j + 2) = 2j(F(j + 3) − F(j + 2)) + F(j + 2)
 = F(j + 2) + 2jF(j + 1)`,

which is the number named in the equivalent form. Writing the odd index as
`n = 2i − 1` turns the second set into `{F(i + 2) : i ≥ 1}`. Every value of the
first set is at least four, so it can equal a Fibonacci number only at an index
of at least five, and such an index lies in the second set; the disjointness of
the two sets and the equivalent form therefore say the same thing.

## Scope of the recorded answer

The recorded theorem `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result` proves
the equivalent form as stated: for every `n` at least one and every index `m`,
`F(m)` differs from `F(n + 2) + 2nF(n + 1)`. The closed-form assertion for
`(a_n)` itself is a different statement and is not settled here; disjointness of
the two sets is a necessary ingredient of it, not the whole of it.

## Bounded prior-resolution evidence

The only text claiming to settle this conjecture was arXiv:2509.26138 by Duc Hieu
Le, whose Theorem 23 and Proposition 24 addressed it. That preprint was withdrawn
by its author on 2025-11-06; the arXiv abstract page carries the comment "This
paper has been withdrawn by Duc Hieu Le" with the author's note that the proofs
in it were machine generated and some were found to be incorrect. A literature
pass opened the journal article and its abstract page, the withdrawn preprint and
its listing history, the OEIS entries A248982 and A007502, and the Fibonacci
literature on when a linear combination of consecutive Fibonacci numbers is again
a Fibonacci number. None of them records a proof of the conjecture. Major
citation-index result pages were not reachable, so this is a bounded negative
finding and no worldwide priority claim is made.
