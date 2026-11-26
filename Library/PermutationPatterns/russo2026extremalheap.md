---
bibkey: russo2026extremalheap
authors: Luís M. S. Russo
year: 2026
title: Heap-type permutation generation with a prescribed final arrangement
doi: 10.48550/arXiv.2611.22780
url: https://arxiv.org/abs/2611.22780v1
claim: Definition 22 gives the extremal Heap schedule. Section 10 item 1 asks for its correctness in the class n congruent to 2 modulo 4.
strata_touched:
  - D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep
  - D5/S3/Combinatorics/Permutation/RussoExtremalHeap
license: citation-only
triage: anchor
---

# Russo's extremal Heap sweep

## Verified locator

See the [version 1 abstract](https://arxiv.org/abs/2611.22780v1)
([DOI 10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780)).
[Version 1, 17 November 2026](https://arxiv.org/pdf/2611.22780v1).
SHA-256 of the consulted PDF is
`ccebe09b956ed3cf6bf7fb29096287a3dbcf86931e0fe3b6826007e2e011bbef`.

- Section 2.5 gives right-to-left composition. Section 3.1 specifies the ordered
  calls and the physical swaps. Definition 3 specifies the cyclic schedule.
- Section 6, Theorem 18(a)–(b), recovers each swap partner from the prescribed
  parked item and computes the net as the power of the lower net times the
  parking cycle.
- Section 7.2, Definition 22 and Theorem 23 on printed pages 16–17, specify the
  two top schedules, the separate cyclic/classic branch for size two, and the
  conditional conclusion from the quotient being a full cycle.
- Section 9 records a bounded check of the orbit criterion through 10000.
  Section 10 item 1, printed page 20, gives the open residue-two case.

## Statement

> The correctness of the extremal variant is proved for n ≡ 0 (mod 4) and verified by computer for all even n ≤ 10000; a proof for n ≡ 2 (mod 4) (the orbit structure of Zₙ) is open.

For sizes at least six in the residue-two class, Definition 22 specifies the
penultimate parking order $1,\ldots,m,2m,\ldots,m+1$ with $m=(n-2)/2$. If $U$
is the actual net of that penultimate sweep, extended to fix position $n$,
and $T$ is reversal, the top order follows the cycle of $Z_n=U^{-n}T$
starting at position $n$.

## Mathematical scope

The formalization uses zero-based positions. Its schedule is a list of
physical swaps in recursive call order. The scan emits the initial state and
every post-swap state. Array entries are obtained by inverting each state. In
the residue-two class the top order runs through the entire carrier, and the
ordered sweep emits each permutation once with terminal array the reversal.

The quotient proof uses the first-return map on the support of $U$. Its
cycle-coordinate map is addition by two after the transposition of the first
two coordinates, joining the two alternating cycles. Every point off the
support occurs in a two-step return. This argument treats the residue-two
class for $n\ge6$. The size-two branch is explicit.

The source comparison covers the pinned version and the related Heap-order
paper and author software identified in the preregistration.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/32907)

Completeness of the external literature screen is ASSUMED-UNVERIFIED.
