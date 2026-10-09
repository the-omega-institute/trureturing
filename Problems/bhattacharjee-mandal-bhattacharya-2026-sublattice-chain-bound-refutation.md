---
slug: bhattacharjee-mandal-bhattacharya-2026-sublattice-chain-bound-refutation
bibkey: bhattacharjee2026sublattice
doi: 10.48550/arXiv.2610.02833
url: https://arxiv.org/abs/2610.02833v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result
---

# The ceiling formula for monochromatic sublattices is false

## Problem

Bhattacharjee–Mandal–Bhattacharya, arXiv:2610.02833v1, Question 9.3:

> Is f(n) = O(n)? Is f(n) = ⌈(n + 1)/2⌉ for every n?

Section 1 specifies:

> a k-colouring of 2^[n] is a map χ : 2^[n] → [k], and a family ℱ ⊆ 2^[n] is monochromatic if χ is constant on ℱ. … it is a sublattice if it is closed under both union and intersection. … f(n) = min_χ max{|ℒ| : ℒ ⊆ 2^[n] is a monochromatic sublattice}, where the minimum is over all 2-colourings.

Sublattices here are nonempty. The Lean definition uses finite families of
subsets of `Fin n`, constant Bool colour, and closure under both union and
intersection. The extremal function is literally a minimum over all colourings
of the maximum cardinality of such a family. The universal `claim` concerns
only the second question, using `(n + 2) / 2` for the ceiling.

## Motivation

The Erdős #1183 problem page records the trivial bound
f(n) ≥ ⌈(n+1)/2⌉, obtained by taking a colour class in a maximal chain.
For every odd n ≥ 11 the bound below increases that guarantee by one.
The proposed equality therefore fails in an entire unbounded family of
dimensions, while the separate question of linear growth remains open.

## Gap

The chain argument gives f(n) ≥ ⌈(n+1)/2⌉ for every n; the Erdős Problems page for #1183 records this bound as the only known lower bound and quotes Erdős ([Er78]): "we have no plausible conjecture for the true order of magnitude of f(n)". Upper bounds of order n(log n)² are due to Chojecki (2026 preprint, Theorem 1.3: f(n) ≤ (3+o(1)) n log₂² n, with lower bound ⌈(n+1)/2⌉) and to Bhattacharjee–Mandal–Bhattacharya (arXiv:2610.02833v1, Theorem 1.4), whose Question 9.3 asks whether f(n) = O(n) and whether f(n) = ⌈(n+1)/2⌉ for every n. The forum thread for #1183 (eleven comments, one proof claim, which concerns F(n) and the asymptotic bounds above) contains no lower bound for f exceeding the chain bound; MathDB searches by title words and authors return no entry for the question.

## Route

Let n be odd and m=(n+1)/2. Suppose no monochromatic sublattice has more
than m members. Every maximal chain has n+1=2m members, and each colour
class within it is a sublattice, so each colour occurs exactly m times.
Two maximal chains differing only at rank r force their distinct r-sets
to have the same colour. Single-element exchanges connect equal-sized
subsets: induction on |A \ B| proves that colour depends only on rank.
Thus the n+1 ranks form a balanced Boolean word.

If one colour has three consecutive occurrences a<b<c with a+c=2b,
write P_r for the first r points and add
X=P_a ∪ {b,…,c−1} to all that colour's prefix subsets. The new member
has rank b, intersects P_b in P_a and unites with P_b to give P_c.
It is comparable with the remaining selected prefixes. This gives a
monochromatic sublattice with m+1 members.

Otherwise the word excludes 000, 111, 01010, 10101, 0110110 and 1001001.
A prefix-extension computation shows that an avoiding word without a
balanced twelve-position window cannot have length fifteen. At length
fourteen the remaining words are unbalanced; length twelve is itself a
balanced window. Hence the balanced rank word has twelve consecutive
ranks with six of each colour.

For a balanced colouring of ranks 0,…,11, enumerate the 924 patterns
by filtering the 4096 twelve-bit words for weight six. In 874 patterns
one colour has the stated consecutive arithmetic progression. Each of
the remaining fifty is covered by one of these ten families:

```
(0,7,56,63,448,455,504,511)
(3,31,227,255,1795,1823,2019,2047)
(1,15,113,127,897,911,1009,1023)
(0,1,30,31,480,481,510,511)
(0,7,120,127,1920,1927,2040,2047)
(0,7,56,63,1984,1991,2040,2047)
(0,3,7,63,963,967,1023)
(1,7,15,127,1927,1935,2047)
(0,3,31,127,899,927,1023)
(1,3,31,481,483,511,2047)
```

Bit i represents element i. The families have seven or eight distinct
members and are closed under bitwise union and intersection. Decoding
preserves the operations and cardinality. Embed the resulting sublattice
in the balanced rank interval b,…,b+11 by
A ↦ P_b ∪ {b+i : i∈A}. Adjoin the same-coloured prefixes outside the
interval. They are comparable with every embedded member, and their
ranks ensure disjointness from the embedded family. The total number
of members is at least m+1.

## Falsifier

The argument would fail if the exchange chains did not differ at exactly
one rank, an equal-size exchange did not reduce |A \ B|, an excluded
subword did not yield consecutive arithmetic-progression occurrences,
the extension recurrence omitted an admissible word, or a finite
pattern was uncovered. The diamond's closure and extra cardinality,
the interval embedding's operation preservation and disjoint counting,
and the literal minimum-over-colourings definition of f are essential.

## Evidence

[proved: Lean] `D5.S3.Combinatorics.ErdosUlam.SublatticeChainBound.odd_lower_bound` proves

$$
  \forall n\in\mathbb N,\qquad
  (11\le n\ \wedge\ n\text{ odd})\ \Longrightarrow
  f(n)\ge \frac{n+3}{2}.
$$

The definition of f is the minimum over all Boolean colourings of the
largest cardinality of a nonempty union- and intersection-closed
monochromatic family. `result : ¬ claim` uses the odd lower bound at
n=11. The four modules contain definitions, general rank rigidity, general
constructions, and the refutation. The refuting module contains the rank-word
alternative, the eleven-dimensional base, and the extremal-function conclusion. Finite certificates use
kernel reduction of `decide`; no native evaluation, new axiom or
incomplete proof is used. Every module is checked with Lean 4.33.0.

## Triage

- [proved: Lean `odd_lower_bound`] For every odd n ≥ 11, f(n) ≥ (n+3)/2.
  In particular f(11) ≥ 7, improving the chain bound recorded on the Erdős
  problem page.
- [proved: Lean `result`] The proposed equality for every n is false: at
  n=11 the lower bound seven exceeds the proposed value six.
- [computed: exact enumeration, not formalized] f(9)=5. Exactly six
  balanced rank colourings of 0,…,9 avoid a six-member monochromatic
  sublattice up to colour swap; one has true ranks {0,1,3,6,7}.
  Together with the smaller odd dimensions, eleven is the least odd
  counterexample to the proposed formula.
- [computed: exact rank enumeration] Of the 924 balanced twelve-rank
  patterns, 874 admit the diamond, and the remaining fifty are covered
  by the ten displayed families. Their operation closure and distinct
  cardinalities are also checked in Lean.
- [open] Determine the exact values of f(n) for even n.
- [open] Determine whether the odd-dimensional lower bound is sharp,
  including whether f(11)=7.
- [open] Decide whether f(n)=O(n), the separate first part of Question 9.3.

## ASSUMED-UNVERIFIED

Forward citations of arXiv:2610.02833 were screened by web search only. The scanned 2026 preprint of Tang and coauthors linked from the forum is an image file and was not read; the forum states that its results coincide with Chojecki's.
