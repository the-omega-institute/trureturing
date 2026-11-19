---
slug: oeis-a094373-ianakiev-shortest-ruler-palindrome
bibkey: ianakiev2019a094373
doi: null
url: https://oeis.org/A094373
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result
---

# Ianakiev's shortest-palindrome first occurrences

## Problem

Ivan N. Ianakiev's complete A094373 COMMENTS conjecture, attributed to
Aug 20 2019, reads:

> Take A007843 and count the repeated values. The result is 1,1,2,1,3,1,2,1,4,1,2,1,3,1,2,1,5,.... Build a third sequence, where a(1) = 1 and a(n) equals the length (greater than 1) of the shortest palindromic subsequence of consecutive terms of the second sequence starting with a(n) of the second sequence. The third sequence starts 1,3,5,3,9,3,5,3,17,3,5,3,9,3,5,3,33,.... Conjecturally, in the third sequence: (1) the indices of the first occurrence of each value form the present sequence and (2) for n>1, a(n) is in the a(n-1)-th position. - _Ivan N. Ianakiev_, Aug 20 2019

Let F(m) be the least positive h such that 2^m divides h!, for every
natural m. Let S(0)=0, and let S(r+1) be the least m>S(r) with
F(m) different from F(S(r)). For i>=1, put B(i)=S(i)-S(i-1).
For i>=2, P(i) is the least L>=2 such that B(i+t)=B(i+L-1-t) for
every t<L. Set P(1)=1 as the source stipulates. The independent sequence
A is A(0)=1 and A(e+1)=2^e+1.

The full conclusion is that all these minima exist, A is strictly
increasing, and for every i>=1 the value P(i) appears for the first time
at i if and only if i=A(m) for some natural m. In addition, for every
m>=2, P(A(m-1))=A(m). The first clause concerns the entire increasing
list, rather than just membership of some first-occurrence positions.

The preceding Jackson formula and the displayed prefix disambiguate
clause (2): its two a's denote A094373, and its position is in P.
In particular, m=2 gives P(2)=3. Applying that identity at m=1, or
minimizing lengths greater than one at i=1, changes the source assertion.
The word "consecutive" excludes scattered subsequences. Index zero of
B and P has no source interpretation.

## Motivation

This Tier 1 question connects inverse factorial divisibility, maximal
constant runs, and the location-dependent minimum length of a contiguous
palindrome. Its 2019 attribution and the inspected later snapshots retain
the named conjecture. The complete two-clause event was registered before
the Lean probe in [issue #30104](https://github.com/the-omega-institute/trureturing/issues/30104).

## Gap

The checked A094373 revisions and immutable oeis/oeisdata exports retain
the conjecture. No exact settlement or event owner was found in the
checked D5 public/private declarations, canonical Scribe material,
Problems, pinned Mathlib, selected public Lean sources, GitHub issues and
PRs including closed items, or the relevant retrieved literature.

Kullmann–Zhao, arXiv:1505.02318v2, Lemma 3.11 and Example 3.7, already
identify the positive factorial plateau lengths with the ruler sequence;
their zero convention differs from the least-positive F(0)=1 convention.
Li's arXiv:2007.08317v1 concerns prefix factorization into palindromes,
which is a different minimum. The accessible precursor of Nuño–Muñoz's
*The Ruler Sequence Revisited* supplies classical ruler background.
These are related results, rather than an exact two-clause supplier in
the material inspected. Bounded absence is not a worldwide priority claim.

## Route

The compiled proof starts with the literal factorial-divisibility
minimum. It proves F(m)<=h if and only if m<=v2(h!) for positive h.
Every next boundary is v2(F(a)!)+1. Induction gives
S(r+1)=v2((2r)!)+1 and F(S(r+1))=2(r+1). The factorial successor
identity therefore gives B(1)=1 and B(r+1)=1+v2(r) for r>=1.
The ruler formula is a proved bridge from the actual runs.

For i>=2 write j=i-1, k=v2(j), and q=2^k. Equal endpoint B-values
force equal valuations, so the endpoints' odd quotients differ by at
least two. Thus every admissible palindrome has length at least 2q+1.
The center c=j+q is divisible by 2^(k+1). For 0<s<=q the valuation
of s is at most k, so unequal-valuation addition gives
v2(c-s)=v2(c+s). The resulting full reflected interval attains the
bound. Hence P(i)=2^(v2(i-1)+1)+1 follows from the literal minimum.

The least positive j of valuation k is 2^k. Consequently the complete
first-occurrence list is 1, followed by 2^k+1 for k>=0. Substitution
at i=A(m-1) proves the second clause for every m>=2.

## Falsifier

A missing minimum at any exponent, run, or positive source position;
an admissible palindrome shorter than the proved lower bound; a failure
of the reflected interval; a first occurrence outside A; a non-first
occurrence at A; or a failed position identity at any m>=2 would
contradict the corresponding conjunct of `claim`. Neither a finite
prefix nor the ruler bridge alone establishes the complete assertion.

## Evidence

The closed theorem is `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result`.
Its source includes the definitions F, S, B, Pal, P, A, First and the
complete closed `claim`. Consumed private lemmas establish the literal
boundary bridge, endpoint lower bound, reflection attainment, derived
minimum formula, and both source conclusions.

The corresponding typed Scribe states all the construction and
quantifier conventions. The Reg mirror observes the factorial-index
function inside the complete assertion, with a full equivalence bridge,
whole-function variation, sensitivity, and actual dependence. Its
source-bound escape audit remains unfinished under the linked-issue
exception in [issue #30128](https://github.com/the-omega-institute/trureturing/issues/30128).
The compiled registration supplies proof data, without an accepted binding
certificate or a claim of audit completion.

## Triage

`theorem`: the single complete two-clause event is the resolution target.

### What the settlement shows

Proved by `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result`:
both source clauses hold for the literal factorial runs and the stated
positive-index convention. The sharp bound comes from spacing of odd quotients after extracting
the common dyadic factor, and it is attained by reflection about a
center of strictly larger valuation. The consumed `p_formula` proves
the exact minimum P(i)=2^(v2(i-1)+1)+1 for every i>=2, so every lower
bound in this argument is attained. All later P-values are at least
three, separating the stipulated initial first occurrence. These are
consequences of this same proof, not additional external settlements.

The positive plateau identification and the elementary valuation laws
are classical support and earn no separate open-problem credit. A
different prime, a different zero convention, or a different palindrome
statistic would require a separate statement and proof. No such extension
is asserted here. No additional dependent conjecture is settled by the
inspected source comment; its two conjectural clauses are now consequences
of the theorem. Other primes, conventions and palindrome statistics remain
outside this statement and are not claimed as extensions.

## ASSUMED-UNVERIFIED

Worldwide absence of an earlier answer remains unverified. The original
2019 history endpoint and the 2024 publisher body were inaccessible.
MathDB returned 403, OpenAlex 429, and several web-search providers
challenged or rate-limited requests. Broad public code search was bounded;
its Lean language filter missed a synthetic A094373 definition found by
the broader search. That definition gives A alone, not this event.
No author clarification was obtained; the contextual source reading is
stated explicitly above. These limits preclude an exhaustive priority
or global-openness claim.
