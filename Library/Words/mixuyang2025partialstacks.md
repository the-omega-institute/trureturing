---
bibkey: mixuyang2025partialstacks
authors: Jared Mi; Jeffrey Xu; Jason Yang
year: 2025
title: "Partially Restricted Stacks as Functions"
doi: 10.54550/ECA2025V5S3R22
url: https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf
claim: "Conjecture 5.2 states that pi takes 2n-5 sorts under s composed with t exactly when pi = 2 sigma 1 n and sigma avoids 213."
strata_touched:
  - D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation
license: citation-only
triage: anchor
---

# Partially restricted stacks as functions

On printed page 1 the paper defines West's map and its partially restricted
generalization:

> The map sends permutations through a stack that always avoids the permutation
> 21 when read from top to bottom.

> We further generalize s to s_{(T,k)}. We define the maps s_{(T,k)} that avoid
> containing more than k distinct permutations from T in the stack at once.
> More specifically, the map sorts a permutation π via the following stack
> sorting algorithm: If adding the leftmost element of the input to the stack
> keeps the stack (T, k)-avoiding, push that element into the stack. Otherwise,
> pop the top element off the stack and append it to the output.

On printed page 2 the paper states:

> Given two permutations π and σ, we say π contains σ if there exist
> a_1, a_2, . . . , a_k such that the sub-permutation
> π_{a_1} π_{a_2} . . . π_{a_k} is order-isomorphic to σ. Otherwise, we say π
> avoids σ.

> Furthermore, for a set T of permutations and a nonnegative integer k, we say
> π is (T, k)-avoiding if π contains at most k elements of T.

> Throughout the paper, we use t to denote s_{({12,21},1)}.

On printed page 6 the paper defines the sorting time:

> Let m_{(s∘t)}(π) be the smallest nonnegative integer j such that
> (s ∘ t)^j(π) = id_{|π|}.

On printed page 7 it states:

> Conjecture 5.2. The permutation π takes 2n − 5 sorts to be sorted to the
> identity by (s ∘ t) if and only if π = 2σ1n and σ ∈ Av_{n−3}(213).

The displayed Conjecture 5.2 follows Lemma 5.5, whose stated range is `n >= 3`.
The notation `pi = 2 sigma 1 n` has first entry 2, final entries 1 and n, and
middle word sigma on the entries from 3 through n-1.

## Verified locator

- DOI: 10.54550/ECA2025V5S3R22
- URL: https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf
- Printed pages checked: 1, 2, 6, and 7.
