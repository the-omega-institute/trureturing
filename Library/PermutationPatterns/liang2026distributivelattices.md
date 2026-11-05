---
bibkey: liang2026distributivelattices
authors: J. Liang and B. E. Sagan
year: 2026
title: Log-concavity and log-convexity via distributive lattices
doi: 10.1007/s11083-026-09735-2
url: https://arxiv.org/abs/2408.02782v2
claim: "Question 8.6(a) asks whether the middle order restricted to each ordered pinnacle class is a distributive lattice."
strata_touched:
  - D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result
license: citation-only
triage: anchor
---

# Ordered pinnacle classes and the middle order

## Verified locator

https://doi.org/10.1007/s11083-026-09735-2

https://arxiv.org/abs/2408.02782v2

Order 43 (2026), Article 21. arXiv:2408.02782v2, Section 6, “Permutations”, printed pages 17–18 (middle order on page 18),
and Section 8, printed pages 34–35 (Pin_n and Question 8.6).

## Source statements

Section 8, printed pages 34–35, Question 8.6 and its preceding definition:

> Let σ be a permutation of distinct positive integers. Let Pin_n(σ) = {π ∈ S_n | the pinnacles of π are the elements of σ in that order}. … Computation of examples raise the following questions.
> Question 8.6. For all n and σ:
> (a) Is the restriction of the middle order to Pin_n(σ) a distributive lattice?
> (b) Is the sequence (pin_n(σ)) log-concave?

Section 6, “Permutations”, printed pages 17–18, defines inversions and inversion tops:

> Given π = π1 π2 . . . πn ∈ Sn in one-line notation, its set of inversion (values) is Inv π = {(πi, πj) | i < j and πi > πj}.

> We also say that πi is an inversion top if (πi, πj) ∈ Inv π for some πj.

On printed page 18 the inversion coordinate and middle order are specified separately:

> where ιi = # of inversions in which i is an inversion top.

> We can now use the bijection just given to define the middle order (Sn, ⪯) by π ⪯ σ if and only if ι(π) ≤ ι(σ) where the order on inversion tables is component-wise.

Its example π=415632 has ι(π)=(0,0,1,3,2,2). Pinnacles are the values
π_j with π_{j−1}<π_j>π_{j+1}, listed from left to right.

## Mathematical correspondence

A permutation is `Equiv.Perm (Fin n)` and is read by positions in increasing
order. A value k in `Fin n` represents the paper's value k+1.
`pinnacleWord` filters the increasing position list by the two strict
neighbour comparisons and then reads the values. `iota` counts smaller
values whose inverse positions are larger; it is the inversion-top table,
not the number of smaller values to the left. `Pin` is the fibre of the
ordered word. Repeated pinnacle values are impossible. A source sequence
containing values outside [n] has an empty class and cannot be encoded as
a list of `Fin n`; the refutation uses distinct in-range values.

For every n≥6, the words A_n=1,n−2,2,n,3,4,…,n−3,n−1 and
B_n=n−1,1,n−2,2,n,3,4,…,n−3 have pinnacle word (n−2,n) and
have no common upper bound in that fibre. Question 8.6(b) is not addressed.
