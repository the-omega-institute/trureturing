---
bibkey: elder2024toggling
authors: Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch
year: 2024
title: "Toggling, rowmotion, and homomesy on interval-closed sets"
doi: 10.48550/arXiv.2307.08520
url: https://arxiv.org/abs/2307.08520v2
claim: "Conjecture 4.9 states that the number of maximal elements minus the number of minimal elements is 0-mesic under rowmotion on interval-closed sets of every product of two finite chains."
strata_touched:
  - D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy
  - D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation
license: citation-only
triage: anchor
---

# Toggling, rowmotion, and homomesy on interval-closed sets

The paper introduces interval-closed sets and their toggle rowmotion. Conjecture
4.9 states that, for every product of two finite chains, the number of maximal
members minus the number of minimal members is 0-mesic on every rowmotion orbit.
The repository target retains the literal interval-closed objects and resolves
this exact conjecture.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2307.08520
- URL: https://arxiv.org/abs/2307.08520v2
- Version and location: arXiv:2307.08520v2, Conjecture 4.9 (the conjecture is
  also identified in the paper's product-of-chains discussion).

## Signed cardinality

Conjecture 4.12 (p. 29) reads: “If m = 2 or m = 3, then the signed
cardinality statistic is 0-mesic under rowmotion on interval-closed sets of
[m]×[n] whenever m + n − 1 is even.”

Definition 3.17 (p. 21) reads: “Fix a finite poset P. For each x ∈ P,
define the signed cardinality statistic SC(x): P → {−1, 1} as follows:”
with SC(x) = 1 if rk(x) is even and −1 if rk(x) is odd. It continues:
“For an interval-closed set I, SC(I) = ∑_{x∈I} SC(x).”

Definition 2.6 (p. 4) defines t_x(I) = I − {x} if x ∈ I and
I − {x} ∈ IC(P), and t_x(I) = I otherwise; if x ∉ I it defines
t_x(I) = I ∪ {x} if I ∪ {x} ∈ IC(P), and t_x(I) = I otherwise.
Its final sentence is: “That is, x is toggled in/out of I if doing so
results in another interval-closed set.” Definition 2.9 (p. 5) reads:
“Given an interval-closed set I ∈ IC(P), the rowmotion of I, Row(I),
is given by applying all toggles in the reverse order of any linear extension.”

The signed-cardinality refutation uses the literal toggles and the distinct
forward orbit on [3]×[12]. The seed {(1,7),(3,2),(3,3),(3,4),(3,5)}
has a 73-state orbit with signed-cardinality sum −1. The separate
max-minus-min statistic and its all-rectangle result are different statements.
