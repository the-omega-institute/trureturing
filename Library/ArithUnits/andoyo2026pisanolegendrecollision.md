---
bibkey: andoyo2026pisanolegendrecollision
authors: Jason D. Andoyo
year: 2026
title: "(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes"
doi: 10.62072/acm.2026.09011
url: https://arxiv.org/html/2601.10561v1
claim: "Section 5, Question 5.3 asks whether distinct nonzero integer seed pairs can have equal complete Pisano sets."
strata_touched:
  - D5/S3/Arith/AndoyoPisanoSetCollision
license: citation-only
triage: anchor
---

## Verified locator

- DOI: https://doi.org/10.62072/acm.2026.09011
- Versioned preprint: https://arxiv.org/html/2601.10561v1
- Journal text: https://www.technoskypub.com/wp-content/uploads/2026/04/acm-090111.pdf

Both texts contain Definitions 2.6 and 2.7 and Section 5, Question 5.3.
The journal identifies the article as Annals of Communications in Mathematics
9 (2026), article 11.

## Source statements

Definition 2.6 takes the initial values F₀=a and F₁=b and defines the
Pisano period as the smallest positive k with Fₙ₊ₖ≡Fₙ modulo the modulus
for every n. Definition 2.7 counts indices in {0,…,πₚ(a,b)−1} separately
for Legendre values 1, −1 and 0. The integer difference is the first count
minus the second and third. The Pisano set contains these differences over
all odd primes.

The paragraph immediately preceding Question 5.3 requires integer seeds,
distinct ordered pairs, and each pair different from (0,0). The question is:

> Are there values of a₁, a₂, b₁, and b₂ for which χ(a₁,b₁)=χ(a₂,b₂)?

There is no positivity, coprimality or identification of shifted pairs in
these hypotheses. The pairs (0,1) and (1,1) therefore meet the stated domain.

## Interpretation and boundary

Equality modulo p is represented by equality of integer casts in ZMod p.
Counts are over indices, so repeated residues retain their multiplicity.
The three counts are cast to integers before subtraction. The formal
collision uses the complete prime-indexed sets; no finite-prime sample
enters the argument.
