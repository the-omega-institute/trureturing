---
bibkey: mccormackzelinsky2023weightedamgm
authors: Tim McCormack; Joshua Zelinsky
year: 2023
title: "Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function"
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
claim: "McCormack and Zelinsky ask in Question 43 whether the strongly pseudoperfect integers have positive natural density and in Question 44 whether strong pseudoperfectness is a strong restriction, a weak restriction, or neither within the Euler forms; Wang and Zelinsky repeat Question 43 as Question 22 and define a positive integer n to be strongly pseudoperfect when a subset S of its positive divisors is closed under d ↦ n/d and sums to 2n. Question 45 asks whether D1, the independent pseudoperfect condition together with an S1 satisfying A(S1,n) <= C(S1,n), is strong, weak, or neither."
strata_touched:
  - D5/S3/Arith/Abundancy/StrongPseudoperfectDensity
  - D5/S3/PrimeGaps/ChiFourWeightedMangoldt
  - D5/S3/PrimeGaps/ModFourChebyshev
  - D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity
  - D5/S3/Arith/Abundancy/WeightedTotientEulerDensity
license: citation-only
triage: anchor
---

# Strongly pseudoperfect integers and natural density

McCormack and Zelinsky, page 18, Question 43:

> Does SP have positive natural density?

Their preceding paragraph defines strongly pseudoperfect numbers using a divisor
sum set closed under complementary divisors. It distinguishes this condition
from requiring the set to contain both 1 and n.

Pages 18--19 define the counting function and Euler set:

> Given a set of natural numbers S, we will write S(x) as the number of elements in S which are at most x.
> Euler proved that if n is an odd perfect number, then n = q^s m^2 for some prime q, where q ≡ s ≡ 1 (mod 4), and where (q, m) = 1. Let E be the set of all numbers of that form.
> Given a statement S we will write E_S to be the set of elements of E which satisfy S.

The definition does not separately require m to be odd. The classification is:

> The second author defined a property S to be a weak property if
> lim_{x→∞} E_S(x)/E(x) = 1.
> Motivated by this, the second author said that S is a strong property if
> lim_{x→∞} E_S(x)/E(x) = 0.

These short quotations retain the source wording with superscripts, subscripts,
and the displayed fractions rendered in linear notation.
Page 19, Question 44 asks:

> Is being a strongly pseudoperfect number a strong restriction, a weak restriction, or neither?

Page 14, equations (12) and (14), define
A(S,n) = sum over d in S of (d/(2n)) log(phi(d)) and
C(S,n) = log(sum over d in S of phi(n/d)/(2d)).
The earlier definitions state:

> Given a positive integer n, when n is pseudoperfect, we will write S0 to be a subset of its positive proper divisors which sum to n.
> We will also write S1(n) to be a subset of all the divisors of n (possibly including n), and with the sum of S1 adding to 2n.

The S1 condition imposes no complementary-divisor closure. The D1 definition
retains the independent pseudoperfect requirement.
Page 19 states:

> Similarly, let D1 be the statement “n is pseudoperfect with some S1 where A(S1, n) ≤ C(S1, n).”
> Question 45. Is D1 a strong property, a weak property, or neither?

Wang and Zelinsky, *Strongly Pseudoperfect Numbers*, arXiv:2609.36068v3,
abstract, define a positive integer n to be strongly pseudoperfect if a subset S
of its positive divisors satisfies d ∈ S if and only if n/d ∈ S, and its sum is 2n.
Section 4, Question 22 asks whether this set has positive natural density.
Proposition 4 states that if p is prime and p > sigma(n), then pn is not
strongly pseudoperfect.

## Verified locator

- Locator: arXiv:2312.11661v4, S0/S1 definitions; page 14, equations (12)--(14); pages 18--19, E and strong/weak definitions; page 19, D1 and Question 45.
- DOI: 10.48550/arXiv.2312.11661
- URL: https://arxiv.org/abs/2312.11661v4
- Locator: arXiv:2312.11661v4, page 18, definition of strongly pseudoperfect and Question 43.
- Locator: arXiv:2312.11661v4, pages 18--19, Euler forms and weak/strong restrictions; page 19, Question 44; page 17, Proposition 37.
- URL: https://arxiv.org/abs/2609.36068v3
- Locator: arXiv:2609.36068v3, abstract, definition; Section 4, Question 22; Proposition 4.
