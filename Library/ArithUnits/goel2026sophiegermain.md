---
bibkey: goel2026sophiegermain
authors: Aradhya Goel
year: 2026
title: "Sophie Germain Primes and the Totient of Fibonacci Numbers"
doi: null
url: https://arxiv.org/abs/2604.17847v3
claim: 'OQ4 asks whether the prime-domain values of π(q)/z(2q+1) are exactly the odd integers.'
strata_touched:
  - D5/S3/Arith/GoelPisanoRatioRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2604.17847v3

Version 3, 22 April 2026. The definitions are in the Introduction, p. 1.
Section 10, OQ4 is on p. 10; Theorem 6.2 and Lemma 6.3 are on p. 7;
Theorem 7.1 is on p. 8. These locators are verified against the versioned PDF
and its TeX source.

## Source statements

“For a prime p, the rank of apparition z(p) is the smallest positive integer k with p | Fₖ;
it is well-defined for every prime p [3, 7]. The Pisano period π(n) is the period of
(Fₘ mod n).” (p. 1).

“OQ4. Values of π(q)/z(2q + 1). Is {π(q)/z(2q + 1) : q > 5 with z(2q + 1) | π(q)}
= {odd integers}?” (Section 10, p. 10).

The corresponding source line is:

```tex
\item[OQ4.] \textbf{Values of $\pi(q)/z(2q+1)$.} Is $\{\pi(q)/z(2q+1) : q > 5 \text{ with } z(2q+1) \mid \pi(q)\} = \{\text{odd integers}\}$?
```

Lemma 6.3 states: “Let q > 5 be a Sophie Germain prime with z(2q+1) | π(q).
Then (5/q) = −1 and π(q) | 2(q + 1).” The parentheses (5/q) denote the Legendre
symbol. Theorem 6.2 states that the eligible quotient is odd; Theorem 7.1 states
that q ≡ 8 (mod 15), under the same hypotheses.

## Interpretation and boundary

The source defines z at primes and treats q as an odd prime. Thus OQ4 uses
Sophie Germain primes q > 5 with z(2q+1) dividing π(q). Every quotient is positive,
so “odd integers” is read as positive odd integers. Reading it as all odd integers
also fails because negative values cannot occur.

The refutation combines the prime Fibonacci rank and period bounds to exclude
every multiple of five. It answers OQ4 in the negative; it does not challenge
Theorems 6.2 or 7.1. Whether the values are exactly the positive odd integers
coprime to five remains open.
