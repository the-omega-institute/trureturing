---
bibkey: mckean2025todaprimes
authors: Stephen McKean
year: 2025
title: Toda primes
doi: null
url: https://arxiv.org/abs/2511.19744v1
claim: "Definition 1.1 defines Toda primes; Notation 5.5 defines Bernoulli-denominator prime sets and first indices; Conjecture 5.6 asserts denominator-based invariance and monotonicity."
strata_touched:
  - D5/S3/Arith/McKeanTodaPrimes/Result
license: citation-only
triage: anchor
---

# Toda primes and Bernoulli denominators

## Verified locator

https://arxiv.org/abs/2511.19744v1

Stephen McKean, *Toda primes*, arXiv:2511.19744v1.
The locators below use printed page numbers.
Mathematical typography is transcribed from the supplied PDF text.

Definition 1.1, §1, printed p. 1:

> Definition 1.1. Let n be an integer. A Toda prime of n is an odd prime p such that
> p − 1 | 4n and gcd(p, 4n/(p−1)) = 1. Denote the set of Toda primes of n by T (n) (see Table 1),
> and let t(n) := |T (n)| (see Figure 1).

Notation 5.5, §5.1, printed p. 8:

> Notation 5.5. Given an even integer 2m, let P (2m) denote the set of primes such that
> p − 1 | 2m, so that D₂ₘ = ∏ₚ∈P(2m) p. Let F (d) = min{2m > 0 : D₂ₘ = d} [PW23].

Conjecture 5.6, §5.1, printed p. 8:

> Conjecture 5.6. Let d be a Bernoulli denominator.
> (i) If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ.
> (ii) If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).

The formal reading uses positive natural a and m, Mathlib's rational Bernoulli
numbers, and their reduced positive denominators. The first-index hypothesis
is expressed by exclusion of every smaller positive even index with the same
denominator. Equality of that denominator at index 4a is implicit in its
being `bernDen (4*a)`.
