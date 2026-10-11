---
bibkey: elima2022robin
authors: Emmanuel Elima
year: 2022
title: On Robin's inequality for positive integers and related bounds
doi: null
url: https://easychair.org/publications/preprint/xW8q
claim: Robin's inequality holds for every integer above 5040 with at most twelve distinct prime divisors, by reduction to 21-full integers.
strata_touched: []
license: citation-only
triage: anchor
---

# On Robin's inequality for positive integers and related bounds

It is a preprint; this card records the stated interfaces and does not audit the proofs.

Write $\omega(n)=k$ for the number of distinct prime divisors of $n$.

- Lemma 1.4 states that $\sigma(n)<e^\gamma n\log\log n$ holds whenever $k\le12$.
  Its proof assumes $n$ is 21-full, using the 21-free case of Axler's theorem, so that some
  prime $q$ has $q^{21}\mid n$ and $n\ge2^{21}\prod_{i=2}^{k}p_i$. It then checks
  $\prod_{i\le k}p_i/(p_i-1)<e^\gamma\log\log\bigl(2^{21}\prod_{i=2}^{k}p_i\bigr)$
  for $k\le12$ by calculation.
- Theorem 1.2 states the inequality for every $t$-full $n$ with
  $t>0.44k\log(k\log k)+0.49k+1$.
- Theorem 1.3 states it for every $n$ with $\log p_k\,(1+1/\log^2p_k)<\log\log n$, where
  $p_k$ is the $k$-th prime.

The bounded-$\omega$ statement therefore rests on the cited 21-free theorem and on the
author's calculation; neither is a Lean verification.

## Verified locator

- URL: https://easychair.org/publications/preprint/xW8q
- Version and location: EasyChair Preprint No. 9446, dated 11 December 2022; Lemma 1.4,
  Theorem 1.2 and Theorem 1.3.
