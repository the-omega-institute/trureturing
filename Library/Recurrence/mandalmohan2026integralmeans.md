---
bibkey: mandalmohan2026integralmeans
authors: Sagar Mandal and Mohan
year: 2026
title: "Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure"
doi: 10.48550/arXiv.2611.32519
url: https://arxiv.org/html/2611.32519v1#S1.Thmtheorem19
claim: "Conjecture 1.19 says the quotient of n to the k-th power by the sum of the first n reciprocal Fibonacci k-th powers is integral exactly at n = 1 and n = 2 for k at least three."
strata_touched:
  - D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean
license: citation-only
triage: anchor
---

# Mandal and Mohan on integral means of Fibonacci numbers

## Verified locator

Sagar Mandal and Mohan, *Integral Means of Fibonacci Numbers: Divisibility,
Density, and Arithmetic Structure*, arXiv:2611.32519v1 (24 November 2026),
Conjecture 1.19. [Versioned source](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem19)
[DOI](https://doi.org/10.48550/arXiv.2611.32519)

## Statement and indexing

The conjecture states that for $k \geq 3$, the expression
$\frac{n^k}{1/F_1^k + \cdots + 1/F_n^k}$ belongs to $\mathbb N$ if and only if
$n=1,2$. The denominator runs over a nonempty prefix of the ordinary
Fibonacci sequence with $F_1=F_2=1$. The Lean statement takes the quotient
in $\mathbb Q$ and tests equality to a natural-number cast.

Theorem 1.18 of the same version classifies $k=1$ at $n=1,2$ and $k=2$
at $n=1,2,3$. The authors discuss the limitations of their 2-adic
argument just before stating Conjecture 1.19.
[Theorem 1.18](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem18)
