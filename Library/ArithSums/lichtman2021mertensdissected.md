---
bibkey: lichtman2021mertensdissected
authors: Jared Duker Lichtman
year: 2021
title: "Mertens' prime product formula, dissected"
doi: null
url: https://arxiv.org/abs/2002.03361v3
claim: The existing fixed-k integer-count asymptotic following Theorem 1.3 supplies the counting input for the project's squarefree odd-kernel cuts; it does not supply a signed FIB remainder estimate or RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-complexity counting and the actual Fibonacci cut

The primary is [arXiv:2002.03361v3](https://arxiv.org/html/2002.03361v3),
version 16 March 2021. The arXiv metadata gives *Integers* **21A** (2021),
Ron Graham Memorial Volume, #A17, 15 pages. The inspected HTML SHA-256 is
`30ba505256e7130ad4071c5255f3f80955e8b681cf55377c1c7333b22fe07282`;
this identifies the inspected HTML, not a journal-PDF byte identity.
The source's §1 discussion surrounding Theorem 1.3 was inspected. The
books cited there were not independently inspected, and no Lean
verification or exhaustive prior-art certification is claimed.

## Use the integer count, not the reciprocal sum

Write $\Omega(n)$ for the number of prime factors counted with multiplicity.
The unnumbered display immediately following Theorem 1.3 gives

$$
\#\{n\le x:\Omega(n)=k\}
=\nu(r)\frac{x}{\log x}
\frac{(\log\log x)^{k-1}}{(k-1)!}
\left(1+O_\varepsilon\!\left(\frac{k}{\log\log x}\right)\right),
\qquad r=\frac{k}{\log\log x},
$$

in its stated range $r\le2-\varepsilon$. Here

$$
\nu(z)=\frac1{\Gamma(z+1)}
\prod_p(1-z/p)^{-1}(1-1/p)^z.
$$

For each fixed positive integer $k$, $r\to0$ and $\nu(r)\to\nu(0)=1$.
Thus the classical Landau fixed-$k$ count and a fixed-$k$ upper bound
are directly available. Theorem 1.3 itself and equation (1.8) concern
$\sum1/n$; those quantities are not substituted for the integer count.
The source cites Montgomery–Vaughan, Theorem 7.19, and Tenenbaum,
Theorem 6.5, for the count. Their proofs are reused rather than reproduced.
No new uniform Hardy–Ramanujan or Sathe–Selberg theorem is asserted.

## The project-specific correspondence

For the [actual FIB prefix, §422](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
the counted objects are odd squarefree kernels with $k$ distinct prime
factors. Removing repeated factors and the prime 2 changes only lower
orders for fixed $k$. The section pays this restriction by applying the
quoted count to the smaller factor counts, retaining the $k=1,2$ cases.
The divisor corrections in the FIB endpoint are then controlled by
separating finitely many small primes, and all growing dyadic bands are
bounded before their limits are combined.

The resulting FIB layer has leading coefficient
$(-1)^k b_q/(k-1)!$, with $b_q=-c_q>0$ taken directly from the existing
§421 coefficient certificate. The leading scale is
$x(\log\log x)^{k-1}/\log x$. No new prime counting, logarithm program,
coefficient computation, or old CA comparison is performed.

For a fixed finite squarefree-kernel truncation, the omitted part of the
same actual prefix must compensate its highest retained layer at that
same scale. This identifies the cost of discarding that complement;
it does not estimate the full signed remainder at the RH scale, cover
Robin host integers, or forbid retaining more information in the FIB
recursive representation. Fixed-$k$ asymptotics are not uniform
statements for a growing $k=k(x)$, and cannot be alternately summed to
obtain a full-array conclusion. The cited paper's uniform counting range
does not by itself supply the missing uniform signed FIB comparison.
