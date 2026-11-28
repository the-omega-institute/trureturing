---
bibkey: dimitrovlazarova2026part4c2
authors: Stoyan Dimitrov and Meglena Lazarova
year: 2026
title: "Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4"
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
claim: "Section 4 states positive-power quotient bounds for all n ≥ 2 and k ≥ 1, including the cubic quotient in Conjecture 1 and the pairwise cubic quotient in Conjecture 2."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovPartFourC1
  - D5/S3/Arith/Divisors/DimitrovPartIVC2
license: CC-BY-4.0
triage: anchor
---

# Part 4, Conjecture 2

## Verified locator

DOI: https://doi.org/10.3390/math14213935.
The [publisher PDF](https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf)
is *Mathematics* **14**(21), 3935, 14 pages, 3219707 bytes,
SHA-256 `21c972599612cd12ac9354219cc73daa316fcdaff7548ed9be3ee381632a0d3a`.
Definitions are in Section 1, pages 1–2; Conjecture 2 is in Section 4, page 13.
The article credits Dimitrov and Lazarova and is distributed under CC BY 4.0.

## Exact statement and function correspondence

For every natural $n\geq2$ and $k\geq1$,

$$
\frac{\varphi(n)^{3k}\psi(n)^{3k}+\psi(n)^{3k}\sigma(n)^{3k}
+\varphi(n)^{3k}\sigma(n)^{3k}}
{\varphi(n)^{2k}\psi(n)^{2k}\sigma(n)^{2k}}
\geq\frac{2(n^2-1)^{3k}+(n+1)^{6k}}{(n-1)^{2k}(n+1)^{4k}}.
$$

All quotients and subtractions are real. Euler's totient is `Nat.totient`.
The existing `OeisA344695GcdSigmaPsiPrimes.psi_prod` identifies `psi n` with
$\prod_{p\mid n}p^{v_p(n)-1}(p+1)$ for nonzero $n$.
`ArithmeticFunction.sigma_one_apply` identifies `ArithmeticFunction.sigma 1 n`
with the sum of positive divisors. No prime, squarefree or finite-range
restriction is imposed. Source Theorem 2 gives only the case $k=1$.

## Application

Set $x=(\psi(n)/\varphi(n))^k$, $y=(\sigma(n)/\varphi(n))^k$ and
$r=((n+1)/(n-1))^k$. The existing arithmetic bounds give $1\leq r\leq x\leq y$.
Writing $F=xy+x/y^2+y/x^2$, exact identities give

$$
F-x^2-\frac2x=
\frac{(y-x)((x^3-1)y^2+(y-x)(2y+x))}{x^2y^2}\geq0,
$$

$$
x^2+\frac2x-r^2-\frac2r=
\frac{(x-r)((x+r)xr-2)}{xr}\geq0.
$$

The source left side equals $F$ and the source right side equals $r^2+2/r$.
The factorization argument is a repository derivation; no novelty claim is made
for this elementary analytic inequality. Arithmetic bounds are imported directly
from `DimitrovLowerBoundsC4C5`, whose existing supplier attribution and
[license account](dimitrov2026c4c5.md) remain applicable. No supplier code is copied.

## Literature boundary

The source calls the full power-family statement a conjecture. The bounded
current-status qualification recorded in
[#30596](https://github.com/the-omega-institute/trureturing/issues/30596#issuecomment-6886094407)
identified no complete prior settlement in its inspected scope. Blocked,
unindexed and worldwide priority surfaces remain unverified. Related pairwise
numerator inequalities and the source's exponent-one theorem do not themselves
settle this quotient. The inspected Lean supplier at
`pro20541/dimitrov-conjectures-lean@95809b59deefd8dfad81e398250aedd7e1aea3b3`
contains reciprocal-product inequalities for Part III, not this complete event.

## Conjecture 1

Section 4, page 13 of the publisher PDF states that for every natural
$n\geq 2$ and $k\geq 1$,

$$
\frac{\varphi(n)^{3k}+\psi(n)^{3k}+\sigma(n)^{3k}}
{\varphi(n)^k\psi(n)^k\sigma(n)^k}
\geq \frac{2(n+1)^{3k}+(n-1)^{3k}}{(n+1)^{2k}(n-1)^k}.
$$

The function correspondence above applies. Subtraction and division are
real. At $k=1$ the right side is
$(3n^3+3n^2+9n+1)/(n^3+n^2-n-1)$, as in Section 3, Theorem 1, page 2.

The C1 proof applies the original `DimitrovPartFourC4.cubic_ratio_bound`,
formerly private in the C4 owner, with
$r=((n+1)/(n-1))^k$, $x=(\psi(n)/\varphi(n))^k$ and
$y=(\sigma(n)/\varphi(n))^k$. The arithmetic bounds `psi_ge` and
`sigma_ge_psi` are imported from `DimitrovLowerBoundsC4C5`, whose note
credits Michael Mazur's pinned Apache-2.0 development. [Supplier attribution and license](dimitrov2026c4c5.md)

The bounded C1 qualification compared Parts III–IV, Sándor–Gryszka III
(DOI 10.7546/nntdm.2025.31.2.361-369, Theorems 8, 9 and 12), and the
Mazur donor at `95809b59deefd8dfad81e398250aedd7e1aea3b3`. The inspected
Sándor–Gryszka results bound sums or pair products, and the donor's
Part III C1/C3 results concern reciprocal products and Nesbitt quotients.
No separate published resolution of the full C1 statement was identified in
that scope. The OpenAlex citing-works query was rate-limited, and Google
Scholar returned a verification page. Exhaustive coverage and priority
remain unverified. [C1 preregistration and bounded screen](https://github.com/the-omega-institute/trureturing/issues/35004)
