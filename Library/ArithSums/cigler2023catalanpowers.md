---
bibkey: cigler2023catalanpowers
authors: Johann Cigler
year: 2023
title: "Some experimental observations about Hankel determinants of convolution powers of Catalan numbers"
doi: 10.48550/arXiv.2308.07642
url: https://arxiv.org/abs/2308.07642v2
claim: "Experimentally conjectured closed forms for shifted Hankel determinants of Catalan powers; Conjecture 11 evaluates a size residue class, while v2 Section 3 Conjecture 16 specifies full generating-function numerators, exact degrees and reciprocity."
strata_touched:
  - D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven
  - D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation
license: citation-only
triage: anchor
---

# Cigler, Hankel determinants of convolution powers of Catalan numbers

The paper studies the Hankel determinants D_{r,s}(N) = det(C_{r,i+j+s})_{0 ≤ i,j < N} of the coefficients
C_{r,j} = r/(2j+r) · binom(2j+r, j) of the r-th power of the Catalan generating function, with C_{r,j} = 0 for
negative j and D_{r,s}(0) = 1. It records computer experiments and states several closed forms as conjectures. In
Section 2.2, Conjecture 11 asserts that for k ≥ 1, 0 ≤ m ≤ k+1 and n ≥ 0,
D_{2k+1,m−k+1}((2k+1)n+k) = (−1)^{kn+binom(k,2)} (2k+1)^m (n+1)^m. The case m = 0 was proved in Cigler,
arXiv:2403.11244, equation (22); the remaining cases were open.

Section 3, Conjecture 16, equation (30), asserts for every integer $k\ge1$ and
$m\ge1-k$ that

$$
\left(1+(-1)^k x^{2k-1}\right)^{\binom{k+m}{2}+1}
\sum_{N\ge0}D_{2k-1,m}(N)x^N=Q_{2k-1,m}(x),
\qquad
\deg Q_{2k-1,m}=\pi_{2k+1}(m+k-1)+k,
$$

where $\pi_j(t)=t((j-2)t+(j-4))/2$. Every numerator is asserted to be
palindromic or skew palindromic at its actual degree. Palindromicity is required
when $k\equiv1\pmod4$ and $m$ is even, when $k\equiv3\pmod4$ and $m$ is odd,
and when $k\equiv0,2\pmod4$ and $m\equiv0,1\pmod4$.

The coefficients are defined first as those of the actual Catalan power
series, with the closed form in (1) as an equivalent expression. Equation (6)
on page 2 already records $D_{1,0}(N)=D_{1,1}(N)=1$. The paragraph following
(30) calls $k=1$ “not optimal” and prints
$Q_{1,m+1}(x)=(x-1)^{m+1}P_{2,m}(x)$. In the $m\ge0$ range from (29), its
shifted index does not include $Q_{1,0}$; it does not expressly remove that
boundary or replace the exact-degree assertion with a bound. The printed sign
is not used to evaluate the boundary. This generating-function conjecture is
specific to v2; v1 Conjecture 16 is the different statement numbered 18 in v2.
The arXiv record links CC BY 4.0; this note attributes the source and reproduces
only the mathematical statement and its relevant context.

## Verified locator

DOI: 10.48550/arXiv.2308.07642

URL: https://arxiv.org/abs/2308.07642v2

- Locator: Section 2.2, Conjecture 11, with definitions (1) and (2).
- Locator: v2 Section 3, Conjecture 16, equation (30), printed page 10;
  definitions on page 1, equation (6) on page 2, reciprocity and polygonal
  numbers on page 9, and the continuation on page 11.
