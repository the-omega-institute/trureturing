---
bibkey: mandel2019dragging
authors: A. Mandel; S. Robins
year: 2019
title: "Dragging the roots of a polynomial to the unit circle"
doi: null
url: https://arxiv.org/abs/1908.03208
claim: "Section 10, Problem 3 asks for the minimal faces of the fan of interlace certs containing rational points and for interlace rational polynomials in those faces."
strata_touched:
  - D5/S3/Arith/InterlaceFan
license: citation-only
triage: anchor
---

# Rational points in the fan of interlace certs

## Verified locator

Source: https://arxiv.org/abs/1908.03208

Version 3, Section 10, Problem 3. Section 5.2, equations (12)–(15), defines the interlace
functionals and their fan; Proposition 5.5 describes its faces. Theorem 4.2
identifies the interlace number with the maximum of the interlace functionals.

Problem 3: “What are the minimal faces of the FOIC that contain rational points?
Most rays clearly do not (except in darga 6). On the other hand, Section 9.2 gives
several examples of faces that do. Are there interlace rational polynomials in
those minimal faces?”

The sigma-coordinate convention is $I_j(x)=-\sum_{k=1}^{\lfloor n/2\rfloor}
\cos(2\pi jk/n)x_k$. Its reciprocal polynomial is
$\sum_k x_k(X^k+X^{n-k})$, so for even $n$ the middle polynomial coefficient
is twice the middle sigma coordinate. Its root evaluations equal $-2I_j(x)$.
Interlace rational means rational coefficients and rational interlace number.

The formal development classifies faces containing nonzero rational points by
the root-order classes they omit. The zero vector belongs to every closed face
and is excluded from this classification.
