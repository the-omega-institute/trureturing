---
bibkey: pintz1984remainder
authors: J. Pintz
year: 1984
title: On the remainder term of the prime number formula and the zeros of Riemann's zeta-function
doi: 10.1007/BFb0099452
url: https://www.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1984.Pintz_0.pdf
claim: The published sign-change interval for pi minus li supplies quantitatively located positive psi-error points for the actual CA source application.
strata_touched: []
license: citation-only
triage: anchor
---

# Sign-change intervals and the actual CA source clock

The [original scan](https://www.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1984.Pintz_0.pdf)
contains the article in Lecture Notes in Mathematics 1068, pp.186–197,
[DOI](https://doi.org/10.1007/BFb0099452). It has 12 pages and SHA-256
`3b2fedd7f1b4aed5938e05eb0d85e9fe3f9884b0cbfa78b0893dad53c9e27741`.
Printed pp.186, 188–190, 192–193 were read for the following inputs.
This checks the cited statements and notation, without an independent
whole-proof audit or Lean verification. Section 4, p.193, sketches the
proof of Theorem 8 and refers proofs of the other theorems to further
papers; the scan is used for Theorem 4's published statement.

Equation (1.1), p.186, defines $\Delta(x)=\psi(x)-x$, retaining all prime
powers. Equation (2.1), p.189, defines
$\Delta_1(x)=\pi(x)-\operatorname{li}(x)$, with
$\operatorname{li}(x)=\operatorname{PV}\int_0^x dt/\log t$.
Theorem 4, p.190, equation (2.4), states unconditionally that
$\Delta_1$ changes sign in

$$
\left[Y\exp\{-500(\log\log Y)^3\},Y\right]
\qquad(Y>Y_2),
$$

where $Y_2$ is ineffective. In particular the interval contains a point
with $\Delta_1>0$. The source writes $\log_2Y$ for $\log\log Y$.

Equation (1.15), p.188, gives the zero abscissa $\Theta$; equation
(3.13), p.192, records
$\Theta=\inf\{\vartheta:\Delta(x)=O(x^\vartheta)\}$.
For $\Theta<1$, this supplies $|\psi(x)-x|=O(x^\sigma)$ for every fixed
$\sigma>\Theta$. When $\Theta=1$, the application instead uses the
prime number theorem's bound with $\sigma=1$.
