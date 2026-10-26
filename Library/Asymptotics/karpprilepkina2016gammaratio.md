---
bibkey: karpprilepkina2016gammaratio
authors: D. B. Karp and E. G. Prilepkina
year: 2016
title: Completely monotonic gamma ratio and infinitely divisible H-function of Fox
doi: 10.1007/s40315-015-0128-9
url: https://arxiv.org/abs/1501.05388
claim: "Conjecture 1 bounds the number of interior zeros of the Meijer G-function by that of the power-sum control function when all a_i are nonnegative and the parameter excess is positive."
strata_touched:
  - D5/S3/Analytic/MeijerZeroCount/Defs
  - D5/S3/Analytic/MeijerZeroCount/Result
license: citation-only
triage: anchor
---

# Gamma quotients and the Meijer zero-count conjecture

## Verified locator

DOI: 10.1007/s40315-015-0128-9

Source: https://arxiv.org/abs/1501.05388

Pinned version: https://arxiv.org/abs/1501.05388v2, Section 2,
equations (9), (10), the definition of $G^{p,0}_{p,p}$ and Conjecture 1.
Journal publication: *Computational Methods and Function Theory*
16 (2016), 135–153.

## Mathematical correspondence

For real parameter vectors $a,b$ of length $p$, put

$$R(s)=\frac{\prod_{i=1}^p\Gamma(a_i+s)}
{\prod_{i=1}^p\Gamma(b_i+s)},\qquad
v(t)=\sum_{i=1}^p(t^{a_i}-t^{b_i}),\qquad
\psi=\sum_{i=1}^p(b_i-a_i).$$

The source defines

$$G^{p,0}_{p,p}\!\left(x\;\middle|\;\begin{matrix}b\\a\end{matrix}\right)
=\frac{1}{2\pi i}\int_L R(s)x^{-s}\,ds.$$

Conjecture 1 asserts that if $a_i\ge0$ and $\psi>0$, then the number
of zeros of this $G$ on $(0,1)$ is at most the number of zeros of $v$
there. `Defs.gammaQuot` and `Defs.control` encode these two expressions.
`Defs.meijerG` uses the inverse Mellin integral on $\Re s=1$.
`Defs.claim` restricts the proposed comparison to $\psi>1$, where this
vertical integral is absolutely convergent and lies to the right of
the numerator poles. Refuting this restriction refutes the source's
universal assertion.

`Result.family` gives exactly $n$ distinct zeros of $G$ and one of $v$
for every integer $n,d\ge2$ and real $c>0$, with
$a=(n+c,n+c)$ and $b=(c,2n+d+c)$.
`Result.result` proves the negation of `Defs.claim`.

The bounded literature scope and its limitations are stated in
`Problems/karp-prilepkina-2015-meijer-zero-count.md`.
