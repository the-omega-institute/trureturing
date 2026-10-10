---
bibkey: liuwuyang2021variant
authors: Kui Liu; Jie Wu; Zhishan Yang
year: 2021
title: A variant of the prime number theorem
doi: null
url: https://arxiv.org/abs/2105.10844v1
claim: Proposition 3.1 bounds triple monomial exponential sums with arbitrary bounded coefficient arrays; it supplies a high-harmonic rectangular estimate under its stated size condition, without controlling a complete drifted Robin positive part.
strata_touched: []
license: citation-only
triage: anchor
---

# A variant of the prime number theorem

The inspected primary is [arXiv:2105.10844v1](https://arxiv.org/abs/2105.10844v1),
submitted 23 May 2021. Proposition 3.1 and equation (3.2), PDF p.3,
have been read in both the PDF and source TeX. This note records that
classical statement and its application boundary, without an independent
audit of the whole proof or Lean certification.

## Triple sums with arbitrary bounded coefficients

Write $e(t)=e^{2\pi it}$ and $m\sim M$ for $M<m\le2M$.
For fixed $\alpha,\beta,\gamma>0$, $\delta\in\mathbb R$, and
$X>0$, $H,M,N\ge1$, the source defines

$$
S_\delta=\sum_{h\sim H}\sum_{m\sim M}\sum_{n\sim N}
 a_{h,m}b_n\,
 e\left(X\frac{M^\beta N^\gamma}{H^\alpha}
          \frac{h^\alpha}{m^\beta n^\gamma+\delta}\right),
\qquad |a_{h,m}|,|b_n|\le1.
$$

The first estimate of Proposition 3.1 states, for every $\varepsilon>0$,

$$
S_\delta\ll_{\alpha,\beta,\gamma,\varepsilon}
 \left((XHMN)^{1/2}+(HM)^{1/2}N
       +HMN^{1/2}+X^{-1/2}HMN\right)X^\varepsilon,
$$

uniformly under $H\le M^{\beta-1}N^\gamma$ and
$|\delta|\le1/\varepsilon$. The application uses $\delta=0$.
The paper also gives an exponent-pair variant; that variant is not
needed for the application recorded here.

## Robin sampling correspondence and limits

The [actual sieve-response application](srivastav2025sievevaughan.md#a-classical-high-harmonic-supplier-on-critical-rectangular-blocks)
uses $(\alpha,\beta,\gamma)=(1,k,1)$ and
$(M,N,X)=(P,D,Hx/(P^kD))$. Its prime and harmonic test coefficients
fit $a_{h,m}$, while the normalized actual LCM coefficient fits $b_n$.
The size hypothesis becomes $H\le P^{k-1}D$; arbitrary bounded
sample-dependent signs are permitted by the coefficient quantifiers.
All four terms and coefficient normalization costs must be retained.
The resulting high-harmonic estimate does not bound the low harmonics,
mean, complete drifted positive part, prime layer or signed Robin tail.
