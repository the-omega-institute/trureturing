---
bibkey: bettin2018trilinear
authors: Sandro Bettin; Vorrapan Chandee
year: 2018
title: "Trilinear forms with Kloosterman fractions"
doi: 10.1016/j.aim.2018.01.026
url: https://arxiv.org/abs/1502.00769v1
claim: "Theorem 1 bounds trilinear forms with inverse-modulus phases; its single-third-variable specialization has no power saving at the Robin residual's 3:1 candidate alias split, even before the missing phase conversion. The stronger all-aspect-ratio claim in arXiv:2601.00292v1 is withdrawn and is not an input."
strata_touched: []
license: citation-only
triage: anchor
---

# Kloosterman-fraction supplier and its applicability boundary

The inspected mathematical text is Theorem 1, equation (1.2), in
[arXiv:1502.00769v1](https://arxiv.org/html/1502.00769v1), submitted
3 February 2015. The arXiv version record lists that single preprint
version and the journal reference *Advances in Mathematics* 328
(2018), 1234--1262. The DOI above identifies the journal publication;
this note does not assert a comparison of its proof with the preprint.
The bounds below are cited or directly specialized, not reproved or
claimed as new mathematics. No Lean verification is supplied.

## The source contract

Write $e(u)=\exp(2\pi i u)$ and let $\|\cdot\|_2$ denote the norm
of a coefficient sequence on its stated support. For positive lengths
$M_1,M_2,U$, take arbitrary complex coefficients supported on
$[M_1/2,M_1]$, $[M_2/2,M_2]$, $[U/2,U]$, respectively. Restricting
to a fixed nonzero integer $\vartheta$ suffices here. Put
$$
\mathcal B(M_1,M_2,U)=
\sum_{\substack{a\in[U/2,U],\ m\in[M_1/2,M_1],\ n\in[M_2/2,M_2]\\
(m,n)=1}}
\alpha_m\beta_n\nu_a\,
 e\!\left(\vartheta\frac{a\overline m}{n}\right),
\qquad m\overline m\equiv1\pmod n.
$$
For every fixed $\eta>0$, Theorem 1 supplies
$$
\begin{aligned}
|\mathcal B(M_1,M_2,U)|
\ll_\eta{}&\|\alpha\|_2\|\beta\|_2\|\nu\|_2
 \left(1+\frac{|\vartheta|U}{M_1M_2}\right)^{1/2}\\
&\times\left[
 (UM_1M_2)^{7/20+\eta}(M_1+M_2)^{1/4}
 +(UM_1M_2)^{3/8+\eta}(UM_1+UM_2)^{1/8}
 \right].
\tag{BC1}
\end{aligned}
$$
The two terms are added. The theorem does not allow choosing their
minimum. The modular inverse and the coprimality condition belong to
the source's object; an additive phase $e(mr/q)$ is a different input.

## Direct single-variable specialization

Set $U=1$ and $\nu_1=1$, so the third variable has one value.
Let $X\to\infty$, and suppose
$$
M_1=X^{t+o(1)},\qquad M_2=X^{1-t+o(1)},
\qquad \tfrac12\le t<1.
$$
With $\vartheta$ fixed, the factor in square brackets in (BC1) is
$$
X^{7/20+t/4+\eta+o(1)}
 +X^{3/8+t/8+\eta+o(1)}.
\tag{BC2}
$$
Both have the same coefficient-norm prefactor. The elementary
Cauchy--Schwarz bound has instead the factor
$(M_1M_2)^{1/2}=X^{1/2+o(1)}$.
A power saving from (BC2), for a sufficiently small fixed $\eta$,
requires $t<3/5$; in this range both exponents without $\eta$ are
strictly below $1/2$. At $t=3/4$, they are respectively
$$
\frac{43}{80}>\frac12,\qquad \frac{15}{32}<\frac12.
\tag{BC3}
$$
Consequently (BC1) does not supply a power saving for this split.
Taking the minimum with the independent elementary bound remains
available, but supplies no power saving either. This is a comparison
of upper-bound allowances, not a lower bound on the actual form.

## Interface to the retained Robin residual

The [owning residual application](corvalan2023interpolation.md),
equations (I18)--(I19) and (I105)--(I106), retains the actual aliases
$$
b_{N,q}=\sum_{j\le N/q}\frac{a_{N,qj}}j
$$
and the phases $e(mr/q)$, with every reduced numerator and their
original weights. A candidate factorization near $q=N^{3/4+o(1)}$
and $qj\asymp N$ has lengths $N^{3/4+o(1)}:N^{1/4+o(1)}$.
Even if a conversion to (BC1) with a single third variable and no
additional losses were available, (BC3) would give no power saving.
No such phase and weight conversion is established here.

Moreover $q>N/2$ has only the alias $j=1$. A bilinear label does
not furnish a second long averaging interval in that sector.
The source does not pay the constant $d_N$, the actual endpoint,
or their interaction with the retained middle frequencies.

This excludes this direct specialization as a quantitative supplier.
It does not exclude a different factorization, a genuine third
average, a valid spectral transformation or additional structure in
the actual coefficients. None of those interfaces is supplied by
renaming the original sum.

## Withdrawn stronger claim

The [current arXiv record for 2601.00292](https://arxiv.org/abs/2601.00292)
marks Dong--Robles--Zeindler, *Bilinear forms with Kloosterman fractions
and applications*, as withdrawn in v2, 5 January 2026. Its withdrawal
comment states that a missed factor $L^2$ in equation (2.53) changes
$L^5$ to $L^7$, and the argument does not give the claimed improvement.
Here $L$ is that paper's amplification parameter.

The [superseded v1](https://arxiv.org/html/2601.00292v1) contains the
stronger all-aspect-ratio bound in Theorem 1.6. That bound is not an
input to this note or to the Robin application. The withdrawal and
its stated reason are existing source information, not a new error
discovery or a new obstruction theorem. No claim about every other
result in that withdrawn manuscript is needed.
