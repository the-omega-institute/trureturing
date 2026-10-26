---
bibkey: jacoblangertrunk2016variational
authors: Birgit Jacob, Matthias Langer, and Carsten Trunk
year: 2016
title: Variational principles for self-adjoint operator functions arising from second-order systems
doi: 10.7153/oam-10-29
url: https://files.ele-math.com/articles/oam-10-29.pdf
claim: Theorem 2.4 supplies a generalized Rayleigh variational principle for a holomorphic self-adjoint operator function with monotone form crossings. On the actual confined Weil domain it supplies negative excess-quotient attainment without assuming a uniform lower bound on the excess relative to the ambient norm.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Generalized Rayleigh attainment on the actual excess domain

The inspected primary is the [publisher's complete article](https://files.ele-math.com/articles/oam-10-29.pdf),
*Operators and Matrices* 10(3) (2016), 501--531,
[DOI:10.7153/oam-10-29](https://doi.org/10.7153/oam-10-29).
The 31-page PDF has SHA-256
`1e118a97d5f29abfa71e15a5a3f1c92e4a30acbe9f7ec0033aed9d44170339f6`.
Definition 2.1 is on printed p.505; Theorem 2.4 and formulas
(2.5)--(2.8) are on pp.507--508. Its general Section 2 is used here;
the positivity hypotheses of the later second-order-system model are
not imposed on the Weil energy.

## Published supplier and exact parameter correspondence

The `literature-attested` supplier assumes a holomorphic type-(B)
operator family, self-adjoint on a real parameter interval, a finite
initial negative spectral index, and scalar forms that cross zero
strictly downwards. Before the operator-function essential spectrum,
Theorem 2.4 characterizes isolated eigenvalues by a generalized
Rayleigh functional. Its empty-spectrum alternative (2.8) is part
of the result; existence cannot be inferred merely by naming (2.5).

Keep [W317, W322 and W326](../Weil/suzuki2026screw.md) and
[MR1--MR13](../Weil/hernandezsantamaria2025optimal.md#select-an-attained-negative-representative-with-exactly-matched-multipliers)
on their actual domain. Write

$$
\mathscr H=L^2((\pi,\infty),dx),\qquad
\mathcal V=\{F:M(F)+\mathcal P(F)<\infty\},\qquad
D=M-H>0\quad(F\ne0).
$$

The last inequality is strict on every nonzero vector, but is not
a uniform inequality $D\ge\delta H$ on the entire domain. Use

$$
t_z=\mathfrak E-zD=q_{-z}+zH,\qquad \Re z<0,
\qquad p(F)=\mathfrak E(F)/D(F).
$$

W317's infinitesimal moment bound gives closed sectorial forms on
the common domain $\mathcal V$: locally in $\Re z<0$ their shifted
real part controls $\mathcal P+M$, and their imaginary part is
bounded by that same shifted form. Their affine coefficients give
holomorphic type (B). On real $z<0$, W322 gives self-adjointness
and compact resolvent, so $0$ is outside the essential spectrum
of each represented operator. Thus the operator-function essential
spectrum misses the chosen real interval. The crossing condition
is exactly $\partial_z t_z[F]=-D(F)<0$.

If a negative source exists, MR5 and W317 already give
$-\infty<\rho:=\inf p<0$. Choose $a<\rho$, take the paper's
interval $\Delta=(a,0)$, and choose $a'\in(a,\rho)$. Then
$t_{a'}[F]>0$ for every nonzero $F$, hence its negative spectral
index is $\kappa=0$. The function $p$ is a generalized Rayleigh
functional under Definition 2.1 even when its value lies at or
above the right endpoint zero.

If the operator function had empty spectrum in $\Delta$, (2.8)
with $n=1$ would give $\inf p\ge0$, contradicting $\rho<0$.
Its first eigenvalue therefore exists. Formula (2.5), with
$\kappa=0,n=1$, gives $\rho=\min p$ and a nonzero actual vector
at which it is attained. The source-specific consequence is the
already recorded MR11:

$$
\lambda=-\rho>0,\qquad
Q_\lambda=\mathfrak E+\lambda(M-H)\ge0,
\qquad Q_\lambda(F_*)=0.
$$

This is a direct supplier application, not a new variational
principle. It requires neither a $D^{-1/2}$ change of domain nor
a separately invented $D$-completion. Real and complex infima
agree by the existing real/imaginary splitting in MR6. The true
unit-$H$ cap remains MR13's parameter-dependent $K_\lambda$;
the theorem does not turn it into cap four, identify every older
constrained minimizer, or supply a lower sign bound for the
complete arithmetic energy. This source correspondence has not
been compiled in Lean and does not prove RH or strict Robin.
