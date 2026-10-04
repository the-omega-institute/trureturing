---
bibkey: kushelzabreiko2008ideal
authors: Olga Y. Kushel and Petr P. Zabreiko
year: 2008
title: Gantmakher–Krein theorem for 2-totally nonnegative operators in ideal spaces
url: https://arxiv.org/abs/0812.0902v1
claim: The source requires positivity preservation on an ideal function space, together with exterior-square positivity and further operator hypotheses. The inherited pointwise cone on the original theta remainder is trivial, so its nonzero compressed semigroup and resolvent cannot meet this interface in the original radial coordinates.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Exterior-square positivity and the original theta remainder

## Published hypotheses

The inspected [primary preprint](https://arxiv.org/pdf/0812.0902v1) is
arXiv:0812.0902v1. Its PDF has SHA-256
`10cc9d4d2207731b83c71ff3514ce0b5197304f0c8ccb07629968eb95b521c28`.
Only bibliographic information and the following source/application
distinctions are retained; no third-party PDF or implementation is copied
into the project.

Section2, PDF p.3, defines a Banach ideal function space by solidity:
if $|f|\le|g|$ almost everywhere and $g$ belongs to the space, then so
does $f$, with the corresponding norm bound. Its nonnegative cone is
the cone of almost-everywhere nonnegative functions. Section4, PDF p.6,
defines regular operators as differences of operators preserving this
cone, and resolvent-regularity requires regularity of every resolvent
outside the spectrum.

Section7, Theorem3, PDF p.10, assumes an almost perfect ideal space, a
compact, positivity-preserving, resolvent-regular operator with positive
spectral radius, and a positivity-preserving exterior square with positive
spectral radius. It obtains a leading positive eigenvalue and a
second-eigenvalue alternative subject to the stated spectral-circle
conditions. Simplicity and nodal ordering are not borrowed from this
statement without their additional hypotheses. Theorem4, PDF pp.10–11,
gives the integral-kernel version: both the original kernel and its second
associated kernel must be nonnegative almost everywhere and not
identically zero on their stated domains. Neither theorem supplies a
prescribed numerical bound such as one-half.

The remark on PDF p.11 allows an arbitrary almost reproducing cone for
the exterior square. It does not remove the original operator's
positivity hypothesis or provide a transported cone for a given
orthogonal remainder. Quadratic nonnegativity in a Hilbert space is a
different condition from preserving a cone of nonnegative functions.

## The inherited cone is lost after critical projection

Use the [original minimal even theta form](fukushima2011dirichlet.md)
with probability measure
$d\nu=2\Phi(x)\cosh(x/2)dx$, nonnegative self-adjoint energy operator
$A$, and $A1=0$. Retain the
[critical decomposition](lagarias2004li.md) into constants, the closed
span $N$ of the known real one-half eigenvectors, and the nontrivial
reducing remainder

$$
\mathcal R=(\mathbb C1\oplus N)^\perp,
\qquad Q=Q_{\mathcal R}.
$$

All these operator/model premises are the existing paper-level source
applications. The following interface check is conditional on them;
it is not a Lean-certified operator construction.

Since $\nu$ is finite, every $r\in\mathcal R$ is integrable and has
$\nu(r)=0$. For a real $r\ge0$ almost everywhere, the usual
nonnegative-integral criterion gives $r=0$ almost everywhere. Thus

$$
\mathcal R\cap L^2_+(\nu)=\{0\}. \tag{1}
$$

The original measure and radial order are retained here. In particular,
$\mathcal R$ is not an ideal function space with that order: for any
nonzero $r\in\mathcal R$, the function $|r|$ belongs to ambient $L^2$
and has positive mean, so $|r|\notin\mathcal R$. Solidity would require
it to belong to $\mathcal R$. Restricting positivity preservation to
the zero cone in (1) would be vacuous and would not supply the source's
ideal-space hypotheses.

There is a stronger ambient obstruction. Suppose a complex-linear
operator $B$ on the original even $L^2(\nu)$ preserves nonnegative real
functions and has range in $\mathcal R$. Equation(1) gives $Bf=0$ for
every nonnegative $f$. Positive and negative parts span the real even
space, and complexification spans the whole even space, so $B=0$.

For $t>0$ and $\alpha>0$, consider the bounded compressions

$$
K_t=Qe^{-tA}Q,\qquad G_\alpha=Q(A+\alpha)^{-1}Q. \tag{2}
$$

They have range in $\mathcal R$ and are nonzero. Indeed, for any
nonzero $r\in\mathcal R$, the spectral measure $\mu_r$ of $A$ gives

$$
\langle r,K_tr\rangle
=\int_{[0,\infty)}e^{-ts}\,d\mu_r(s)>0,
\qquad
\langle r,G_\alpha r\rangle
=\int_{[0,\infty)}\frac{d\mu_r(s)}{s+\alpha}>0. \tag{3}
$$

Consequently neither compression preserves the ambient pointwise
nonnegative cone. In any ordinary integral-kernel representation acting
on that entire ambient even/radial space, its kernel cannot be
nonnegative almost everywhere: such a kernel would preserve this cone.
No existence or regularity of such a kernel is assumed. This rules out
the direct application of the source's nonnegative-kernel criterion in
the original coordinates before any ordered-minor calculation.

This conclusion is separate from the
[full semigroup's ordered-jump obstruction](karlinmcgregor1959coincidence.md).
It requires no compact support in $\mathcal R$, no projected bump
calculation, and no compactness assertion about $A|_{\mathcal R}$.
The known critical vectors lie in $N$, not in $\mathcal R$, so they
cannot be identified as the first or second eigenvectors of an operator
whose domain is $\mathcal R$.

## The quantitative obligation remains

The cone obstruction does not decide the desired lower bound on
$\mathcal R$. A different ordered realization would require an explicit
map from its function space and cone to this same remainder, verification
of the published operator hypotheses, and a spectral identification that
produces the numerical threshold. Merely naming a new cone or observing
quadratic nonnegativity of an exterior power does not provide that map
or estimate.

For the already specified nonnegative self-adjoint restriction
$A_{\mathcal R}$, the spectral theorem gives the standard equivalence

$$
D(r)\ge\tfrac12\|r\|_\nu^2
\quad(r\in\mathcal R\cap\mathcal F)
\quad\Longleftrightarrow\quad
\|(A_{\mathcal R}+\alpha)^{-1}\|
\le\frac1{\alpha+1/2}, \tag{4}
$$

for any fixed $\alpha>0$. Equation(4) is a reformulation, not a new
resolvent estimate. The norm bound remains unproved; this source check
does not settle RH, Robin, or the original cofinal signed comparison.
