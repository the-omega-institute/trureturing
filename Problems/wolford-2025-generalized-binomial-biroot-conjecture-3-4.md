---
slug: wolford-2025-generalized-binomial-biroot-conjecture-3-4
bibkey: wolford2025biroot
doi: 10.48550/arXiv.2508.14095
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/WolfordBinomialBiroot.result
url: https://arxiv.org/abs/2508.14095v3
---

# Wolford's generalized binomial biroot convergence conjecture

## Problem

Isaac Wolford, *Combinatorial and Gaussian Foundations of Rational Nth Root
Approximations: Theorems and Conjectures*, arXiv:2508.14095v3 (2025),
Conjecture 3.4:

> For any $x > 0$, positive integer $n$, and $c > 0$,
> $$\lim_{m \to \infty} \beta^n_m(x, c) = \sqrt[n]{x}$$
> where $\beta^n_m(x,c)$ is defined as above.

The definition in Section 3.1.3 is

$$
\beta^n_m(x,c)=
\frac{\displaystyle\sum_{k=0}^{\lceil m/n\rceil}
 x^k c^{m-nk}\binom m{nk}}
{\displaystyle\sum_{k=0}^{\lceil m/n\rceil-1}
 x^k c^{m-nk-1}\binom m{nk+1}}.
$$

Both upper bounds are inclusive. The exponents of $c$ are signed integers,
and $\binom m j=0$ when $j>m$. The quantifiers cover all positive real
$x,c$, every natural $n\ge1$, and the full sequence of positive integers
$m$, including every residue class. The target is the positive real
$n$th root $x^{1/n}$.

### Source identity

The source note is `D5/L/ArithSums/wolford2025biroot`. The checked primary
`main.tex` SHA-256 is
`3402df742475b710e44e388927ebd5f8fd81b8537a67c4dc55ef9a1f70a49156`.
Its definition is at line 339, Conjecture 3.4 at lines 357–361, the statement
that no general proof is attempted at line 363, and the zero-extension
convention at line 448. These identify the v3 source, not a different
floor-indexed or integer-parameter assertion.

## Motivation

The settling declaration is `D5/S3/ArithSums/WolfordBinomialBiroot.result`.
It applies finite stochastic mixing to the literal binomial multisections
in the conjecture. Wolford supplies the generalized biroot and its
convergence conjecture, together with the square-root case. The repository
derivation connects the full real-parameter assertion to the retained
`FiniteStochasticMixing.primitive_convergence` theorem.

## Gap

The mathematical gap addressed is convergence of the complete source
quotient, including the exceptional indexing at $n=1$ and positivity of
every positive-index denominator. The settling theorem includes both
denominator positivity and the full limit. It imposes no rationality,
primality or subsequence restriction.

### Known limits

The theorem assumes $x,c>0$ and $n\ge1$. It supplies no quantified rate
uniform in these parameters, no assertion for nonpositive parameters or
$n=0$, and no assertion for a root index varying with $m$. The Lean
sequence is totalized to zero at $m=0$; that index lies outside the
positive tail and does not assert positivity of its denominator.

## Route

Put $r=x^{1/n}>0$, so $r^n=x$, and for $j\in\mathbb Z/n\mathbb Z$ define

$$
R_j(m)=\sum_{\substack{0\le\ell\le m\\\ell\equiv j\pmod n}}
 \binom m\ell c^{m-\ell}r^\ell.
$$

Let $S$ shift each cyclic state to its successor and set
$P=aI+bS$, where $a=c/(c+r)$ and $b=r/(c+r)$. Then $a,b>0$ and
$a+b=1$. Expanding $P^m$ gives
$(P^m)_{0j}=R_j(m)/(c+r)^m$. The walk is stochastic. Its $n$th power
has a positive term for each displacement: choose the representative
$0\le\ell<n$ of $j-i$ and use the corresponding binomial summand.
This establishes primitivity for every positive $n$, including composite
$n$. Its stationary row is uniform, and finite stochastic mixing gives

$$
\frac{R_j(m)}{(c+r)^m}\longrightarrow\frac1n.
$$

For $n\ge2$, write the source numerator and denominator as $U_m,V_m$.
The exact index correspondence $\ell=nk$ gives $U_m=R_0(m)$, and
$\ell=nk+1$ gives $rV_m=R_1(m)$. Terms beyond $m$ vanish by zero
extension, including terms whose displayed integer exponent is negative.
Thus $U_m/V_m=rR_0(m)/R_1(m)\to r$, using $1/n\ne0$.

For $n=1$, the source denominator omits the constant binomial term.
The exact identities are $U_m=(c+x)^m$ and
$xV_m=(c+x)^m-c^m$ for positive $m$. Hence

$$
\beta^1_m(x,c)=\frac{x}{1-(c/(c+x))^m}\longrightarrow x,
$$

because $0<c/(c+x)<1$. This correction is necessary; the uncorrected
residue ratio does not equal the source quotient at $n=1$.
For all $n\ge1$ and $m>0$, the $k=0$ denominator term is
$mc^{m-1}>0$ and all other terms are nonnegative, proving $V_m>0$.

### Formalization

Lean names below have prefix `D5.S3.ArithSums.WolfordBinomialBiroot`.

| Source object or bridge | Lean declaration | Correspondence |
| --- | --- | --- |
| Exact ceiling | `ceiling` | Natural ceiling of the rational quotient $m/n$. |
| Inclusive source sums | `numerator`, `denominator` | Natural binomial coefficients and integer powers of $c$. |
| Positive-tail quotient | `beta` | Literal quotient for $m>0$, zero at $m=0$. |
| Cyclic walk expansion | `shift_pow`, `walk_pow`, `normalized_residue` | Complete weighted binomial multisection in each matrix entry. |
| Mixing hypotheses and limit | `walk_stochastic`, `walk_primitive`, `walk_column`, `walk_limit` | Primitive stochastic walk with uniform stationary row. |
| Source reconstruction | `multisection`, `numerator_residue`, `denominator_residue` | Exact finite index bijections for the original bounds. |
| Boundary and domain | `denominator_one`, `limit_one`, `denominator_pos` | Corrected $n=1$ denominator and every positive-index domain. |
| Full assertion | `result` | All positive real $x,c$, every $n\ge1$, denominator positivity and convergence along all natural indices. |

The bridge declarations other than the public definitions and `result`
are private implementation helpers, not separate resolved problems.

## Falsifier

A positive real pair $x,c$ and positive integer $n$ for which some
positive-index denominator is nonpositive, or the full quotient fails to
converge to $x^{1/n}$, would contradict the settling assertion. A mismatch
in the inclusive bounds, integer exponents, zero extension or $n=1$
correction would invalidate the source correspondence even if a different
quotient converged. Finite numerical agreement alone establishes none of
these universal claims.

## Evidence

### Results

The frozen theorem `D5.S3.ArithSums.WolfordBinomialBiroot.result` has the
complete telescope $(x,c:\mathbb R)$, $(n:\mathbb N)$, $0<x$, $0<c$,
$1\le n$, and concludes

$$
\bigl(\forall m\in\mathbb N,\ m>0\Rightarrow V_m>0\bigr)
\quad\land\quad
\operatorname{Tendsto}(\beta^n_\bullet(x,c),\operatorname{atTop},
 \mathcal N(x^{1/n})).
$$

Its frozen statement identity is
`sha256:c3ac23c1075ad16841dee4b5fd997a18904709053158ee3b936986819d0257e7`;
its compiled type identity is
`sha256:081ee0d58066e142c171790e66d30719373ae47c9d9609fdeeaa18d1a7ce3aa8`.
The checked axiom closure is `Classical.choice`, `Quot.sound`, `propext`.
The corresponding Reg evidence covers the whole six-binder telescope,
with registration identity
`f553f1f9ed93d50eedf9a01b759722503c8658f3d4f9eb07eae3bda77c3a1758`
and binding evidence
`861b1aac94448ce877961f2abab7d4030dd56b794ab8b08179fe274941a7f007`.

The intended admission basis is `open-problem-resolution`, Tier 1,
source year 2025. Its immutable preregistration is
[issue 25810, comment 6588918078](https://github.com/the-omega-institute/trureturing/issues/25810#issuecomment-6588918078).
This metadata adds no Lean declaration or escape-witness claim and does
not reclassify the frozen proof. Direct reuse of finite stochastic mixing
and its consumed helpers supplies no additional resolved-problem credit.

## Triage

- **Proved mechanism.** The cyclic walk and exact source reconstruction
  give the full fixed-parameter limit; the separate $n=1$ correction
  preserves the original denominator. The settling theorem also proves
  positivity for every positive index.
- **Source consequences.** The square-root case and every other fixed
  positive integer root index follow within the same assertion. They are
  consequences of this one settlement, not additional problems or credit.
- **Unproved extensions and neighbouring questions.** A rate uniform in
  $x,c,n$, a root index varying with $m$, monotonicity of the quotient,
  and extensions beyond positive real parameters are future research
  candidates. No such additional statement is asserted or formalized here.

## ASSUMED-UNVERIFIED

Worldwide literature coverage, external ownership coverage, priority and
exhaustive openness are unverified. The checked primary source states the
conjecture without attempting a general proof. The checked nearby source,
Shunia–Prunescu, arXiv:2610.13365v1, Appendix A.3 through line 2185,
has integer-radicand, floor and root-index restrictions in its stated
scope; it does not supply the exact arbitrary-positive-real assertion
recorded here. This bounded comparison is not a worldwide novelty claim.

Loogle and LeanSearch returned HTTP 403, and the citation search returned
HTTP 429. Reservoir catalog availability does not establish a filtered
theorem search. These access limits leave external search coverage
incomplete; no broad search or fresh Lean verification is claimed by this
metadata dossier. Publication projections, final source validation,
required CI, merge and dev synchronization remain separate obligations;
no delivered credit follows from this source binding alone.
