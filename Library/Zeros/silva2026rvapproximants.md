---
bibkey: silva2026rvapproximants
authors: Alisson M. Silva
year: 2026
title: Finite Rodríguez-Villegas Approximants to the Riemann ξ-Function
doi: null
url: https://arxiv.org/abs/2609.25564v1
claim: Theorems 2.1 and 3.1 supply the original-theta Stieltjes profile, reciprocal finite numerators and critical-strip convergence; a directed original-source computation excludes the unit-circle numerator premise at degree four.
strata_touched: []
license: citation-only
triage: anchor
---

# Original-theta finite RV approximants

The primary is [arXiv:2609.25564v1](https://arxiv.org/html/2609.25564v1),
Alisson M. Silva, *Finite Rodríguez-Villegas Approximants to the Riemann
ξ-Function*. Theorems 2.1, 3.1 and 4.1, their proofs and section 5 were
inspected. These remain public-preprint statements; this note supplies
neither a complete independent audit of the paper nor Lean verification.
No source text is vendored.

## Reused source and exact correspondence

Use the standard completed function $\xi$ and $\Xi(t)=\xi(1/2+it)$.
The original even theta density is normalized by
$\Xi(t)=\int_{\mathbb R}\Phi(v)e^{itv}\,dv$. Equations (9)--(10) give

$$
P(x)=G(x(1-x)),\qquad
G(p)=\int_0^\infty
\frac{2\Phi(v)\cosh(v/2)}{1+4p\sinh^2(v/2)}\,dv.
\tag{RV1}
$$

Theorem 2.1 supplies positivity, symmetry, the Stieltjes representation
and the exact critical-strip transform. In particular the endpoint
identity is $P(0)=\xi(1)=1/2$. For an even positive integer $E$, the
paper's numerator and transform are

$$
U_E(q)=\sum_{j=0}^E(-1)^j\binom EjP(j/E)q^j,\qquad
Z_E(s)=\sum_{j=0}^E(-1)^j\binom EjP(j/E)\binom{E-j-s}{E}.
\tag{RV2}
$$

Theorem 3.1 supplies reciprocity of $U_E$, $Z_E(1-s)=Z_E(s)$ and
$Z_E\to\xi$ locally uniformly in $0<\Re s<1$. Theorem 4.1 interprets
the same coefficients through a fermionic supertrace. These constructions
are reused, not new project theorems.

The classical RV unit-circle theorem recalled in section 1 requires
all numerator zeros to lie on the unit circle and $U_E(1)\ne0$.
Section 5 explicitly leaves the numerator zero locations unproved.
Positivity, Stieltjes structure, reciprocity and convergence do not
supply that premise.

## Directed degree-four original-source obstruction

This is a repo-derived numerical application of (RV1)--(RV2), not an
originality claim or a kernel-verified theorem. With
$a=P(1/4)$, $b=P(1/2)$ and $p_0=1/2$, the exact numerator is

$$
U_4(q)=p_0(1+q^4)-4a(q+q^3)+6bq^2.
\tag{RV3}
$$

For $q\ne0$ put $t=q+q^{-1}$. Then

$$
q^{-2}U_4(q)=p_0(t^2-2)-4at+6b,\qquad
\Delta=16a^2-24p_0b+8p_0^2=16a^2-12b+2.
\tag{RV4}
$$

Directed Arb integration of the original infinite theta density gives
strict rational enclosures

$$
\begin{aligned}
495681591851/10^{12}&<a<495681591854/10^{12},\\
494287091469/10^{12}&<b<494287091472/10^{12}.
\end{aligned}
\tag{RV5}
$$

Their exact rational consequence is

$$
\Delta\le
-\frac{3769524708640210671}{15625000000000000000000}<0.
\tag{RV6}
$$

If $|q|=1$, then $t$ is real, but the real quadratic (RV4) has no real
zero. Hence $U_4$ has no unit-circle zero. Its nonzero leading and
constant coefficients make all four zeros lie off that circle. The same
certificate gives $U_4(1)>0$, with an enclosure centered at
$0.0002698140052424128699$. The failure is the unit-circle condition,
not the endpoint nonvanishing condition.

The independent experimental program and directed data are in the
private [experiments repository](https://github.com/the-omega-institute/trureturing-experiments),
[`experiments/xi-rv-quartic/`](https://github.com/the-omega-institute/trureturing-experiments/tree/b4f751e4df5a715a8f492d1599d5a24e2605cf29/experiments/xi-rv-quartic). It reuses the original theta-jet and
scalar-envelope implementations in `docs/reports/theta-mixed-matrix`.
The 256-bit computation includes the infinite theta-series error. For
the integration beyond $v=3$, an explicit bound is less than
$1.13\cdot10^{-544}$. Thus neither a finite theta truncation nor an
unaccounted compact integration replaces the original source.
The numerical enclosures and source normalization remain numerical
certificate evidence, not Lean proofs.

This excludes the premise that every even-degree numerator in this
specific original-source construction has unit-circle zeros. It does
not exclude a sufficiently large-degree subsequence, assert an off-line
zero of $Z_4$, invalidate the paper's convergence or functional equation,
or prove or refute RH. Full Robin remains unresolved. The next usable
input would have to control an appropriate large-degree family or a
different exact zero-location transfer; the failed universal
unit-circle premise cannot be used.
