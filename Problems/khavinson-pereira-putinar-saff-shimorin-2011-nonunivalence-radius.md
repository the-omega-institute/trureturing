---
slug: khavinson-pereira-putinar-saff-shimorin-2011-nonunivalence-radius
bibkey: khavinson2011borcea
doi: 10.1007/978-3-0348-0142-3_16
url: https://arxiv.org/abs/1010.5167
triage: theorem
motivation_gids:
  - D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result
---

# Khavinson–Pereira–Putinar–Saff–Shimorin: nonunivalence radius

## Problem

D. Khavinson, R. Pereira, M. Putinar, E. B. Saff and S. Shimorin, *Borcea's variance conjectures on the critical points of polynomials*, arXiv:1010.5167v2, §5, Theorem 5.1 and Conjecture 4. See [khavinson2011borcea](../Library/Zeros/khavinson2011borcea.md).

> Theorem 5.1 (Alexander-Kakeya). If a polynomial F of degree n has no critical points in a closed disk of radius R, then it is univalent in the concentric disk of radius R sin(π/n).

> If F is an nth degree polynomial with F(0) = 0, then F is not univalent in any closed disk of radius larger than σ_p(F) sin(π/n), p ≥ 1, centered at zero.

> Of course, if the conjecture is true for p = 1, then it follows for all p ≥ 1. By the Alexander-Kakeya Theorem, the truth of this conjecture implies the truth of Conjecture 1 for the same value of p. It can be easily seen that the strongest case p = 1 of this conjecture is true for n = 2.

For every $n\ge1$, every complex polynomial $F$ of degree $n$ vanishing at zero, every real $p\ge1$ and every real $r>\sigma_p(F)\sin(\pi/n)$, the assertion forbids injectivity on the closed disk centered at zero with radius $r$. Zeros are counted with algebraic multiplicity, and $\sigma_p$ is the infimum over all complex centers of the normalized root moment. The formal definition includes every stated quantifier and imposes no simple-root or geometric restrictions.

## Motivation

The conjecture proposes an analytic route from a root-spread statistic to a critical-point bound. The external assertion and proposed counterexample are identified in [issue #18950](https://github.com/the-omega-institute/trureturing/issues/18950).

## Gap

The proposed radius can be strictly smaller than a disk on which the polynomial remains injective. A root moment controls a global root configuration; the divided difference can still stay away from zero throughout that disk.

## Route

Set $F(z)=z-z^4$, $p=1$, and $r=5/8$. Its four roots with multiplicity are $0,1,\omega,\overline\omega$, with $\omega=-1/2+i\sqrt3/2$ and all three nonzero roots of modulus one. Evaluation of the moment at center zero gives $\sigma_1(F)\le3/4$. Nonnegativity of every root moment supplies the lower bound needed for this infimum comparison.

Since $\sin(\pi/4)=\sqrt2/2$,

$$
\sigma_1(F)\sin(\pi/4)\le\frac{3\sqrt2}{8}<\frac58.
$$

For $|z|,|w|\le5/8$,

$$
F(z)-F(w)=(z-w)(1-z^3-z^2w-zw^2-w^3),\qquad
|z^3+z^2w+zw^2+w^3|\le4(5/8)^3=125/128<1.
$$

The second factor never vanishes, proving injectivity on the closed disk.

## Falsifier

The exact degree-four polynomial, order one and radius five eighths refute the universal assertion. The roots, strict radius inequality and closed-disk injectivity must all hold for the same polynomial and radius; none is substituted by an open-disk estimate or a numerical approximation.

## Evidence

`D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius.result : ¬ conjecture` proves the refutation with the full conjecture as its target. The only public declarations are the root-moment definition, its infimum, the conjecture and its negation. All auxiliary calculations are private.

## Triage

**REFUTED — Conjecture 4, by $z-z^4$ at $p=1$.** The conjectured radius is at most $3\sqrt2/8$, while the polynomial is injective on the closed disk of radius $5/8$.

**COMPUTED (analytic calculation, not Lean-verified here) — failure at every finite real $p\ge1$.** For $G(z)=z-z^6$, the roots are zero and the five fifth roots of unity. Thus $\sigma_p(G)\le(5/6)^{1/p}\le1$, and $\sigma_p(G)\sin(\pi/6)\le1/2<3/5$. The divided-difference sum is $z^5+z^4w+z^3w^2+z^2w^3+zw^4+w^5$. Its six terms each have modulus at most $(3/5)^5$, so its modulus is at most $6(3/5)^5=1458/3125<1$. Hence $G$ is injective on the closed disk $|z|\le3/5$ for every such order.

**UNAFFECTED — Borcea's variance Conjecture 1.** Only the proposed nonunivalence route fails; no counterexample to the critical-point variance statement follows.

**OPEN — a correct universal radius replacing $\sigma_p(F)\sin(\pi/n)$.** For $n≥2$, one can ask for the sharp constants $C_{n,p}$ such that every degree-$n$ polynomial vanishing at zero fails injectivity beyond $C_{n,p}\sigma_p(F)$. The counterexample rules out the proposed constants but does not determine valid sharp replacements. For $z-z^4$, the same estimate proves injectivity whenever $4r^3<1$.

## ASSUMED-UNVERIFIED

Absence of subsequent settlements and worldwide priority are not established. The degree-six calculation and any proposed sharp universal replacement are not Lean theorems in this module. Theorem 5.1 is contextual literature, not an additional formalized claim.
