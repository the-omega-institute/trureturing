---
bibkey: khavinson2011borcea
authors: D. Khavinson, R. Pereira, M. Putinar, E. B. Saff, S. Shimorin
year: 2011
title: "Borcea's variance conjectures on the critical points of polynomials"
doi: 10.1007/978-3-0348-0142-3_16
url: https://arxiv.org/abs/1010.5167
claim: Section 5, Conjecture 4 proposes a nonunivalence radius in terms of the minimum root moment; this assertion is refuted by the polynomial z minus z to the fourth power at order one.
strata_touched:
  - D5/S3/Zeros/CriticalPoints/BorceaNonunivalenceRadius
license: citation-only
triage: anchor
---

# Borcea's variance conjectures on the critical points of polynomials

## Locator

- arXiv: https://arxiv.org/abs/1010.5167 ; specified version arXiv:1010.5167v2.
- DOI: https://doi.org/10.1007/978-3-0348-0142-3_16
- Location: arXiv:1010.5167v2, §5, Theorem 5.1 and Conjecture 4.

## Source and scope

> If F is an nth degree polynomial with F(0) = 0, then F is not univalent in any closed disk of radius larger than σ_p(F) sin(π/n), p ≥ 1, centered at zero.

Here the zeros $z_j$ include algebraic multiplicity and

$$
\sigma_p(F)=\inf_{c\in\mathbb C}\left(\frac1n\sum_{j=1}^n|z_j-c|^p\right)^{1/p}.
$$

The definitions and the conjecture are attributed to the source. The counterexample and the exact estimates below are repository derivations.

## Counterexample

For $F(z)=z-z^4$, the roots are $0,1,\omega,\overline\omega$, where $\omega=-1/2+i\sqrt3/2$. Therefore $\sigma_1(F)\le3/4$ and

$$
\sigma_1(F)\sin(\pi/4)\le3\sqrt2/8<5/8.
$$

For $|z|,|w|\le5/8$, the divided difference is

$$
F(z)-F(w)=(z-w)\bigl(1-(z^3+z^2w+zw^2+w^3)\bigr),
$$

and the sum in parentheses has modulus at most $125/128<1$. Thus $F$ is injective on that closed disk, contradicting Conjecture 4.

## Literature boundary

The source version and statement are supplied with the problem. No online literature check is performed, and no claim of worldwide priority or absence of later settlements is made. The counterexample concerns Conjecture 4's univalence route, and does not refute Borcea's variance Conjecture 1.

## License and formalization boundary

This citation-only note incorporates no source software. The Lean result is the literal negation of the fully quantified Conjecture 4, witnessed at degree four, order one and radius five eighths. The all-finite-order degree-six extension in the problem note is an analytic calculation outside the Lean result.
