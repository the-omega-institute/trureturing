---
bibkey: faveri2026fixedorder
authors: Alexandre de Faveri
year: 2026
title: Optimal large sieve for fixed order characters
doi: null
url: https://arxiv.org/abs/2610.04045v1
claim: Theorem 1.1 gives an n-th-power-free large sieve for fixed-order Hecke characters over number fields containing the n-th roots of unity; applying it to the project's complete sextic signed packet requires additional reciprocity, weight, and source-restoration checks.
strata_touched: []
license: citation-only
triage: anchor
---

# Optimal large sieve for fixed order characters

The source is [arXiv:2610.04045v1](https://arxiv.org/pdf/2610.04045v1), submitted 2 October 2026. This card records the statement of Theorem 1.1 and the conditions relevant to the FIB sextic interface. It is a preprint; no independent proof audit, Lean verification, or claim about the Robin problem is made here.

The theorem fixes $n\ge3$, a number field containing the $n$-th roots of unity, and a finite set $S$ containing the places above $n$ such that the ring of $S$-integers has class number one. The family $\chi_a$ is built from fixed ray data. Its reciprocity law has the form

$$
\chi_a(b)\,\chi_b(a)^{-1}=\alpha([a],[b]),
$$

where the phase $\alpha$ depends only on the two ray-class images. Thus the theorem permits a finite ray-class decomposition; it does not permit an unqualified exchange of the two arguments.

## The large-sieve statement

Let $n\ge3$, let $K$ contain the $n$-th roots of unity, and fix the finite set of places and ray data used to construct the family of $n$-th order Hecke characters $\chi_a$. With $\Theta_n(A,B)$ denoting the operator norm in which both the parameter $a$ and the inner variable $b$ range over $n$-th-power-free ideals, Theorem 1.1 states

$$
\Theta_n(A,B)
\ll_{\varepsilon}
(AB)^\varepsilon
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right).
$$

The theorem is therefore available in principle for $n=6$ over the Eisenstein field, which contains the sixth roots of unity. Its hypotheses concern the specified Hecke-character family and ideal norms; they do not supply a result for an arbitrary row weight or an arbitrary signed subpacket.

## The possible FIB interface

The active carrier expression in the current native packet is

$$
a=A_1R_2^2R_3^3R_4^4R_5^5.
$$

The existing [sextic packet analysis](openai2026quasirh.md) already records the primary-generator choice, the unit and modulus-36 finite Fourier factors, the root-number transport, and the source decomposition
$$
u=\epsilon_u n b_2^2b_3^3b_4^4b_5^5.
$$
\]
Those results are the reusable local input for this interface. They do not yet identify the project's transported character, with all its zero extensions and masks, with the particular ray-data family $\chi_a$ fixed in de Faveri's definition, so the reciprocity step remains an interface obligation rather than a second derivation of the local formulas.

If the five radicals are actual pairwise-coprime squarefree ideals, then every prime valuation of $a$ is in ${0,1,2,3,4,5}$, so $a$ is sixth-power-free. Freezing $R_2,R_3,R_4,R_5$ and applying the theorem in the $A_1$ direction gives the four formal output scales

$$
R^2,\qquad A_1R,\qquad A_1^{5/6}R^{4/3},\qquad A_1^{1/3}R^{11/6}.
$$

Combining those scales with the already recorded carrier count produces the source-conditional exponent envelope

$$
\max\left\{\frac5{12},\frac49,\frac{19}{36},\frac49\right\}
=\frac{19}{36}<\frac23.
$$

This is an arithmetic comparison of exponents. It becomes an analytic estimate only after the source packet has been shown to satisfy every hypothesis below.

## Conditions that remain open for this application

The project has the character in the orientation $\chi_p(a)$, while the theorem is stated for $\chi_a(b)$. Sextic reciprocity gives a finite ray-class phase relating them on the coprime locus, but that phase must be partitioned and transported together with the original units, conjugate orientation, and all zero extensions. The extra fixed factors already present in the source row also have to be included before the row parameter is declared sixth-power-free.

The theorem is an $L^2$ operator bound with a coefficient vector in the inner variable. The native packet additionally contains the original Möbius coefficients, moving masks, common smooth profiles, and a complete signed pair of parent columns. It is necessary to prove that these weights can be fixed or decomposed without a new polynomial loss, and that polarization or an equivalent argument preserves the complete signed restoration.

Finally, the frozen carrier sums must be performed on the same actual realization. Independent optimization of the five carrier boxes would not establish a bound for the jointly constrained source. Until these reciprocity, sixth-power-free, profile, restoration, and joint-count steps are supplied, the $19/36$ figure is only a conditional interface calculation. It does not prove the native Robin estimate, Robin's inequality, or the Riemann hypothesis.
