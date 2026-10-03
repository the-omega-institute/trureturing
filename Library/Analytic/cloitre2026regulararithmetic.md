---
bibkey: cloitre2026regulararithmetic
authors: Benoit Cloitre
year: 2026
title: "Regular Arithmetic Functions, Volume I. Theory, Applications, Examples"
doi: null
url: https://arxiv.org/abs/2609.09366v1
claim: The volume introduces a regularity index for triangular arithmetic kernels, proves an Ingham-kernel equivalence with RH, and records a Fibonacci gauge for an Abelian fractional-part sum; the gauge does not transport the project's FIB affine source to Robin's divisor-sum point values.
strata_touched: []
license: citation-only
triage: anchor
---

# Regular arithmetic functions and the Fibonacci gauge

The source is [arXiv:2609.09366v1](https://arxiv.org/abs/2609.09366v1), submitted 8 September 2026. It is a 374-page preprint; this card records the stated theorem interfaces and does not independently audit the complete proof or claim Lean verification.

## The RH interface

The volume studies the triangular equation

$$
\sum_{k\le n}a_kG(n,k)=n^{-\beta}
$$

and defines a regularity index from the transition between forced decay and absorbed decay. For the Ingham kernel

$$
G(n,k)=\Phi(k/n)=\frac{k}{n}\left\lfloor\frac{n}{k}\right\rfloor,
$$

the source states that the regularity index is $1/2$ exactly when the Riemann hypothesis holds. The mechanism passes through the discrete equation, Möbius inversion and the Mellin transform; it is not a new Robin inequality or a finite verification.

## The Fibonacci result and its boundary

Section 14.9 records Harcos's theorem for the Fibonacci gauge $f(n)=F_n$:

$$
\sum_{k=1}^{n}\left\{\frac{F_n}{F_k}\right\}
=
\begin{cases}
\dfrac{\pi}{8}n+O(\sqrt n),&n\text{ odd},\\[4pt]
\dfrac{3\log 2}{4}n+O(\sqrt n),&n\text{ even}.
\end{cases}
$$

The proof uses Lucas--Fibonacci congruences and parity. This is a genuine Fibonacci-indexed Abelian density, but its gauge is the sequence $F_n$ in a fractional-part sum. It does not define the project's five-window Zeckendorf address, the affine family $N_g=1+F_rg$, or the complete divisor weight $\sigma(N_g)/N_g$.

Consequently the source supplies a candidate analytic language for a future FIB-gauged kernel, not the missing map from FIB atoms to the same Robin/Möbius point value. To consume the RH equivalence here one would still need a kernel whose discrete coefficients recover the relevant divisor or signed $\mu/\Phi$ residual and a proof that the FIB observation preserves its regularity index. The Fibonacci gauge theorem alone supplies neither.
