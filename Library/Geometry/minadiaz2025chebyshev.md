---
bibkey: minadiaz2025chebyshev
authors: Erwin Miña-Díaz; Olof Rubin
year: 2025
title: "Chebyshev polynomials on equipotential curves"
doi: null
url: https://arxiv.org/abs/2505.03967v1
claim: "Problem 2.2 asks whether equality of a monic Chebyshev polynomial and a monic Faber polynomial on K persists on every exterior equipotential curve."
strata_touched: []
license: citation-only
triage: anchor
---

## Locator

DOI: null

Source: https://arxiv.org/abs/2505.03967v1

Section 1, equation (1.2), specifies the exterior-map normalization.
Section 2, Theorem 2.1, gives convergence to the monic Faber polynomial
as the equipotential radius tends to infinity. Problem 2.2 asks:

> Suppose the compact set $K$ is such that for some $n\in\mathbb N$, $T_{n,K}=\hat F_n$, where $\hat F_n$ is the $n$th monic Faber polynomial associated to the map $\phi$ that satisfies (1.2). Is it true then that $T_{n,L_r}=\hat F_n$ for all $r>1$?

The arXiv version is the source locator; no DOI is recorded.

# Chebyshev polynomials and enclosing circles

Let $\Omega$ be the unbounded component of $\mathbb C\setminus K$.
The normalization is $g_\Omega(z,\infty)=\log|\phi(z)|$ and
$\phi(z)=cz+c_0+c_{-1}/z+\cdots$, where
$c=\operatorname{cap}(K)^{-1}$. When $\Omega$ is simply connected,
$\psi=\phi^{-1}$ maps $|w|>1$ onto $\Omega$.
Write $L_r=\{z\in\Omega:|\phi(z)|=r\}$, let $F_n$ be the
polynomial part of $\phi^n$ at infinity, and set $\hat F_n=c^{-n}F_n$.
The polynomial $T_{n,E}$ is the unique monic degree-$n$ minimizer of
the sup norm on $E$.

For degree one, $T_{1,E}(z)=z-h$, where $h$ is the centre of the
minimal enclosing circle of $E$.

**Repository-derived counterexample.** The declaration
`D5.S3.Analytic.Chebyshev.FaberEquipotentialRefutation.result`
refutes the propagation assertion using the map

$$
\psi(w)=w+\frac1{4w}+\frac1{100}(w^{-2}-w^{-4})
$$

has compact complement contained in the disc of radius $5/4$ and
containing $\pm5/4$. Its monic degree-one Faber polynomial is $z$,
which is also Chebyshev on that complement. On the radius-two image
circle, $z-3/1600$ has sup norm at most $17/8$, whereas
$|\psi(2)|=3403/1600>17/8$. Thus exact equality need not propagate.
The geometric subject is enclosing circles and their centres under
exterior conformal maps.

## Related literature and scope

O. Rubin, *Chebyshev polynomials in the complex plane and on the real
line*, arXiv:2411.14175v2, revised 2026-02-18, lists the same question
as Problem 5.6. Hübner–Rubin, arXiv:2405.05067, gives
rotation-symmetric examples with $T=\hat F=z^\ell$ preserved on
equipotentials. Miña-Díaz–Rubin–Wennman, arXiv:2509.22588, concerns
$n\to\infty$ asymptotics, rather than this fixed-degree implication.
These readings do not establish an exhaustive priority claim.

Xiao–Qiu, *Acta Mathematica Sinica, Chinese Series* 53(2) (2010),
323–328, gives an example where Chebyshev polynomials on a Julia set
and its equipotentials differ. **ASSUMED-UNVERIFIED:** its full text
was not available, so whether its Julia set
satisfies $T=\hat F$ was not determined. In the monic degree-$m$
normalization, the relevant centre condition is
$h=-a_{m-1}/m$, where $a_{m-1}$ is the coefficient of $z^{m-1}$.

Citation only; no source PDF or TeX is redistributed.
