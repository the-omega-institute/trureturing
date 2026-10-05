---
bibkey: calderon2026rectangular
authors: Kevin Calderon
year: 2026
title: "Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients"
doi: 10.48550/arXiv.2608.00347
url: https://arxiv.org/abs/2608.00347v1
claim: "Conjecture 6.3 asks for reciprocal first and second moment congruences for inert primes in imaginary quadratic orders."
strata_touched:
  - D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments
license: citation-only
triage: anchor
---

# Reciprocal moments in imaginary quadratic orders

## Verified locator

DOI: 10.48550/arXiv.2608.00347. Source: https://arxiv.org/abs/2608.00347v1.
Conjecture 6.3 is on PDF page 19; equations (6.1) and (6.3) specify its setting.

## Source statement

“Let ω satisfy (6.1), and let p satisfy (6.3). Then, for every k ≥ 1,
H₁,ω(k) ∈ p²ᵏOω,p, H₂,ω(k) ∈ pᵏOω,p.”

The source TeX states:

> Let $\omega$ satisfy \eqref{eq:omega-minimal-polynomial}, and let $p$ satisfy
> \eqref{eq:omega-inert-prime}.  Then, for every $k\geq1$,

$$
H_{1,\omega}(k)\in p^{2k}\mathcal O_{\omega,p},
\qquad
H_{2,\omega}(k)\in p^k\mathcal O_{\omega,p}.
$$

The setting is ω² − Tω + N = 0, T,N ∈ ℤ, Δ = T² − 4N < 0,
p > 5, p ∤ Δ, and (Δ/p) = −1. The source defines

$$
U_{\omega,k}:=\{x+y\omega:1\leq x,y\leq p^k,\quad p\nmid(x,y)\},
\qquad H_{r,\omega}(k):=\sum_{z\in U_{\omega,k}}z^{-r}.
$$

Here p ∤ (x,y) means that the two coordinates are not simultaneously divisible
by p. The local order is Oω,p = ℤp[ω]. Both coordinates use positive
representatives, including pᵏ for the zero residue.

## Scope

The paper states Conjecture 6.3 as a conjecture. The Lean result proves both
congruences for all its admissible parameters, using the literal adjoin-root
ring over the p-adic integers. The ω-Ljunggren and ω-Bailey conjectures remain
separate questions; this result discharges their reciprocal-moment premise.
Sharpness of the moment bounds is open.

## Definition fidelity

| Source expression (page 19) | Lean expression |
| --- | --- |
| $\mathcal O_{\omega,p}:=\mathbb Z_p[\omega]$ | `R`: adjoin-root of $X^2-TX+N$ over `PadicInt p` |
| $x+y\omega$ | `element`: natural casts and the pinned `AdjoinRoot.root` |
| $U_{\omega,k}:=\{x+y\omega:1\le x,y\le p^k,\ p\nmid(x,y)\}$ | `U`: the finite image of the filtered positive rectangle in `R` |
| $H_{r,\omega}(k):=\sum_{z\in U_{\omega,k}}z^{-r}$ | `H1`, `H2`: sums over that finite set using `Ring.inverse`, the underlying inverse unit value |

In the admissible setting every element of `U` is a unit. Mathlib's
`Ring.inverse` equals the underlying value of that unit's inverse; its
zero value on nonunits does not occur in the conjecture. The internal shifted
coordinate subtype is related bijectively to the literal finite set inside
the proof of `result`, so the sums count each ring element once.
