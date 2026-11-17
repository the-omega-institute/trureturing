---
bibkey: diaconismiclo2013secondorder
authors: Persi Diaconis; Laurent Miclo
year: 2013
title: On the spectral analysis of second-order Markov chains
doi: 10.5802/afst.1383
url: https://hal.science/hal-00719047v1
claim: Conjecture 1.3 asks for unimodality of the absolute spectral gap and a square-root comparison at its maximum.
strata_touched:
  - D5/S3/Fourier/DiaconisMicloUnimodality
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.5802/afst.1383

Source: https://hal.science/hal-00719047v1

Published source: Annales de la Faculté des Sciences de Toulouse (6), 22(3), 573–621.

## Source statement

Conjecture 1.3, printed p. 580:

> Let G be a finite Abelian group and S be a generating set of G with |S| ≥ 2. Let K⁽¹⁾ be the identity S × S matrix (seen as a speed transfer kernel, it forces the chain to keep going always in the same direction) and consider again the interpolating kernels given in (1.9), as well as the associated second order Markov kernels M⁽ᵃ⁾ for a ∈ [0,1], which are also trajectorially reversible with respect to the probability measure m defined in (1.10). There exists a₀ ∈ [0,1] such that λ(M⁽ᵃ⁾) is nondecreasing for a ∈ [0,a₀] and nonincreasing on [a₀,1]. Furthermore there exists two values 0 < c₁ < c₂ (perhaps depending on |S|), such that c₁ √λ(L) ≤ λ(M⁽ᵃ⁰⁾) ≤ c₂ √λ(L).

The uniform speed interpolation is equation (1.9), the position–speed transition is (1.6), the underlying walk is (1.8), and the stationary pair law is (1.10). The gap uses the maximum modulus on stationary-mean-zero complex functions, rather than the real-part gap or the singular-value gap.

The source has no arXiv identifier. Its HAL version is hal-00719047v1.

## Defining expressions

Equation (1.6), printed p. 577, and equations (1.8)–(1.10), printed p. 578:

> P((x,y),(x′,y′)) = δ_xy(x′) K_{x′}(y,y′) (1.6).
> L(x,x′) = μ(x′ − x) (1.8).
> ∀ a ∈ [0,1],  K⁽ᵃ⁾ := (1 − a)K⁽⁰⁾ + aK⁽¹⁾ (1.9).
> ∀ x,x′ ∈ G,  m(x,x′) := 1/(|G||S|) if x′ − x ∈ S, and 0 otherwise (1.10).

Printed p. 575:

> By invariance of m, the subspace F_*(m,ℂ) := {F ∈ F(V²,ℂ) : m[F] = 0} is stable under M, so let Θ_*(M) ⊂ ℂ be the spectrum of M_*, the restriction of M to F_*(m,ℂ).
> The spectral gap of M is λ(M) := 1 − max{|θ| : θ ∈ Θ_*(M)} ∈ [0,1]

Printed p. 576:

> Similar definitions can be given for the spectral gap of L, by replacing the state space V² by V.

## Scope

The four-speed example on ZMod 11 refutes the unimodality clause and hence the conjunction. The square-root comparison considered independently remains open. Neither an extension to every product group nor a general product-character radius estimate is asserted.

The citation screen recorded in issue #26482 did not find a settlement among the sources examined; completeness remains ASSUMED-UNVERIFIED.

## Arithmetic experiment

Repository: https://github.com/the-omega-institute/trureturing-experiments

Commit: b05508b33fd60e3c180beba68b13be65d8c8b379

Path: docs/reports/diaconis-miclo-2013-conjecture-1.3-unimodality-product-family/check.py

SHA-256: 96dc31d6b841057f7ba34eb62c20b6e1130a3efe2673f04c3ac0cce726fb80d0

The recorded exact-arithmetic command is `python3 check.py` (exit 0). It certifies the four-speed determinant identity, root intervals, endpoint Schur inequalities, and middle sign change. It supplies arithmetic evidence for the single-factor example. It does not certify the proposed bound for every product character: a two-factor character at a=3/10 has a computed real eigenvalue between 453/1000 and 454/1000, which exceeds 43/100. The stronger product-family claim is excluded.
