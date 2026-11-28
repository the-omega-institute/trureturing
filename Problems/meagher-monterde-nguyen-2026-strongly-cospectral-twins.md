---
slug: meagher-monterde-nguyen-2026-strongly-cospectral-twins
bibkey: meaghermonterdenguyen2026sedentary
doi: 10.48550/arXiv.2611.00567
url: https://arxiv.org/abs/2611.00567v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.result
---

# A return-amplitude bound for sedentary strongly cospectral twins

## Problem

Meagher, Monterde and Nguyen ask the following in §9, printed page 27, of
*Sedentariness in Cayley graphs*. [Versioned source](https://arxiv.org/pdf/2611.00567v1#page=27)

> In general, it would be interesting to find a bound for sedentary twins that admit strong cospectrality.

## Motivation

The graph-level floor quantifies the amount of amplitude that must remain
at either twin throughout the walk. The hypotheses allow both adjacent
and nonadjacent twins, including graphs with irrational supported gaps.

## Gap

The source's Theorem 2.2(2), equation (2.3), gives the qualitative equivalence
at half spectral mass. Section 9 asks for an explicit lower bound. The
preregistration records the checked literature and related graph-specific
bounds. [Issue #35281](https://github.com/the-omega-institute/trureturing/issues/35281)

## Route

For a finite simple graph with adjacency matrix $A$, let $u$ and $v$ be
distinct vertices with identical adjacency to every third vertex and with
$E_λ e_u = ± E_λ e_v$ for each full eigenspace projector $E_λ$. The twin
difference has eigenvalue $θ=-1$ for adjacent twins and $θ=0$ for
nonadjacent twins. Projecting the difference and applying strong cospectrality
gives $E_θe_u=(e_u-e_v)/2$, including when $θ$ is repeated.

Put $U(t)=e^{itA}$, let $J$ be the distinct remaining supported eigenvalues,
and write $a_λ=(E_λ)_{uu}>0$ for their weights. These weights sum to one half.
The projector weights agree at both twins, giving equality of the complex
diagonal amplitudes. Dephasing by $e^{itθ}$ gives
$F=1/2+Σ_{λ∈J}a_λ z_λ$ with $z_λ=e^{it(λ-θ)}$.

An odd zero-gap relation has character value $1$ at $z$ and $-1$ at the
constant phase $-1$. The weighted character chord bound gives
$4≤D(ℓ)Σ_{λ∈J}a_λ|z_λ+1|²=2D(ℓ)\operatorname{Re}F$.
When every zero-gap relation has even coefficient sum, the positive-time
orbit closure contains the constant phase $-1$, where $F$ vanishes.

## Falsifier

A counterexample to the quantitative statement would require a finite
simple adjacency graph, a qualifying twin pair, an odd zero-gap relation
and a real time violating its lower bound.

## Evidence

In $C_5[O_2]$ the pair-difference space has eigenvalue zero, and the
pair-constant restriction is twice the five-cycle adjacency matrix.
The cycle eigenvalues are $2$ and $(-1±\sqrt{5})/2$ with multiplicities
$1,2,2$. Cyclic symmetry makes each projector diagonal constant, and
doubling a fiber divides each of those weights by two. The two vertices
in a doubled fiber are strongly cospectral. Their nonzero gaps are
$4,-1+\sqrt{5},-1-\sqrt{5}$ with weights $1/10,1/5,1/5$. The irrational
ratio to $4$ precludes a positive period. The exact relation $(1,2,2)$
gives $D=50$ and a certified floor of $1/25$. Example 7.14 of the source
gives qualitative sedentariness for the cycle blow-up.

## Triage

For every relation $ℓ:J→\mathbb Z$ with $Σ_{λ∈J}ℓ_λ(λ-θ)=0$ and odd
$Σ_{λ∈J}ℓ_λ$, the result gives the following for all real $t$.

```text
D(ℓ) = Σ_{λ∈J} ℓ_λ²/a_λ > 0
|U(t)_{uu}| = |U(t)_{vv}| ≥ 2/D(ℓ)
```

Such a relation exists exactly when the return amplitude has a positive
uniform floor on positive times. The proof uses arbitrary real gaps
and arbitrary multiplicity of the twin eigenvalue.

## ASSUMED-UNVERIFIED

The exact infimum for a general graph and optimal bounds depending only
on graph order remain outside the claim.

The Reg escape audit for `result` remains unfinished. Its source-bound
`DependentFamily.realize` registration and current binding evidence are pending.
[Audit disclosure on #35281](https://github.com/the-omega-institute/trureturing/issues/35281#issuecomment-7239505775)
