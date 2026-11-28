---
slug: glampe-2026-six-period-multipliers
bibkey: glampe2026polynomial
doi: null
url: https://arxiv.org/abs/2610.15131v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/GlampeSixPeriodMultipliers.multipliers_iff
---

# Glampe et al. multipliers for a scaled six-period recurrence

## Problem

After equation (10), Glampe et al. ask, “Given a gibonacci sequence, for which
values of $k$ do such identities exist? How are the coefficients obtained?”
Take the family with $G_{t,0}=1$, $G_{t,1}=0$ and
$G_{t,n+2}=tG_{t,n+1}-t^2G_{t,n}$ for each integer $t$ with $|t|\ge 2$.
For any characteristic-zero field $K$ and positive integer $k$, determine
whether there are coefficients $c_0,\ldots,c_k\in K$ and bits
$\varepsilon_0,\ldots,\varepsilon_k\in\mathrm{Bool}$, all fixed independently of $n$,
such that the following holds for every natural $n$, including zero. The function
$\mathrm{bit}$ decodes a Boolean value as zero for false and one for true.
$\mathrm{IntCast}_K$ denotes the canonical cast from the integers into $K$.

$$
\mathrm{IntCast}_K(G_{t,kn})
= \sum_{i=0}^k c_i (-1:K)^{n\mathrm{bit}(\varepsilon_i)}
       \mathrm{IntCast}_K(G_{t,n})^i.
$$

This specializes the multiplier question on page 2, equations (9)–(10).
[Versioned source and locator](../Library/RecurrenceAlgebraic/glampe2026polynomial.md)

## Motivation

A classification for this family gives an explicit criterion on $k$ and an
explicit coefficient vector in every admitted residue. It includes rational
coefficients by taking $K=\mathbb{Q}$.

## Gap

The paper poses the general multiplier question. The literature search
recorded in the preregistration found related results with different
hypotheses and found no classification for this family in its searched
sources. The dossier concerns the specialization with seeds $(1,0)$ and
recurrence parameters $(t,-t^2)$. [Preregistration #35126](https://github.com/the-omega-institute/trureturing/issues/35126)

## Route

Write $G_{t,n}=t^n h_n$, where $h_n$ repeats $(1,0,-1,-1,0,1)$. At the odd
indices $1$ and $7$, both source values vanish, so any fixed mask and
coefficient vector give equal outputs. The powers of $t$ at exponents $k$
and $7k$ are distinct, which forces $h_k=0$ and leaves residues $1$ and $4$.
At indices $6j$ every sign factor is one. The even-index polynomial agrees
with $X^k$ on the infinitely many distinct inputs $t^{6j}$ and is therefore
$X^k$. At index $2$, residue $4$ gives opposing nonzero values, so only
residue $1$ remains. In that residue $h_{kn}=h_n$, and oddness of $k$ gives
$h_n^k=h_n$.

## Falsifier

An identity with a fixed mask and coefficient vector at an excluded residue
and an allowed scale would contradict necessity. A failure of
$G_{t,kn}=G_{t,n}^k$ at any index, including zero, for an admitted multiplier
and an allowed scale would contradict the exhibited witness.

## Evidence

The frozen theorem `multipliers_iff` has statement ID
`sha256:3df5bcd3949db5aa5a11c13eb58cd50e6b697a1c01311dccc418c65c10053592`.
The Mathlib report measures `Classical.choice`, `Quot.sound`, and
`propext` for this theorem and `scaledGibonacci`.
[Blueprint](../Blueprint/D5/S1/Recurrence/GlampeSixPeriodMultipliers.md) · [Frozen state](../Golden/Frozen/state/D5/S1/Recurrence/GlampeSixPeriodMultipliers.lean.json)

The four-slot registration remains unresolved under IE-C050
`ClosedTruthReadout` with `forbidden_dependency` under `source.unsafe_or_external` at
`Int.natAbs`.
A validated binding certificate for the exact scale hypothesis is still
missing. [Issue disclosure](https://github.com/the-omega-institute/trureturing/issues/35126#issuecomment-7233870654)

## Triage

Tier 1. For this family, `multipliers_iff` proves existence exactly when
$k\equiv 1\pmod 6$. One witness has $c_k=1$, all other coefficients zero,
and an all-false mask. Either mask value works in degrees with zero coefficient.
[Theorem](../Blueprint/D5/S1/Recurrence/GlampeSixPeriodMultipliers.md)

### What the settlement shows

The odd-index comparison restricts the possible residues, and the even
indices force a unique polynomial through infinitely many distinct values.
The scale hypothesis ensures those comparisons over each field of
characteristic zero. The general multiplier classification for equation (9)
remains open in this development.

## ASSUMED-UNVERIFIED

Priority beyond the sources recorded in the preregistration is unverified.
[Search scope](https://github.com/the-omega-institute/trureturing/issues/35126)
