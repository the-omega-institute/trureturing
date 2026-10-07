---
slug: alai-2026-ghz-mermin-staircase
bibkey: alai2026staircase
doi: 10.48550/arXiv.2608.00124
url: https://arxiv.org/abs/2608.00124v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result
---

# Alai's Staircase for faithful GHZ–Mermin measurement dependence

## Problem

Aaron Alai, *Exact minimum measurement dependence for faithful local
deterministic models of multipartite GHZ–Mermin correlations*,
arXiv:2608.00124v1, Section IX, Conjecture 1 (Staircase), PDF page 4:

> With $R(n) := 2^{\lfloor (n-1)/2 \rfloor}$ the Mermin violation ratio and
> $s(n) := (R+1)/(2R)$ the classical satisfiability,
> $F_{\min}(n) = \frac{R}{2(R+1)} = \frac{1}{4\,s(n)},
> \qquad F_{\min}\cdot s = \frac{1}{4}.$

Section II specifies $n\ge3$, all even-Y setting strings, and all $4^n$
deterministic X/Y answer tables. At each setting the real density is
nonnegative and normalized. A faithful model reproduces the prescribed
full correlator and makes every nonempty proper-subset correlator zero.
The objective is $F=M/2$, where
$M=\max_{s,s'}\sum_\lambda|\rho_s(\lambda)-\rho_{s'}(\lambda)|$.

## Motivation

The frozen declaration
`D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result`
establishes the exact minimum for every $n\ge3$, including a faithful model
attaining it and the matching bound for every faithful model. The exact
value extends the source's certified range $3\le n\le13$ to all party counts.

## Gap

Preregistration #13111 classifies the conjecture as Tier 1 and records the
literal source, quantified target, and literature check. The search seat
reported identifier, title-word, author, and related measurement-dependence
searches with no settlement found; MathDB was checked by indexed search.
The author's arXiv:2608.18886 cites the source but studies a different CHSH
trade-off. These are `not-found-in-searched-scope` readings, not an exhaustive
worldwide priority claim.

## Route

The Walsh-square identity for the complete Boolean quadratic form gives
the exact spectral magnitude. Uniform parity-fiber lifting removes every
nonempty proper-subset correlator while preserving the full correlator.
The odd-party construction attains the spectral overlap lower bound.
The even-party construction lifts the adjacent odd-party model, and an
embedded odd-party setting subset supplies the matching lower bound.
An attained lower bound identifies the infimum with the minimum. Real
algebra then gives the classical-satisfiability form and product identity.

## Falsifier

A faithful model with $F<R/(2(R+1))$, or failure of attainment for some
$n\ge3$, would contradict the quantified claim. `result : claim` is an
unconditional kernel-checked proof: neither optimality nor the existence
of a faithful model is assumed.

## Evidence

The settlement is carried by `AlaiStaircase.result` and its Scribe
`OpenProblemResolutionClaim` with resolution `Proved`. Supporting proofs
include `qFree_walsh_square`, the frozen `parity_conditioned_moments`,
`finite_overlap_lower_bound`, `staircase_lower`, `odd_construction`, and
`even_construction`. The objective ranges over the literal faithful-model
densities, rather than a restricted certificate family.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1; Proved. The settlement concerns the full GHZ–Mermin finite setting
sets and the source's surrendered fraction $F=M/2$.

### What the settlement shows

- **Proved in the settlement module:** the exact value
  $F_{\min}(n)=R/(2(R+1))=1/(4s(n))$ and
  $F_{\min}(n)s(n)=1/4$ for every $n\ge3$, with attainment and universal
  optimality.
- **Proved as consequences of the settlement:** adjacent odd/even party
  counts have the same minimum, every finite minimum is strictly below
  $1/2$, and $F_{\min}(n)$ tends to $1/2$. These consequences are checked
  with the delivered definitions in transient Lean examples; no additional
  public settlement theorem is introduced.
- **Proved by the matching construction and bound:** the source's general
  overlap bound, optimized over setting subsets, is sharp for every full
  GHZ–Mermin scenario. For odd $n$ use all settings; for even $n$ use an
  embedded odd-party subset. This does not assert sharpness of the bound
  obtained using all settings in an even-party scenario.
- **Computed with a transient Lean `norm_num` check:** for $n=4$, the
  source's full-set values $N=8$, $m=6$ give $(N-m)/(N-1)=2/7<1/3$,
  whereas the exact minimum is $1/3$.
- **Open:** frustration-ansatz optimality for cluster-state cores and
  general deterministic-target scenarios. The present proof does not
  settle those questions or richer measurement scenarios.

The conjectured Staircase and its classical-satisfiability identity are
therefore available unconditionally on the stated GHZ–Mermin setting
sets. Claims about other scenario families retain their own hypotheses
and unresolved bounds.

## ASSUMED-UNVERIFIED

Worldwide literature completeness and priority are not established by the
bounded searches recorded in #13111. Extension to cluster-state cores,
general scenarios, and additional settings is not proved here.
