---
slug: kang-jager-2026-universal-permutative-lift-refutation
bibkey: kang2026lifts
doi: 10.48550/arXiv.2609.01140
url: https://arxiv.org/abs/2609.01140v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/PeriodicOrbits/SkewGroupHolonomy
  - D5/S1/Dynamics/OdometerCyclicFactor
---

# The general minimal branch of Question 1.10

## Problem

The cited v1 asks whether a given minimal/strictly ergodic (Toeplitz)
subshift admits a permutative sliding block code of length ℓ≥2 whose entire
inverse image is minimal/strictly ergodic. This dossier selects the complete
general minimal branch, without the optional Toeplitz hypothesis.

The definition `UniversalRefutation.claim` quantifies over all finite
discrete alphabets A with at least two letters and all nonempty closed
shift-invariant minimal subsets of A^ℤ. It asks for some k≥0 and code
h:A^(k+2)→A, bijective in both endpoints with the remaining letters fixed,
such that every integer shift orbit in the whole inverse image is dense.
The result is literally `UniversalRefutation.result : Not claim`.

## Motivation

The original finite extension uses the actual fibre A^(ℓ−1). Group
holonomy over a regular group action cannot silently replace this fibre.
The construction instead trivializes every finite-set-valued permutation
cocycle on one explicit infinite minimal binary base.

## Gap

Tier 1: an explicitly numbered external question, preregistered before the
formal probe in [issue 24726](https://github.com/the-omega-institute/trureturing/issues/24726).
The inspected public sources included the original v1, the author-hosted
paper, author publication lists, arXiv version/author searches, and adjacent
finite-extension and profinite/S-adic papers. No exact uniform construction
was found in that scope. Citation coverage is incomplete and announced
works in preparation could not be checked. Priority is unestablished.

## Route

Set W₀ᵃ=a and Wₙᵃ=(Wₙ₋₁⁰)^(n!)(Wₙ₋₁¹)^((a+1)n!). The base is the
intersection of all compact two-sided Wₙ-tiling subshifts. Markers in the
decoded block types give unique continuous tilings. Every lower block pair
appears two levels higher, proving uniform recurrence and minimality.
Recognizable boundaries and increasing block lengths exclude every positive
period, so the base is infinite.

For any finite Q and two permutations of Q, a sufficiently high level has
identity holonomy on both block types. Prefix holonomy gives a continuous
transfer satisfying β(Sy)=π(y₀)β(y). The full skew product on Y×Q is
therefore conjugate to S×id. Independently, `BipermutativeLift` reconstructs
every two-sided preimage from the coded point and its actual length-(k+1)
prefix. Combining these homeomorphisms splits the entire lift. Two distinct
prefixes give distinct closed invariant fibres, contradicting minimality.

The same binary Y works for every k and every permitted code. There is no
bounded-length restriction and no substitution of a component for the lift.

## Attribution and limits

The coboundary/invariant-subset mechanism is known prior work; the Library
note gives its primary locator. The formal argument reuses pinned Mathlib
compactness, symbolic dynamics, finite groups, and minimal-action APIs.
The optional Toeplitz branch and formal strict-ergodicity strengthening are
outside this result. Compiled/kernel and delivery status must be read from
the actual checks and PR, not inferred from this dossier.
