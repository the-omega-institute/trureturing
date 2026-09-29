---
slug: lu-sun-zhang-2024-beta-invertible-s3-obstruction
bibkey: lu2024galitydefects
doi: 10.1007/JHEP11(2025)081
url: https://arxiv.org/abs/2406.12151v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result
---

# No β-invertible S₃ symmetry in the ℤ_N × ℤ_N SymTFT when 3 ∣ N

## Problem

D.-C. Lu, Z. Sun and Z. Zhang (arXiv:2406.12151, JHEP 11 (2025) 081) study
G-ality defects of 2d QFTs through the SymTFT of the finite Abelian symmetry
`A`. The anyons of the SymTFT are the pairs `(a, â) ∈ A ⊕ Â`, and an anyon
permutation symmetry is a block matrix `U = (α β; γ δ)` with `β : Â → A` that
preserves the self-statistics and the braiding; `U` is β-invertible when `β`
is invertible. A G-ality extension needs a subgroup isomorphic to `G` whose
non-identity elements are all β-invertible. For `A = ℤ_N × ℤ_N` and `G = S₃`
the paper states (§1.1):

> We find that for any N containing a factor of 2 or 3, there are no
> β-invertible S_3 symmetries in the SymTFT, thus there cannot be S_3-ality
> defects for these N. We are able to prove this analytically when N is even,
> and we conjecture this is true generally for N being a multiple of 3 based
> on our numerical evidence.

Issue #11228 fixes the reading: `Â` is identified with `ℤ_N × ℤ_N` through
the dot product, the symmetries are the invertible 4 × 4 matrices over
`ZMod N` preserving `Q(a, â) = a·â`, `β` is the upper-right 2 × 2 block, and a
β-invertible `S₃` is a homomorphism `ρ : S₃ → GL₄(ZMod N)` into these
symmetries with `det β(ρ g)` a unit for every `g ≠ 1`. Only this group-theoretic
statement is settled; the physical consequence rests on the
Etingof–Nikshych–Ostrik classification of G-extensions and is not formalized.

## Motivation

`D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.result` proves the
conjecture for every `N` divisible by 3. Together with the paper's even case it
shows that a β-invertible `S₃`, and hence an `S₃`-ality extension of this
kind, can exist only when every prime factor of `N` is at least 5, in line with
the paper's tables, where `N = 5` is the smallest admissible value.

## Gap

Issue #11228 preregisters the conjecture, the route and the literature check.
arXiv lists three versions, the last (2025-10-25) matching the published
paper, with the conjecture unchanged. INSPIRE-HEP lists 24 citing records and
OpenAlex 2; the full texts of 23 of them and of the related arXiv:2405.15648
were searched for S₃-ality, G-ality and β-invertibility, and none addresses
the conjecture. The classification of Jordan and Larson (arXiv:0812.1603), on
which the paper builds, reduces such questions to orbits on the Lagrangian
Grassmannian and states no bound of the kind used here.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Reduction modulo 3 maps `ρ` to a homomorphism into the matrices over
   `ZMod 3` that preserve `Q`, with invertible `β` at every `g ≠ 1`: every
   vector over `ZMod 3` lifts, and the determinant of `β` reduces to a unit.
2. Over `ZMod 3`, for `g ≠ 1` let `S_g = δ_g β_g⁻¹`. The matrix `ρ(g)` sends
   `(0, x)` to `(β_g x, δ_g x)` and `Q(0, x) = 0`, so `y · S_g y = 0` for all
   `y`; hence `S_g` has zero diagonal, `S_g(1, 0) = −S_g(0, 1)`, and `S_g` is
   determined by `S_g(0, 1)`.
3. If `g ≠ h` are both non-identity with `S_g = S_h`, then `ρ(h)` sends
   `(0, β_h⁻¹ β_g x)` to `ρ(g)(0, x)`, so `ρ(h⁻¹g)` maps `(0, x)` to a vector
   of the form `(0, z)`, and its `β` block vanishes although `h⁻¹g ≠ 1`.
4. So `g ↦ S_g(0, 1)` is injective from the five non-identity permutations
   into `ZMod 3`, which has three elements.

The same argument shows that every β-invertible group has order at most
`p + 1` for each prime `p ∣ N`; only the conjecture is delivered.

## Falsifier

The answer would change if the symmetries of the SymTFT were not the
`Q`-preserving automorphisms of `A ⊕ Â`, or if β-invertibility referred to a
block other than the component `Â → A`.

## Evidence

Exact enumeration (issue #11228): over `𝔽_p` with `p = 2, 3, 5` the orthogonal
groups have 72, 1152 and 28800 elements; every β-invertible element has an
alternating `S_g`, with exactly `p` distinct values; there is no β-invertible
`S₃` for `p = 2, 3` and there is one for `p = 5`, the positive control. The
paper reports none for `N = 3, 9, 27`.

The canonical source is
`D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.lean`. Its public
declarations are `Q`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:15d1a898db8463dbe87625c971e362a1838820b25afd11c1f2eadb3410026a90`.
The result declaration has statement identity
`sha256:a91923f6fa6ecdf6441fa3da91d6c1fb6777f4d9fab5c6aecf713be4688e3b5b`.
The Freeze event is
`sha256:0a8b88661d71cb2bdabfc2380b3da260fe971e67b5d65af775bedca8ad54c457`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #11228 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the reduction modulo 3, the alternating lemma, the
injectivity lemma and the count are proved in the module. Its escape witness
is form (2), the public conclusion itself, and its admission basis is
`open-problem-resolution`. Utility `none`: the statement holds for every `N`
divisible by 3.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer; the counting bound may be
known to specialists without a written statement that was found. The Lean
kernel does not authenticate the external source or its version history.
