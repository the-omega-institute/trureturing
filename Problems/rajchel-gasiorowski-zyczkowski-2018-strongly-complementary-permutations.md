---
slug: rajchel-gasiorowski-zyczkowski-2018-strongly-complementary-permutations
bibkey: rajchelgasiorowskizyczkowski2018robust
doi: 10.1007/s11786-018-0384-y
url: https://arxiv.org/abs/1804.10715v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result
---

# The maximal number of pairwise strongly complementary permutation matrices

## Problem

G. Rajchel, A. Gąsiorowski and K. Życzkowski, *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*, arXiv:1804.10715v2, Mathematics in Computer Science 12 (2018), ask about sets of $k$ $n\times n$ permutation matrices whose pairs are strongly complementary. In `unisto9.tex`, lines 678–690, they write:

> Due to the definition of strong complementarity each pair of matrices has non-zero entries in different places, so that $k \leq n$. We are not able to determine how the maximal number $k$ of such matrices depends on the dimension $n$, nor whether the bistochastic matrices belonging to the interior of this polytope are unistochastic.

The first clause is the cardinality problem settled here. The formal predicate `claim` says that for every natural $n$ with $1\le n$, the `sSup` of the cardinalities of finite sets of $n\times n$ natural-valued permutation matrices that are pairwise `IsStronglyComplementary` is $2^{\operatorname{padicValNat}(2,n)}$. The unistochasticity question is separate.

## Motivation

The paper uses strongly complementary permutation matrices to build unistochastic triangles and higher-dimensional faces with the flat bistochastic matrix. Determining the largest possible family gives the exact two-adic size of the available permutation vertices in dimension $n$. It also identifies the range in which the paper's face construction can be instantiated, while leaving its separate interior-unistochasticity question untouched.

## Gap

The bounded literature check recorded in issue #23851 found the question in both arXiv versions v1 and v2. The nine Semantic Scholar citing works listed there (1812.09083, 2003.12184, 2101.11288, 2306.00532, 2307.06998, 2312.00497, 2404.18847, 2405.05785 and 2608.21185), together with arXiv:2204.13008, were reported not to contain the phrase “strongly complementary”; additional screens of 0708.4051 and 2310.03436 and targeted arXiv and Semantic Scholar searches were reported not to determine the maximum. Repository searches for 1804.10715, “strongly complementary” and “robust Hadamard” found no earlier settlement of this question. This is `not-found-in-searched-scope`, not an exhaustive priority claim.

## Route

1. The definitions are literal encodings of the source. `entry_one` and `entry_zero`, for every type `α` with `[DecidableEq α]`, every permutation `σ : Equiv.Perm α`, and every `i j : α`, identify the entries of `σ.permMatrix ℕ` with `σ i = j` and `σ i ≠ j`, respectively. `matrix_injective`, under the same type and decidable-equality hypotheses, proves that the map from permutations to their matrices is injective.

2. `complementary_iff`, for every `α` with `[DecidableEq α]` and every `σ τ : Equiv.Perm α`, proves that the matrix complementarity predicate is equivalent to `Function.Involutive (σ⁻¹ * τ)`. `strong_iff`, with the same hypotheses, strengthens this to equivalence with `Function.Involutive (σ⁻¹ * τ) ∧ ∀ x, (σ⁻¹ * τ) x ≠ x`. Thus strong complementarity is exactly a fixed-point-free relative involution for the formal permutation matrices.

3. `row_relabelling`, for every `α` with `[DecidableEq α]` and every `ρ σ τ : Equiv.Perm α`, proves that replacing `σ, τ` by `σ * ρ⁻¹, τ * ρ⁻¹` preserves strong complementarity. `lift_family`, for `n : ℕ` and a finite matrix set `s : Finset (Matrix (Fin n) (Fin n) ℕ)` satisfying `∀ p ∈ s, IsPermutationMatrix p`, produces a finite permutation set whose matrix image is `s` and whose cardinality is `s.card`. `normalize_family`, for `n : ℕ`, a finite permutation set `s : Finset (Equiv.Perm (Fin n))`, `hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ => IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))`, and `hne : s.Nonempty`, preserves its cardinality and pairwise relation while producing a set containing the identity permutation.

4. `normalized_involutions`, for `n : ℕ`, a finite permutation set `s : Finset (Equiv.Perm (Fin n))`, `h1 : 1 ∈ s`, and `hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ => IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))`, proves both `∀ σ ∈ s, σ ^ 2 = 1` and `(s : Set (Equiv.Perm (Fin n))).Pairwise Commute`. `closure_exponent_two`, for `n : ℕ`, a finite `s : Finset (Equiv.Perm (Fin n))`, `hs : ∀ σ ∈ s, σ ^ 2 = 1`, and `hc : (s : Set (Equiv.Perm (Fin n))).Pairwise Commute`, proves `∀ g ∈ Subgroup.closure (s : Set (Equiv.Perm (Fin n))), g ^ 2 = 1`. Hence the generated subgroup is a 2-group in the exact sense used by the next step.

5. `orbit_evaluation_bound`, for `n : ℕ`, a finite `s : Finset (Equiv.Perm (Fin n))`, `hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ => IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))`, and `x : Fin n`, proves `s.card ≤ Nat.card (MulAction.orbit (Subgroup.closure (s : Set (Equiv.Perm (Fin n)))) x)`. `least_orbit_divisor`, for `n : ℕ` with `1 ≤ n`, a subgroup `g : Subgroup (Equiv.Perm (Fin n))`, and `hg : IsPGroup 2 g`, produces an `x : Fin n` and `a : ℕ` such that the orbit has cardinality `2 ^ a` and `2 ^ a ∣ n`. `permutation_family_upper`, for `n : ℕ` with `1 ≤ n`, a finite `s : Finset (Equiv.Perm (Fin n))`, and `hs : (s : Set (Equiv.Perm (Fin n))).Pairwise (fun σ τ => IsStronglyComplementary (σ.permMatrix ℕ) (τ.permMatrix ℕ))`, combines these facts to prove `s.card ≤ 2 ^ padicValNat 2 n`; its empty-family branch is handled separately.

6. `matrix_family_upper`, for `n : ℕ` with `1 ≤ n`, a finite matrix set `s : Finset (Matrix (Fin n) (Fin n) ℕ)`, `hp : ∀ p ∈ s, IsPermutationMatrix p`, and `hs : (s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary`, lifts `s` and applies `permutation_family_upper` to prove the same cardinality bound. For the lower bound, `two_adic_decomposition`, under `1 ≤ n`, supplies `m` with `0 < m`, `Odd m`, and $n = 2^{padicValNat(2,n)}m$. `elementary_translation_family`, for `n a m : ℕ`, a hypothesis `hm : 0 < m`, and an equivalence `e : Fin n ≃ ((Fin a → ZMod 2) × Fin m)`, constructs a finite family of permutations of cardinality `2 ^ a` whose distinct members are pairwise strongly complementary. `matrix_family_lower`, under `1 ≤ n`, produces a finite matrix set `s` satisfying `∀ p ∈ s, IsPermutationMatrix p`, `(s : Set (Matrix (Fin n) (Fin n) ℕ)).Pairwise IsStronglyComplementary`, and `s.card = 2 ^ padicValNat 2 n`.

7. `result` unfolds `claim`, uses `matrix_family_lower` to exhibit an attained cardinality $2^{padicValNat(2,n)}$, uses `matrix_family_upper` to bound every attained cardinality by that value, and applies the two order bounds for the natural-number supremum. This proves the exact `sSup` identity for every $n$ with $1 ≤ n$.

## Falsifier

A falsifier would have to exhibit a positive dimension $n$ for which the formal `sSup` differs from $2^{\operatorname{padicValNat}(2,n)}$, or show that the formal predicates do not encode the source's objects. The formal family consists of finite sets of matrices on `Fin n`; `IsPermutationMatrix` means equality with `σ.permMatrix ℕ` for a permutation of `Fin n`, and `IsStronglyComplementary` is exactly the source's four-index complementarity condition together with the one-way zero-support condition. The matrix convention is `σ.permMatrix ℕ i j = 1` exactly when `σ i = j`.

Because `maxStronglyComplementary` is defined with `sSup`, a valid challenge would also need to account for both parts of the proof: `matrix_family_lower` supplies a member at the claimed cardinality and `matrix_family_upper` bounds every attained cardinality. The theorem is restricted to $n\ge1$; it makes no claim about the extension of the definition at $n=0$.

## Evidence

The canonical source is `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.lean`.
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.lean.json`.

Declaration statements:
- `result`: `sha256:4ed3e2c7e07b136366af1a8ef2c31345a20d6bfdbd3f88a3dc00a7f1b4feb316`;
- `claim`: `sha256:ceb1bc6deb688a5d911a3d05c674e618929edd5a2ee293bc0eb2e242fe9896a4`.

## Triage

Tier 1 question stated in a 2018 paper, preregistered in issue #23851 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every natural number $n$ with $1\le n$, the `sSup` of the cardinalities of finite sets of $n\times n$ natural-valued permutation matrices whose distinct members are pairwise `IsStronglyComplementary` is $2^{\operatorname{padicValNat}(2,n)}$.

**Computed, not formalized:** the values of $2^{v_2(n)}$ on the valuation classes of small $n$.

**Argued, not formalized:** The orbit description gives the explanatory mechanism: after a common row relabelling puts one permutation at the identity, relative permutations are fixed-point-free involutions; the normalized family generates a commuting exponent-two subgroup, its orbit sizes are powers of two, and a smallest orbit size divides $n$. The exact statements needed for the settlement are formalized by the named lemmas in `Route`; this paragraph adds no separate theorem. The matching construction is the translation picture on $(\mathbb Z/2)^a\times\{1,\ldots,m\}$ with $n=2^a m$ and $m$ odd; its exact finite implementation is the content of `elementary_translation_family` and `matrix_family_lower`.

The settlement answers only the cardinality clause in the source question. It does not determine whether bistochastic matrices in the interior of the polytope generated by a strongly complementary family and the flat matrix are unistochastic. The source's robust Hadamard and equi-entangled-basis results, and its conditional statements about unistochastic faces, are outside the proposition proved here and receive no new formal conclusion. Any source statement that requires the unresolved interior-unistochasticity clause therefore remains conditional/open after this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and searches recorded in issue #23851; the citing-work screens and search-seat reports there were not independently reproduced here, so exhaustive worldwide priority is unverified. The source's interior-unistochasticity question and its other results are not formalized by `result`. The explanatory interpretations in “Argued, not formalized” are not additional Lean declarations. Any claim beyond the exact positive-dimension `sSup` identity, including a conclusion about the interior of the associated polytope, remains unverified here.
