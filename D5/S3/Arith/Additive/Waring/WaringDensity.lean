/- GID: D5/S3/Arith/Additive/Waring/WaringDensity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringDensity.lean#L1-L198
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringBound

/-!
# Schnirelmann density and the last step of Waring's problem

Linnik's proof of the Waring–Hilbert theorem (see `WARING-M3-PLAN.md` and the
notes of G. Jameson, "Linnik's proof of the Waring–Hilbert theorem") separates
into two halves:

* an **analytic** half: for suitable `s = s(k)` the number of representations
  `r_s(n) = #{(n_1,…,n_s) : n_1^k + … + n_s^k = n}` satisfies a mean-value
  estimate, which forces the set
  `S = {n | ∃ t ≤ s, IsSumOfKthPowers k n t}` to have positive *Schnirelmann
  density*;
* a **combinatorial** half: a set of positive Schnirelmann density is an
  additive basis of finite order.

This file formalizes the step of the combinatorial half that is needed once the
density is known to exceed `1/2`:

```lean
theorem add_eq_univ_of_density (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hA : HasDensity A α) (hB : HasDensity B β) (hαβ : 1 < α + β) :
    ∀ n, ∃ a ∈ A, ∃ b ∈ B, a + b = n
```

i.e. two sets of Schnirelmann densities summing to more than `1` cover `ℕ` by
sums.  Applied with `A = B = S` this says: *if more than half of all positive
integers are sums of at most `s` `k`-th powers, then every natural number is a
sum of at most `2s` `k`-th powers.*

The proof is the pigeonhole principle: if `n` is not a sum `a + b` with
`a ∈ A`, `b ∈ B`, then `a ↦ n - a` injects `A ∩ [1,n]` into
`[0,n-1] \ B`, so

```text
|A ∩ [1,n]| + |B ∩ [1,n-1]| ≤ n - 1,
```

which contradicts `α + β > 1` for `n ≥ 1`.

The remaining combinatorial step (Schnirelmann's iteration, which amplifies
*positive* density to density exceeding `1/2`) is **not** proved here; see
`WARING-M3-PLAN.md`.
-/

open Finset

namespace Waring

/-- The number of elements of `A` in `[1, n]`. -/
noncomputable def densityCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun m => m ∈ A)).card

/-- `A` has Schnirelmann density at least `δ`: every initial segment `[1,n]`
contains at least `δ n` elements of `A`. -/
def HasDensity (A : Set ℕ) (δ : ℚ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → δ * (n : ℚ) ≤ (densityCount A n : ℚ)

theorem hasDensity_le_one {A : Set ℕ} {δ : ℚ} (h : HasDensity A δ) : δ ≤ 1 := by
  have h1 := h 1 le_rfl
  have hc : densityCount A 1 ≤ 1 := by
    classical
    unfold densityCount
    have := Finset.card_le_card (Finset.filter_subset (fun m => m ∈ A) (Finset.Icc 1 1))
    simpa using this
  have : (densityCount A 1 : ℚ) ≤ 1 := by exact_mod_cast hc
  push_cast at h1
  linarith

/-! ## Closure of sums of `k`-th powers -/

theorem IsSumOfKthPowers.add {k n m s t : ℕ} (h1 : IsSumOfKthPowers k n s)
    (h2 : IsSumOfKthPowers k m t) : IsSumOfKthPowers k (n + m) (s + t) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  refine ⟨Fin.append f g, ?_⟩
  rw [Fin.sum_univ_add, hf, hg]
  simp

/-! ## The pigeonhole step -/

/-- Two sets whose Schnirelmann densities sum to more than `1` cover `ℕ` by sums. -/
theorem add_eq_univ_of_density {A B : Set ℕ} {α β : ℚ}
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hA : HasDensity A α) (hB : HasDensity B β)
    (hαβ : 1 < α + β) : ∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, a + b = n := by
  classical
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, hA0, 0, hB0, by simp⟩
  have hn1 : 1 ≤ n := hn
  by_contra hmem
  -- the three counting sets
  set s : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m ∈ A) with hs
  set u : Finset ℕ := (Finset.range n).filter (fun m => m ∈ B) with hu
  set t : Finset ℕ := (Finset.range n).filter (fun m => ¬ m ∈ B) with ht
  have hs_card : (s.card : ℚ) = (densityCount A n : ℚ) := by
    rw [hs]
    simp [densityCount]
  -- `a ↦ n - a` maps `s` into `t`
  have himage : s.image (fun a => n - a) ⊆ t := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, han⟩, haA⟩ := ha
    rw [ht, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro hbB
    exact hmem ⟨a, haA, n - a, hbB, by omega⟩
  have hinj : Set.InjOn (fun a => n - a) ↑s := by
    intro a ha b hb hab
    have hab' : n - a = n - b := hab
    rw [Finset.mem_coe] at ha hb
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at ha hb
    omega
  have hst : s.card ≤ t.card := by
    have h := Finset.card_le_card himage
    rwa [Finset.card_image_of_injOn hinj] at h
  -- `u` and `t` partition `range n`
  have hut : u.card + t.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun m => m ∈ B)
    rw [← hu, ← ht, Finset.card_range] at h
    omega
  -- `u` contains `0` together with all of `B ∩ [1, n-1]`
  have hinsert : insert 0 ((Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B)) ⊆ u := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rw [hu, Finset.mem_filter, Finset.mem_range]
    rcases hm with rfl | hm
    · exact ⟨by omega, hB0⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmn⟩, hmB⟩ := hm
      exact ⟨by omega, hmB⟩
  have h0not : (0 : ℕ) ∉ (Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B) := by
    intro h
    rw [Finset.mem_filter, Finset.mem_Icc] at h
    omega
  have hucard : densityCount B (n - 1) + 1 ≤ u.card := by
    have h := Finset.card_le_card hinsert
    rw [Finset.card_insert_of_notMem h0not] at h
    have hc : ((Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B)).card = densityCount B (n - 1) := by
      simp [densityCount]
    omega
  -- arithmetic
  have hAcard : α * (n : ℚ) ≤ (s.card : ℚ) := by
    rw [hs_card]
    exact hA n hn1
  have hBcard : β * ((n - 1 : ℕ) : ℚ) ≤ ((densityCount B (n - 1) : ℕ) : ℚ) := by
    rcases Nat.eq_or_lt_of_le hn1 with h1 | h1
    · have h0 : n - 1 = 0 := by omega
      rw [h0]
      simp [densityCount]
    · exact hB (n - 1) (by omega)
  have hnat : s.card + (densityCount B (n - 1) + 1) ≤ n := by omega
  have hnatq : (s.card : ℚ) + ((densityCount B (n - 1) : ℕ) : ℚ) + 1 ≤ (n : ℚ) := by
    exact_mod_cast hnat
  have hcast : (n : ℚ) = ((n - 1 : ℕ) : ℚ) + 1 := by
    rw [Nat.cast_sub hn1]
    ring
  have hβle : β ≤ 1 := hasDensity_le_one hB
  nlinarith [hAcard, hBcard, hαβ, hβle, hcast, hnatq]

/-! ## The Waring corollary -/

/-- **Density step.**  If more than half of all positive integers are sums of at
most `s` `k`-th powers, then every natural number is a sum of at most `2s`
`k`-th powers. -/
theorem isWaringBound_of_density {k s : ℕ} {δ : ℚ} (hδ : 1 / 2 < δ)
    (h : HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ) :
    IsWaringBound k (s + s) := by
  classical
  intro n
  have hzero : (0 : ℕ) ∈ {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} :=
    ⟨0, Nat.zero_le s, ⟨fun i => 0, by simp⟩⟩
  obtain ⟨a, ⟨ta, hta, ha⟩, b, ⟨tb, htb, hb⟩, hab⟩ :=
    add_eq_univ_of_density hzero hzero h h (by linarith) n
  refine ⟨ta + tb, by omega, ?_⟩
  rw [← hab]
  exact IsSumOfKthPowers.add ha hb

/-- Waring's theorem follows from the density statement of Linnik's proof. -/
theorem waringTheorem_of_density
    (h : ∀ k : ℕ, 0 < k → ∃ s : ℕ, ∃ δ : ℚ, 1 / 2 < δ ∧
      HasDensity {n : ℕ | ∃ t ≤ s, IsSumOfKthPowers k n t} δ) :
    WaringTheorem := by
  intro k hk
  obtain ⟨s, δ, hδ, hdens⟩ := h k hk
  exact ⟨s + s, isWaringBound_of_density hδ hdens⟩

end Waring
