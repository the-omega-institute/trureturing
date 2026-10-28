/- GID: D5/S3/Combinatorics/Circle/MixedDyadicAugmentation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/MixedDyadicAugmentation
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: At most two fresh physical labels strictly augment arbitrary legal dyadic reset words. -/
module
public import D5.S3.Combinatorics.Circle.DyadicResetSource
public import D5.S3.Combinatorics.Circle.DyadicResetBlocks
public import D5.S3.Combinatorics.Circle.DyadicResetAllocation

/-! Mixed insertion uses physical permutation balances and the original lexicographic objective. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open DyadicResetSource DyadicResetBlocks DyadicResetAllocation
open scoped BigOperators

private theorem descent_of_perm {k t : ℕ} (W V I R : List (Fin k))
    (hW : W.Nodup) (hI : I.Nodup) (hIW : ∀ a ∈ I, a ∉ W)
    (hR : ∀ a ∈ R, a ∈ W) (hRS : ∀ a ∈ R, ¬ Large k t a)
    (hperm : (V ++ R).Perm (W ++ I))
    (hgain : 0 < largeUsed k t I ∨
      (R.length < I.length ∧ ∀ a ∈ I, ¬ Large k t a)) :
    V.Nodup ∧ J k t V < J k t W ∧
      I.toFinset = V.toFinset \ W.toFinset ∧
      R.toFinset = W.toFinset \ V.toFinset := by
  classical
  have hWI : (W ++ I).Nodup := hW.append hI (List.disjoint_left.mpr (by
    intro a ha hi; exact hIW a hi ha))
  obtain ⟨hV, hRn, hVR⟩ := List.nodup_append'.mp (hperm.nodup_iff.mpr hWI)
  have hvR : ∀ a ∈ V, a ∉ R := fun a ha => List.disjoint_left.mp hVR ha
  have hm (a : Fin k) : (a ∈ V ∨ a ∈ R) ↔ (a ∈ W ∨ a ∈ I) := by
    simpa only [List.mem_append] using hperm.mem_iff (a := a)
  have hsets : I.toFinset = V.toFinset \ W.toFinset ∧
      R.toFinset = W.toFinset \ V.toFinset := by
    constructor <;> ext a
    all_goals
      have h1 := hm a
      have h2 := hvR a
      have h3 := hIW a
      have h4 := hR a
      simp only [List.mem_toFinset, Finset.mem_sdiff]
      tauto
  have hmass {β : Type} [AddCommMonoid β] (w : Fin k → β) :
      mass w V + mass w R = mass w W + mass w I := by
    simpa [mass] using (hperm.map w).sum_eq
  have hRzero : largeUsed k t R = 0 := by
    simp only [largeUsed, mass]
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    simp [largeWeight, hRS a ha]
  have hwg := physical_balance (largeWeight k t) W hW
  have hvg := physical_balance (largeWeight k t) V hV
  have hlg := hmass (largeWeight k t)
  change G k t W + largeUsed k t W = _ at hwg
  change G k t V + largeUsed k t V = _ at hvg
  change largeUsed k t V + largeUsed k t R = largeUsed k t W + largeUsed k t I at hlg
  have hG : G k t V + largeUsed k t I = G k t W := by omega
  have hwc : U W + W.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) W hW
  have hvc : U V + V.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) V hV
  have hlen := hperm.length_eq
  simp only [List.length_append] at hlen
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases hgain with hg | ⟨hu, hIS⟩
    · exact Or.inl (by omega)
    · have hIZ : largeUsed k t I = 0 := by
        simp only [largeUsed, mass]
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        simp [largeWeight, hIS a ha]
      have hezero (L : List (Fin k)) (hL : ∀ a ∈ L, ¬ Large k t a) : H k t L = 0 := by
        simp only [H, mass]
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        simp [energyWeight, hL a ha]
      have he := hmass (energyWeight k t)
      change H k t V + H k t R = H k t W + H k t I at he
      rw [hezero R hRS, hezero I hIS] at he
      refine Or.inr ⟨by omega, ?_⟩
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inr ⟨by omega, by omega⟩
  exact ⟨hV, hJ, hsets⟩

end D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
