/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelve
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelve
   mirror-E: none(waiver:egge-conjecture-ten-twelve)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Prod, mathlib/module/Mathlib.Data.Fintype.Option]
   utility: none
   digest: Last-zero histories prove Egge's Fishburn and classical equality at every size. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelveLastZero
import D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalCount
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelve

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnClassicalDefs
open FishburnBasicInsertion FishburnBasic1243 FishburnBasicPatterns
open FishburnTenTwelveStructure FishburnTenTwelveSuccession FishburnTenTwelvePaths
open FishburnTenTwelveCodes FishburnTenTwelveLastZero FishburnTenNineClassicalCount

theorem result : FishburnClassicalDefs.claim1012 := by
  classical
  have hprepend (size : ℕ) (word : List ℕ)
      (hp : word ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]]) :
      (size + 1) :: word ∈ avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] := by
    have hmax : ∀ value ∈ word, value < size + 1 := by
      intro value hm
      have hr := hp.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hr
      obtain ⟨offset, hb, heq⟩ := hr
      omega
    refine ⟨?_, ?_, ?_⟩
    · apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    · apply (isFishburn_insertIdx_max_iff word (size + 1) 0 (by omega) hmax).mpr
      exact ⟨hp.2.1, by intro before later heq; omega⟩
    · intro pattern hpattern hocc
      have hc : pattern = [1, 2, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · have ht := (maximum_1243_test size word hp.1 0 (by omega)).mp hocc
        rcases ht with hold | ⟨_, second, _, _, hb, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
      · have ht := ((maximum_pattern_tests size word hp.1 0 (by omega)).2.1).mp hocc
        rcases ht with hold | ⟨_, _, third, _, _, hb, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
  have hpathCode (size steps : ℕ)
      (base : avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]]) :
      Nonempty (PositiveHistory (size + 1) ((size + 1) :: base.val) steps ≃
        Option {pair : Fin steps × Fin steps // pair.1 < pair.2}) := by
    let start := (size + 1) :: base.val
    have hstart : start ∈ avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] :=
      hprepend size base.val base.property
    obtain ⟨first, extra, hf, hfe, hextent, hone, hcuts, hmaximum⟩ :=
      four_state_structure (size + 1) (by omega) start hstart
    have heq : extra = first := by
      by_contra hne
      have hlt : first < extra := by omega
      obtain ⟨maximum, hmfirst, hmextra, hmvalue⟩ := hmaximum hlt
      have hnodup : start.Nodup := hstart.1.nodup_iff.mpr (List.nodup_range' 1)
      have hzero : start.getD 0 0 = size + 1 := rfl
      have hindex := (List.getD_inj (by omega) (by omega) hnodup).mp
        (hmvalue.trans hzero.symm)
      omega
    have hmaxleft : ∃ maximum < first, start.getD maximum 0 = size + 1 := ⟨0, hf, rfl⟩
    have hlabel : label (size + 1) start first extra = .A := by
      rw [heq]
      simp only [label, if_neg (lt_irrefl first), if_pos hmaxleft]
    obtain ⟨historyCode⟩ := positive_history_walk steps (size + 1) start (by omega)
      hstart first extra hf hfe hextent hone hcuts hmaximum
    rw [hlabel] at historyCode
    obtain ⟨_, _, _, stateCode⟩ := walk_codes steps
    exact ⟨historyCode.trans stateCode⟩
  have hcodeCard (steps : ℕ) :
      Nat.card (Option {pair : Fin steps × Fin steps // pair.1 < pair.2}) =
        1 + steps.choose 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype,
      Fintype.card_product_filter_lt]
    simp only [Fintype.card_fin]
    omega
  have hfinite (size : ℕ) : (avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]]).Finite := by
    apply (List.finite_toSet (List.range' 1 size).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  have hrecurrence (size : ℕ) :
      (avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]).ncard =
        ∑ cut ∈ Finset.range (size + 1),
          (avoiders cut [[1, 2, 4, 3], [3, 1, 2, 4]]).ncard *
            (1 + (size - cut).choose 2) := by
    let (cut : Fin (size + 1)) : Finite
        (avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) := (hfinite _).to_subtype
    let (cut : Fin (size + 1)) : Fintype
        (avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) := Fintype.ofFinite _
    let (cut : Fin (size + 1)) (base : avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) :
        Finite (PositiveHistory (cut.val + 1) ((cut.val + 1) :: base.val)
          (size - cut.val)) :=
      Finite.of_equiv (Option {pair : Fin (size - cut.val) × Fin (size - cut.val) //
        pair.1 < pair.2}) (Classical.choice (hpathCode cut.val (size - cut.val) base)).symm
    have hcard := Nat.card_congr (Classical.choice (last_zero_bijection size))
    rw [Nat.card_sigma] at hcard
    rw [← Nat.card_coe_set_eq, ← hcard]
    simp only [Nat.card_sigma]
    have hpathCard (cut : Fin (size + 1))
        (base : avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) :
        Nat.card (PositiveHistory (cut.val + 1) ((cut.val + 1) :: base.val)
          (size - cut.val)) = 1 + (size - cut.val).choose 2 := by
      rw [Nat.card_congr (Classical.choice (hpathCode cut.val (size - cut.val) base)),
        hcodeCard]
    simp only [hpathCard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact Fin.sum_univ_eq_sum_range (fun cut =>
      (avoiders cut [[1, 2, 4, 3], [3, 1, 2, 4]]).ncard *
        (1 + (size - cut).choose 2)) (size + 1)
  have hzero : (avoiders 0 [[1, 2, 4, 3], [3, 1, 2, 4]]).ncard =
      (classicalAvoiders 0 [[2, 3, 1], [4, 1, 2, 3]]).ncard := by
    apply congrArg Set.ncard
    ext p
    constructor
    · intro hp
      have heq : p = [] := List.perm_nil.mp hp.1
      subst p
      refine ⟨by simp, ?_⟩
      intro pattern hpattern hocc
      obtain ⟨_, _, _, hsub, _⟩ := hocc
      have hlen := hsub.length_le
      have hc : pattern = [2, 3, 1] ∨ pattern = [4, 1, 2, 3] := by
        simpa using hpattern
      rcases hc with rfl | rfl <;> simp at hlen
    · intro hp
      have heq : p = [] := List.perm_nil.mp hp.1
      subst p
      refine ⟨by simp, ?_, ?_⟩
      · intro first later horder hbound
        simp at hbound
      · intro pattern hpattern hocc
        obtain ⟨_, _, _, hsub, _⟩ := hocc
        have hlen := hsub.length_le
        have hc : pattern = [1, 2, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
          simpa using hpattern
        rcases hc with rfl | rfl <;> simp at hlen
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
    cases size with
    | zero => exact hzero
    | succ size =>
      rw [hrecurrence size, classical_count_recurrence size]
      apply Finset.sum_congr rfl
      intro cut hcut
      have hb := Finset.mem_range.mp hcut
      rw [ih cut (by omega)]

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelve
