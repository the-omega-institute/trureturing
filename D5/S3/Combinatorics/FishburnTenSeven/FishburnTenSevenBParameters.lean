/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters
   mirror-E: none(waiver:dependent-normal-form-parameter-count)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Disjoint maximum and upper-endpoint splits count the second-class parameters. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliaryCounting
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenAuxiliary FishburnTenSevenAuxiliaryCounting

def BParameters (size : ℕ) :=
  Σ maximum : {maximum : ℕ // 1 ≤ maximum ∧ maximum ≤ size},
    HStart maximum.val ⊕
      (Σ low : {low : ℕ // 2 ≤ low ∧ low < maximum.val},
        Σ _high : {high : ℕ // low.val ≤ high ∧ high < maximum.val}, H (low.val - 2))

theorem BParameters_card (size : ℕ) (hsize : 1 ≤ size) :
    Finite (BParameters size) ∧ Nat.card (BParameters size) = 2 ^ size - size := by
  classical
  have hfiniteH (total : ℕ) : Finite (H total) := by
    have hf : ({p : List ℕ | p.Perm (List.range' 1 total) ∧ IsFishburn p ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] p} : Set (List ℕ)).Finite := by
      apply (List.finite_toSet (List.range' 1 total).permutations).subset
      intro p hp
      exact List.mem_permutations.mpr hp.1
    exact hf.to_subtype
  let (total : ℕ) : Finite (H total) := hfiniteH total
  let (total : ℕ) : Finite (HStart total) := by dsimp only [HStart]; infer_instance
  let (low high : ℕ) : Finite {value : ℕ // low ≤ value ∧ value < high} :=
    (Set.finite_Ico low high).to_subtype
  let (low high : ℕ) : Finite {value : ℕ // low ≤ value ∧ value ≤ high} :=
    (Set.finite_Icc low high).to_subtype
  let (low high : ℕ) : Fintype {value : ℕ // low ≤ value ∧ value < high} :=
    Fintype.ofFinite _
  let (low high : ℕ) : Fintype {value : ℕ // low ≤ value ∧ value ≤ high} :=
    Fintype.ofFinite _
  let Tail (maximum : ℕ) :=
    Σ low : {low : ℕ // 2 ≤ low ∧ low < maximum},
      Σ high : {high : ℕ // low.val ≤ high ∧ high < maximum}, H (low.val - 2)
  let Layer (maximum : ℕ) :=
    Σ low : {low : ℕ // 2 ≤ low ∧ low ≤ maximum}, H (low.val - 2)
  let Slice (maximum : ℕ) := HStart maximum ⊕ Tail maximum
  let (maximum : ℕ) : Finite (Tail maximum) := by
    dsimp only [Tail]
    infer_instance
  let (maximum : ℕ) : Finite (Layer maximum) := by
    dsimp only [Layer]
    infer_instance
  let (maximum : ℕ) : Finite (Slice maximum) := by
    dsimp only [Slice]
    infer_instance
  have hfinite (total : ℕ) : Finite (BParameters total) := by
    dsimp only [BParameters]
    infer_instance
  let (total : ℕ) : Finite (BParameters total) := hfinite total
  have htailSplit (maximum : ℕ) : Tail (maximum + 1) ≃ Tail maximum ⊕ Layer maximum := by
    refine
      { toFun := fun ⟨low, high, q⟩ =>
          if hh : high.val < maximum then
            Sum.inl ⟨⟨low.val, low.property.1, by
              have := high.property.1; omega⟩, ⟨high.val, high.property.1, hh⟩, q⟩
          else Sum.inr ⟨⟨low.val, low.property.1, by
            have := low.property.2; omega⟩, q⟩
        invFun := fun data => match data with
          | Sum.inl ⟨low, high, q⟩ =>
            ⟨⟨low.val, low.property.1, by have := low.property.2; omega⟩,
              ⟨high.val, high.property.1, by have := high.property.2; omega⟩, q⟩
          | Sum.inr ⟨low, q⟩ =>
            ⟨⟨low.val, low.property.1, by have := low.property.2; omega⟩,
              ⟨maximum, low.property.2, by omega⟩, q⟩
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨⟨low, hl⟩, ⟨⟨high, hh⟩, q⟩⟩
      dsimp only
      by_cases hlt : high < maximum
      · simp only [hlt, ↓reduceDIte]
      · have he : high = maximum := by omega
        subst high
        simp only [lt_self_iff_false, ↓reduceDIte]
    · rintro (⟨⟨low, hl⟩, ⟨⟨high, hh⟩, q⟩⟩ | ⟨⟨low, hl⟩, q⟩)
      · dsimp only
        simp only [hh.2, ↓reduceDIte]
      · dsimp only
        simp only [lt_self_iff_false, ↓reduceDIte]
  have hlayerCard (maximum : ℕ) (hm : 2 ≤ maximum) :
      Nat.card (Layer maximum) = Nat.card (H (maximum - 1)) := by
    let index : {low : ℕ // 2 ≤ low ∧ low ≤ maximum} ≃ Fin (maximum - 1) :=
      { toFun := fun low => ⟨maximum - low.val, by have := low.property; omega⟩
        invFun := fun cut => ⟨maximum - cut.val, by have := cut.is_lt; omega⟩
        left_inv := by
          intro low
          apply Subtype.ext
          dsimp only
          have := low.property
          omega
        right_inv := by
          intro cut
          apply Fin.ext
          dsimp only
          have := cut.is_lt
          omega }
    change Nat.card (Σ low : {low : ℕ // 2 ≤ low ∧ low ≤ maximum}, H (low.val - 2)) =
      Nat.card (H (maximum - 1))
    rw [Nat.card_sigma]
    conv_rhs =>
      rw [Nat.card_congr (H_maximum_equiv (maximum - 1) (by omega)), Nat.card_sigma]
    apply Fintype.sum_equiv index
    intro low
    have he : maximum - 1 - (maximum - low.val) - 1 = low.val - 2 := by
      have := low.property
      omega
    change Nat.card (H (low.val - 2)) =
      Nat.card (H (maximum - 1 - (maximum - low.val) - 1))
    rw [he]
  have hmaximumSplit (total : ℕ) :
      BParameters (total + 1) ≃ BParameters total ⊕ Slice (total + 1) := by
    refine
      { toFun := fun ⟨maximum, data⟩ =>
          if hm : maximum.val ≤ total then
            Sum.inl ⟨⟨maximum.val, maximum.property.1, hm⟩, data⟩
          else Sum.inr (cast (congrArg Slice (by
            have := maximum.property; omega : maximum.val = total + 1)) data)
        invFun := fun data => match data with
          | Sum.inl ⟨maximum, body⟩ =>
            ⟨⟨maximum.val, maximum.property.1, by
              have := maximum.property.2; omega⟩, body⟩
          | Sum.inr body => ⟨⟨total + 1, by omega, by omega⟩, body⟩
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨⟨maximum, hm⟩, body⟩
      dsimp only
      by_cases hle : maximum ≤ total
      · simp only [hle, ↓reduceDIte]
        rfl
      · have he : maximum = total + 1 := by omega
        subst maximum
        simp only [Nat.not_succ_le_self, ↓reduceDIte, cast_eq]
        rfl
    · rintro (⟨⟨maximum, hm⟩, body⟩ | body)
      · dsimp only
        simp only [hm.2, ↓reduceDIte]
      · dsimp only
        simp only [Nat.not_succ_le_self, ↓reduceDIte, cast_eq]
  have htailSmall (maximum : ℕ) (hm : maximum ≤ 2) : Nat.card (Tail maximum) = 0 := by
    let : IsEmpty (Tail maximum) := ⟨fun data => by have := data.1.property; omega⟩
    simp
  have hsliceOne : Nat.card (Slice 1) = 1 := by
    change Nat.card (HStart 1 ⊕ Tail 1) = 1
    rw [Nat.card_sum, H_start_one_card 1 (by omega), htailSmall 1 (by omega)]
    simp
  have hslice (index : ℕ) : Nat.card (Slice (index + 2)) + 1 = 2 ^ (index + 1) := by
    induction index with
    | zero =>
        change Nat.card (HStart 2 ⊕ Tail 2) + 1 = 2 ^ 1
        rw [Nat.card_sum, H_start_one_card 2 (by omega), htailSmall 2 (by omega)]
        norm_num
    | succ index ih =>
        have htailCount : Nat.card (Tail (index + 3)) =
            Nat.card (Tail (index + 2)) + 2 ^ index := by
          have htail := Nat.card_congr (htailSplit (index + 2))
          rw [Nat.card_sum, hlayerCard (index + 2) (by omega)] at htail
          change Nat.card (Tail (index + 3)) =
            Nat.card (Tail (index + 2)) + Nat.card (H (index + 1)) at htail
          rw [H_card] at htail
          simpa [show index + 1 ≠ 0 by omega] using htail
        have hpreviousOne : Nat.card (HStart (index + 2)) = 2 ^ index := by
          simpa [show index + 2 ≠ 1 by omega] using
            H_start_one_card (index + 2) (by omega)
        have hnextOne : Nat.card (HStart (index + 3)) = 2 ^ (index + 1) := by
          have he : index + 3 - 2 = index + 1 := by omega
          simpa [show index + 3 ≠ 1 by omega, he] using
            H_start_one_card (index + 3) (by omega)
        have hprevious : Nat.card (Slice (index + 2)) =
            Nat.card (HStart (index + 2)) + Nat.card (Tail (index + 2)) := Nat.card_sum
        have hnext : Nat.card (Slice (index + 3)) =
            Nat.card (HStart (index + 3)) + Nat.card (Tail (index + 3)) := Nat.card_sum
        rw [hpreviousOne] at hprevious
        rw [hnextOne, htailCount] at hnext
        change Nat.card (Slice (index + 3)) + 1 = 2 ^ (index + 2)
        rw [pow_succ]
        omega
  have hzero : Nat.card (BParameters 0) = 0 := by
    let : IsEmpty (BParameters 0) := ⟨fun data => by have := data.1.property; omega⟩
    simp
  have hone : Nat.card (BParameters 1) = 1 := by
    rw [Nat.card_congr (hmaximumSplit 0), Nat.card_sum, hzero, hsliceOne]
  have htotal (index : ℕ) : Nat.card (BParameters (index + 1)) + (index + 1) =
      2 ^ (index + 1) := by
    induction index with
    | zero => simp [hone]
    | succ index ih =>
        have hstep := Nat.card_congr (hmaximumSplit (index + 1))
        rw [Nat.card_sum] at hstep
        change Nat.card (BParameters (index + 2)) =
          Nat.card (BParameters (index + 1)) + Nat.card (Slice (index + 2)) at hstep
        have hsliceStep := hslice index
        change Nat.card (BParameters (index + 2)) + (index + 2) = 2 ^ (index + 2)
        rw [pow_succ]
        omega
  refine ⟨hfinite size, ?_⟩
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  change Nat.card (BParameters (index + 1)) = 2 ^ (index + 1) - (index + 1)
  have := htotal index
  omega

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters
