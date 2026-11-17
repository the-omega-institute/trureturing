/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftWord
   generality: I
   mirror-B: none(waiver:consumed-by-eight-bit-physical-lift)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftPrefix

/-! # Literal physical blocks and their inventory -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShorteningArithmetic

def physicalBlock {k : ℕ} (orientation : Fin 8 → Bool)
    (j : Fin (k + 1)) : List (Fin (k + 9)) :=
  if hj : j.val < 8 then
    if orientation ⟨j.val, hj⟩ then
      [liftOldLabel j, liftNewLabel ⟨j.val, hj⟩]
    else [liftNewLabel ⟨j.val, hj⟩, liftOldLabel j]
  else [liftOldLabel j]

theorem target_full_old_rows (k : ℕ) (hk : 8 ≤ k) (j : Fin (k + 1)) :
    fullFirst (k + 8) (liftOldLabel j) =
      256 * fullFirst k j - 255 * fullCharge k j ∧
    fullCharge (k + 8) (liftOldLabel j) = fullCharge k j ∧
    earIndicator (liftOldLabel j) = earIndicator j ∧
    actualSource (k + 9) 170 (liftOldLabel j) =
      256 * actualSource (k + 1) 170 j - 255 * fullCharge k j -
        21675 * earIndicator j := by
  have hfc : fullFirst (k + 8) (liftOldLabel j) =
        256 * fullFirst k j - 255 * fullCharge k j ∧
      fullCharge (k + 8) (liftOldLabel j) = fullCharge k j ∧
      earIndicator (liftOldLabel j) = earIndicator j := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have he : liftOldLabel (Fin.last k) = Fin.last (k + 8) := by
        apply Fin.ext; simp [liftOldLabel]
      simp [he, fullFirst, fullCharge, earIndicator]
    · have he : liftOldLabel i.castSucc =
          (⟨i.val + 8, by omega⟩ : Fin (k + 8)).castSucc := rfl
      simp only [he, fullFirst, fullCharge, Fin.lastCases_castSucc]
      refine ⟨target_old_first_row k hk i, charge_shift_eight k i, ?_⟩
      simp [earIndicator, ne_of_lt i.isLt, show i.val + 8 ≠ k + 8 by omega]
  refine ⟨hfc.1, hfc.2.1, hfc.2.2, ?_⟩
  have hs := (full_source_rows (k + 8) (by omega) (liftOldLabel j)).2.2
  have hb := (full_source_rows k hk j).2.2
  change actualSource (k + 9) 170 (liftOldLabel j) = _ at hs
  rw [hs, hfc.1, hfc.2.1, hfc.2.2, hb]
  ring

theorem target_full_new_rows (k : ℕ) (hk : 8 ≤ k) (i : Fin 8) :
    fullFirst (k + 8) (liftNewLabel i) = 85 * (2 : ℤ) ^ i.val ∧
    actualSource (k + 9) 170 (liftNewLabel i) = 170 * (2 : ℤ) ^ i.val := by
  have he : liftNewLabel (k := k) i =
      (⟨i.val, by omega⟩ : Fin (k + 8)).castSucc := rfl
  constructor
  · rw [he]
    simp only [fullFirst, Fin.lastCases_castSucc]
    exact target_new_first_row k hk i
  · exact target_new_second_row k hk i

theorem physical_block_sums (k : ℕ) (hk : 8 ≤ k)
    (orientation : Fin 8 → Bool) (j : Fin (k + 1)) :
    ((physicalBlock orientation j).map (fullFirst (k + 8))).sum =
      256 * fullFirst k j - 255 * fullCharge k j + 85 * lowWeight j ∧
    ((physicalBlock orientation j).map (actualSource (k + 9) 170)).sum =
      256 * actualSource (k + 1) 170 j - 255 * fullCharge k j -
        21675 * earIndicator j + 170 * lowWeight j := by
  have hold := target_full_old_rows k hk j
  by_cases hj : j.val < 8
  · have hnew := target_full_new_rows k hk ⟨j.val, hj⟩
    unfold physicalBlock
    rw [dif_pos hj]
    split_ifs <;> simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hold.1, hold.2.2.2, hnew.1, hnew.2,
      lowWeight, if_pos hj, Fin.val_mk] <;> simp [add_comm]
  · simp [physicalBlock, hj, lowWeight, hold.1, hold.2.2.2]

theorem physical_word_sums (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (orientation : Fin 8 → Bool) :
    ((physicalLiftWord w orientation).map (fullFirst (k + 8))).sum = firstState w ∧
    ((physicalLiftWord w orientation).map (actualSource (k + 9) 170)).sum = secondState w := by
  induction w with
  | nil => simp [physicalLiftWord, firstState, secondState]
  | cons j w ih =>
      change (((physicalBlock orientation j) ++ physicalLiftWord w orientation).map _).sum = _ ∧
        (((physicalBlock orientation j) ++ physicalLiftWord w orientation).map _).sum = _
      simp only [List.map_append, List.sum_append, ih.1, ih.2]
      rw [(physical_block_sums k hk orientation j).1,
        (physical_block_sums k hk orientation j).2]
      simp only [firstState, secondState, List.map_cons, List.sum_cons]
      constructor <;> ring

theorem physical_block_mem (k : ℕ) (orientation : Fin 8 → Bool)
    (j : Fin (k + 1)) (x : Fin (k + 9)) :
    x ∈ physicalBlock orientation j ↔
      x = liftOldLabel j ∨ (j.val < 8 ∧ x.val = j.val) := by
  by_cases hj : j.val < 8
  · have he : x = liftNewLabel (k := k) ⟨j.val, hj⟩ ↔ x.val = j.val := by
      constructor
      · intro h; exact congrArg Fin.val h
      · intro h; apply Fin.ext; exact h
    simp only [physicalBlock, dif_pos hj]
    split_ifs <;> simp [he, hj, or_comm]
  · simp [physicalBlock, hj]

theorem physical_inventory (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (hw : w.Perm (List.finRange (k + 1)))
    (orientation : Fin 8 → Bool) :
    (physicalLiftWord w orientation).Perm (List.finRange (k + 9)) := by
  have hnd : (physicalLiftWord w orientation).Nodup := by
    change (w.flatMap (physicalBlock orientation)).Nodup
    refine List.nodup_flatMap.mpr ⟨?_,
      (hw.nodup_iff.mpr (List.nodup_finRange _)).imp ?_⟩
    · intro j _
      unfold physicalBlock
      split_ifs <;> simp [liftOldLabel, liftNewLabel, Fin.ext_iff]
    · intro i j hij
      apply List.disjoint_left.mpr
      intro x hxi hxj
      rw [physical_block_mem] at hxi hxj
      rcases hxi with rfl | ⟨hi, hxi⟩ <;> rcases hxj with h | ⟨hj, hxj⟩
      · apply hij
        apply Fin.ext
        have h := congrArg Fin.val h
        simp only [liftOldLabel, Fin.val_mk] at h
        omega
      · simp only [liftOldLabel, Fin.val_mk] at hxj
        omega
      · have he := congrArg Fin.val h
        simp only [liftOldLabel, Fin.val_mk] at he
        omega
      · apply hij
        exact Fin.ext (by omega)
  apply (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange _)).mpr
  intro x
  simp only [List.mem_finRange, iff_true]
  change x ∈ w.flatMap (physicalBlock orientation)
  rw [List.mem_flatMap]
  by_cases hx : x.val < 8
  · let j : Fin (k + 1) := ⟨x.val, by omega⟩
    refine ⟨j, hw.mem_iff.mpr (List.mem_finRange j), ?_⟩
    exact (physical_block_mem k orientation j x).mpr (Or.inr ⟨hx, rfl⟩)
  · let j : Fin (k + 1) := ⟨x.val - 8, by omega⟩
    refine ⟨j, hw.mem_iff.mpr (List.mem_finRange j), ?_⟩
    apply (physical_block_mem k orientation j x).mpr
    left
    apply Fin.ext
    dsimp [liftOldLabel, j]
    omega

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
