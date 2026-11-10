/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionInventory
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic block membership and target inventory for resonant insertion. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionSchedule

/-! # Generic target inventory -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport

theorem resonant_block_mem {k ell : ℕ} (orientation : Fin ell → Bool)
    (j : Fin (k + 1)) (x : Fin (k + ell + 1)) :
    x ∈ resonantBlock orientation j ↔
      x = liftOldLabel j ∨ (j.val < ell ∧ x.val = j.val) := by
  by_cases hj : j.val < ell
  · have he : x = liftNewLabel (k := k) (ell := ell) ⟨j.val, hj⟩ ↔ x.val = j.val := by
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        apply Fin.ext
        exact h
    simp only [resonantBlock, dif_pos hj]
    split_ifs <;> simp [he, hj, or_comm]
  · simp [resonantBlock, hj]

theorem resonant_inventory {k ell : ℕ}
    (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) (hword : word.Perm (List.finRange (k + 1)))
    (orientation : Fin ell → Bool) :
    (resonantLiftWord word orientation).Perm (List.finRange (k + ell + 1)) := by
  have hnd : (resonantLiftWord word orientation).Nodup := by
    change (word.flatMap (resonantBlock orientation)).Nodup
    refine List.nodup_flatMap.mpr ⟨?_, (hword.nodup_iff.mpr (List.nodup_finRange _)).imp ?_⟩
    · intro j _
      by_cases hj : j.val < ell
      · let i : Fin ell := ⟨j.val, hj⟩
        have hell : 1 ≤ ell := by omega
        have hne : ell ≠ 0 := by omega
        by_cases ho : orientation i
        · simp [resonantBlock, hj, ho, hne, liftOldLabel, liftNewLabel, i, Fin.ext_iff]
        · simp [resonantBlock, hj, ho, hne, liftOldLabel, liftNewLabel, i, Fin.ext_iff]
      · simp [resonantBlock, hj, liftOldLabel, liftNewLabel, Fin.ext_iff]
    · intro i j hij
      apply List.disjoint_left.mpr
      intro x hxi hxj
      rw [resonant_block_mem] at hxi hxj
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
  change x ∈ word.flatMap (resonantBlock orientation)
  rw [List.mem_flatMap]
  by_cases hx : x.val < ell
  · let j : Fin (k + 1) := ⟨x.val, by omega⟩
    refine ⟨j, hword.mem_iff.mpr (List.mem_finRange j), ?_⟩
    exact (resonant_block_mem orientation j x).mpr (Or.inr ⟨hx, rfl⟩)
  · let j : Fin (k + 1) := ⟨x.val - ell, by omega⟩
    refine ⟨j, hword.mem_iff.mpr (List.mem_finRange j), ?_⟩
    apply (resonant_block_mem orientation j x).mpr
    left
    apply Fin.ext
    dsimp [liftOldLabel, j]
    omega

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
