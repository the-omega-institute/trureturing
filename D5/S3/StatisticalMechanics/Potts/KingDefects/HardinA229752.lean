/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward.structural_certificate
   digest: The registered width-five two-defect king recurrence. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (external open-problem-resolution)
result: proof_shape=content; consumers=none (external open-problem-resolution #30655)
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Forward
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Topology.QuandleMarkovColoring

/-! An exact-budget transfer proves the recurrence for every row index at least twelve. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229752
open TwoDefectStrips.Width5
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

attribute [local irreducible] Data.T initial terminal W cl

theorem result (n : ℕ) (hn : 12 ≤ n) :
    (KingTwoGrid.T n 5 : ℤ) = 9 * KingTwoGrid.T (n-1) 5 -
      33 * KingTwoGrid.T (n-2) 5 + 63 * KingTwoGrid.T (n-3) 5 -
      66 * KingTwoGrid.T (n-4) 5 + 36 * KingTwoGrid.T (n-5) 5 -
      8 * KingTwoGrid.T (n-6) 5 := by
  have labelled (m : ℕ) :
      (literalCount (q := 4) horizontal between 2 (m+1) : ℤ) =
      dotProduct initial ((Data.T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl
      Data.T initial terminal 2 (fun _ _ => rfl)
    · intro p d h
      exact Forward.structural_certificate.1 p ⟨d, by change d ≤ 2 ∧ _ at h; omega⟩ h
    · intro p d hp r hr
      change d ≤ 2 ∧ _ at hp
      change _ ≤ 2 ∧ _
      dsimp only [id]
      constructor <;> omega
    · exact Certificate.transition_counts
    · intro r hr
      change 2 - _ ≤ 2 ∧ _
      dsimp only [id]
      constructor <;> omega
    · exact Forward.structural_certificate.2.1
  have tab (i : Fin 12) : forward Data.T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact Forward.structural_certificate.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward Data.T initial i.val) Data.T = W i.succ
      change forward Data.T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (Forward.structural_certificate.2.2.1.2 i).symm
  have poly : forward Data.T initial (5+6) =
      ∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) •
        forward Data.T initial (5+j.val) := by
    rw [tab ⟨11, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward Data.T initial (5+j.val) = W ⟨5+j.val, by omega⟩
      from fun j => tab ⟨5+j.val, by omega⟩]
    exact Forward.structural_certificate.2.2.2
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((Data.T ^ m).mulVec terminal) =
        24 * (KingTwoGrid.T (m+1) 5 : ℤ) := by
    rw [← labelled, TwoDefectStrips.GridBridge.literal_bridge horizontal between]
    · rw [KingTwoGrid.labelled_eq_twentyFour (m+1) 5 (by omega) (by omega) (by omega)]
      push_cast
      rfl
    · intro r
      unfold bondDefects
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      change (∑ a ∈ Finset.univ.image (fun j : Fin 4 => (j.castSucc, j.succ)),
        if r a.1 = r a.2 then 1 else 0) = _
      rw [Finset.sum_image]
      · simp [-Finset.sum_boole, -Finset.sum_const, Fin.sum_univ_succ, KingGrid.lo, KingGrid.hi,
          D5.S3.Topology.QuandleMarkovColoring.leftSlot,
          D5.S3.Topology.QuandleMarkovColoring.rightSlot]
      · intro a ha b hb hab
        apply Fin.ext
        exact congrArg (fun x => x.1.val) hab
    · intro r t
      unfold bondDefects
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simp [between, -Finset.sum_boole, -Finset.sum_const, Fin.sum_univ_succ, KingGrid.lo, KingGrid.hi,
        D5.S3.Topology.QuandleMarkovColoring.leftSlot,
        D5.S3.Topology.QuandleMarkovColoring.rightSlot]
      omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := forward_shift Data.T initial terminal 6 5 ![-8,36,-66,63,-33,9] poly m
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h5 := bridge (m+5) (by omega)
  have h6 := bridge (m+6) (by omega)
  have h7 := bridge (m+7) (by omega)
  have h8 := bridge (m+8) (by omega)
  have h9 := bridge (m+9) (by omega)
  have h10 := bridge (m+10) (by omega)
  have h11 := bridge (m+11) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h5 h6 h7 h8 h9 h10 h11
  rw [h5, h6, h7, h8, h9, h10, h11] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  have e1 : 12+m-1 = m+11 := by omega
  have e2 : 12+m-2 = m+10 := by omega
  have e3 : 12+m-3 = m+9 := by omega
  have e4 : 12+m-4 = m+8 := by omega
  have e5 : 12+m-5 = m+7 := by omega
  have e6 : 12+m-6 = m+6 := by omega
  rw [e1,e2,e3,e4,e5,e6]
  have e0 : 12+m = m+12 := by omega
  rw [e0]
  linarith

end D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229752
