/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripLastCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripLastCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
last_class: proof_shape=bind-only; consumers=transition_counts
zero_crossing: proof_shape=bind-only; consumers=zero_table
zero_table: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=TwoDefects.Last.HardinA229604StripClass16 through HardinA229604StripClass26
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Target classes with two horizontal defects require at least two available defects. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
open HardinA229604StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem last_class (r : Row) (d : ℕ) (j : Fin 22)
    (hc : cl r d = j.natAdd 74) : 2 ≤ bondDefects horizontal r r := by
  by_contra hn
  have hr : bondDefects horizontal r r ≤ 1 := by omega
  by_cases hd : 0 < d
  · have he : cl r d = (HardinA229457StripData.cl r (d - 1)).castAdd 54 := by
      rw [cl, if_pos hd]
    rw [he] at hc
    have h := congrArg Fin.val hc
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    have := (HardinA229457StripData.cl r (d - 1)).isLt
    omega
  · have h := congrArg Fin.val hc
    simp only [cl, if_neg hd, if_pos hr, Fin.val_mk, Fin.val_natAdd] at h
    have := (HardinA229457StripData.cl r 0).isLt
    omega
private theorem zero_crossing : ∀ (i : Fin 32) (j : Fin 22),
    T ((i.natAdd 10).castAdd 54) (j.natAdd 74) = 0 := by
  decide +kernel
private theorem zero_table : ∀ p : Row, ∀ d : Fin 3, d.val < 2 →
    ∀ j : Fin 22, T (cl p d.val) (j.natAdd 74) = 0 := by
  intro p d hd j
  have hz : d.val = 0 ∨ d.val = 1 := by omega
  rcases hz with hz | hz
  · rw [hz]
    have hi : ¬ (cl p 0).val < 42 := by
      intro hs
      let i : Fin 42 := ⟨(cl p 0).val, hs⟩
      have hc : cl p 0 = i.castAdd 54 := by apply Fin.ext; rfl
      have h := HardinA229604StripCut.active_cut p 1 1 i (by decide)
      have hb := h.mp ⟨by decide, by simpa only [Fin.val_one, Nat.sub_self] using hc⟩
      have : (1 : ℕ) ≤ 0 := by simpa only [Fin.val_one, Nat.sub_self] using hb.1
      omega
    have hj0 : ¬ (j.natAdd 74).val < 42 := by dsimp; omega
    have hj1 : ¬ (j.natAdd 74).val < 74 := by dsimp; omega
    have hj2 : ¬ (j.natAdd 74).val < 52 := by dsimp; omega
    simp only [T, hi, hj0, hj1, hj2, ↓reduceDIte]
    split_ifs <;> rfl
  · rw [hz, cl, if_pos (by decide : 0 < 1)]
    have hlo : ∀ r : Row, 10 ≤ (HardinA229457StripData.cl r 0).val := by decide +kernel
    have hl := hlo p
    let i : Fin 32 := ⟨(HardinA229457StripData.cl p 0).val - 10, by
      have := (HardinA229457StripData.cl p 0).isLt
      omega⟩
    have he : (HardinA229457StripData.cl p (1 - 1)).castAdd 54 =
        (i.natAdd 10).castAdd 54 := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [he]
    exact zero_crossing i j

theorem transition_counts (j : Fin 22) : ∀ p : Row, ∀ d : Fin 3, d.val < 2 →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.natAdd 74
      then (1 : ℤ) else 0) = T (cl p d.val) (j.natAdd 74) := by
  intro p d hd
  rw [zero_table p d hd j]
  apply Finset.sum_eq_zero
  intro r _
  apply if_neg
  intro h
  have hr := last_class r _ j h.2
  omega

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
