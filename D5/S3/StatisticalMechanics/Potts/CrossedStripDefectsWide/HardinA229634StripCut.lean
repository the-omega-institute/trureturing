/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.finite_certificate
   digest: Exact width-five two-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229634Strip.result)
zero_lower: proof_shape=bind-only; consumers=active_class, inherited_counts
active_class: proof_shape=bind-only; consumers=active_cut, inherited_counts
active_cut: proof_shape=bind-only; consumers=inherited_counts
inherited_counts: proof_shape=bind-only; consumers=HardinA229634Strip.finite_certificate
zero_cut: proof_shape=bind-only; consumers=HardinA229634StripClass0.transition_counts through HardinA229634StripClass5.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripCut
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229634StripData
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefects
open HardinA229531StripData (Row horizontal between)
private theorem zero_lower : ∀ r : Row, 20 ≤ (cl r 0).val := by decide +kernel

private theorem active_class (r : Row) (d : ℕ) (j : Fin 20) :
    (cl r d = j.castAdd 13) ↔
      0 < d ∧ HardinA229531StripData.cl r (d - 1) = j := by
  by_cases hd : 0 < d
  · rw [cl, if_pos hd]
    simp only [hd, true_and]
    constructor
    · intro h
      exact Fin.ext (congrArg (fun x : Fin 33 => x.val) h)
    · rintro rfl
      rfl
  · have dz : d = 0 := by omega
    subst d
    have hn : cl r 0 ≠ j.castAdd 13 := by
      intro h
      have hv := congrArg Fin.val h
      have hl := zero_lower r
      have hj := j.isLt
      simp only [Fin.val_castAdd] at hv
      omega
    simp only [hn, hd, false_and]

theorem active_cut (p r : Row) (d : Fin 3) (j : Fin 20) (hd : 0 < d.val) :
    ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 13) ↔
      bondDefects between p r + bondDefects horizontal r r ≤ d.val - 1 ∧
      HardinA229531StripData.cl r
        (d.val - 1 - (bondDefects between p r + bondDefects horizontal r r)) = j) := by
  rw [active_class]
  have he : d.val - (bondDefects between p r + bondDefects horizontal r r) - 1 =
      d.val - 1 - (bondDefects between p r + bondDefects horizontal r r) := by omega
  rw [he]
  constructor
  · rintro ⟨hc, hpos, hj⟩
    exact ⟨by omega, hj⟩
  · rintro ⟨hc, hj⟩
    exact ⟨by omega, by omega, hj⟩

theorem inherited_counts (p : Row) (d : Fin 3) (hp : Valid p d.val) (j : Fin 20) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 13
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 13) := by
  by_cases hd : 0 < d.val
  · simp_rw [active_cut p _ d j hd]
    have hv : HardinA229531StripData.Valid p (d.val - 1) := by
      dsimp only [Valid] at hp
      dsimp only [HardinA229531StripData.Valid]
      omega
    have ht := HardinA229531StripClasses.transition_counts p ⟨d.val - 1, by omega⟩ hv j
    have table : ∀ p (d : Fin 3) (j : Fin 20), 0 < d.val →
        HardinA229531StripData.T (HardinA229531StripData.cl p (d.val - 1)) j =
          T (cl p d.val) (j.castAdd 13) := by
      intro p d j hd
      rw [cl, if_pos hd]
      simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁]
      rfl
    exact ht.trans (table p d j hd)
  · have hzero : ∀ (r : Row) (c : ℕ) (j : Fin 20),
        ¬ (c ≤ 0 ∧ cl r (0 - c) = j.castAdd 13) := by
      intro r c j h
      have hh : cl r 0 = j.castAdd 13 := by simpa only [Nat.zero_sub] using h.2
      have hn := (active_class r 0 j).mp hh
      omega
    have dz : d.val = 0 := by omega
    simp_rw [dz, if_neg (hzero _ _ j)]
    have table : ∀ p (j : Fin 20), T (cl p 0) (j.castAdd 13) = 0 := by
      intro p j
      have hl := zero_lower p
      have hu := (cl p 0).isLt
      let k : Fin 13 := ⟨(cl p 0).val - 20, by omega⟩
      have he : cl p 0 = k.natAdd 20 := by
        apply Fin.ext
        dsimp [k]
        omega
      rw [he]
      simp only [T, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rfl
    simpa using (table p j).symm


theorem zero_cut (p r : Row) (j : Fin 6) :
    ((bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) =
        ⟨20 + j.val, by omega⟩) ↔
      bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
        HardinA229531StripData.cl r
          (0 - (bondDefects between p r + bondDefects horizontal r r)) =
            ⟨6 + j.val, by omega⟩) := by
  have h : ∀ (r : Row) (j : Fin 6),
      (cl r 0 = ⟨20 + j.val, by omega⟩ ↔
        HardinA229531StripData.cl r 0 = ⟨6 + j.val, by omega⟩) := by decide +kernel
  simp only [Nat.zero_sub, h]

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripCut
