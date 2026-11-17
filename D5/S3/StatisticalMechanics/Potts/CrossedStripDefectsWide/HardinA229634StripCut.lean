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
numeric_cut: proof_shape=bind-only; consumers=active_cut
active_cut: proof_shape=bind-only; consumers=inherited_counts
inherited_counts: proof_shape=bind-only; consumers=HardinA229634Strip.finite_certificate
zero_cut: proof_shape=bind-only; consumers=HardinA229634StripClass0.transition_counts through HardinA229634StripClass5.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripData
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
private theorem numeric_cut : ∀ (r : Row) (c d : Fin 3) (j : Fin 20),
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = j.castAdd 13) ↔
      c.val < d.val ∧ HardinA229531StripData.cl r (d.val - 1 - c.val) = j) := by
  intro r
  generalize h0 : r 0 = c0
  generalize h1 : r 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

theorem active_cut (p r : Row) (d : Fin 3) (j : Fin 20) (hd : 0 < d.val) :
    ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 13) ↔
      bondDefects between p r + bondDefects horizontal r r ≤ d.val - 1 ∧
      HardinA229531StripData.cl r
        (d.val - 1 - (bondDefects between p r + bondDefects horizontal r r)) = j) := by
  by_cases hc : bondDefects between p r + bondDefects horizontal r r < 3
  · rw [numeric_cut r ⟨_, hc⟩ d j]
    have hn : (bondDefects between p r + bondDefects horizontal r r < d.val) ↔
        bondDefects between p r + bondDefects horizontal r r ≤ d.val - 1 := by omega
    rw [hn]
  · have hn : ¬ (bondDefects between p r + bondDefects horizontal r r ≤ d.val) := by omega
    have hm : ¬ (bondDefects between p r + bondDefects horizontal r r ≤ d.val - 1) := by omega
    simp only [hn, hm, false_and]

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
          T (cl p d.val) (j.castAdd 13) := by decide +kernel
    exact ht.trans (table p d j hd)
  · have hzero : ∀ (r : Row) (c : ℕ) (j : Fin 20),
        ¬ (c ≤ 0 ∧ cl r (0 - c) = j.castAdd 13) := by
      intro r c j h
      have hn := numeric_cut r 0 0 j
      have hh : cl r 0 = j.castAdd 13 := by simpa using h.2
      have := hn.mp ⟨by omega, hh⟩
      omega
    have dz : d.val = 0 := by omega
    simp_rw [dz, if_neg (hzero _ _ j)]
    have table : ∀ p (j : Fin 20), T (cl p 0) (j.castAdd 13) = 0 := by decide +kernel
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
