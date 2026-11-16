/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Probe
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Probe
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-five exact-budget transfer measurement. -/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! A single output class of the canonical-boundary defect transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Probe
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
local instance (p : Row) : Decidable
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p) := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val →
 D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
 (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
 cl r (d.val-(bondDefects between p r+bondDefects horizontal r r)) = (0 : Fin 43) then (1 : ℤ) else 0) = T (cl p d.val) 0 := by
  let E : Row ≃ Fin (4^5) := finFunctionFinEquiv
  have h : ∀ i : Fin (4^5), ∀ d : Fin 3, Valid (E.symm i) d.val →
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical (E.symm i) →
      (∑ j : Fin (4^5), if
        bondDefects between (E.symm i) (E.symm j) +
          bondDefects horizontal (E.symm j) (E.symm j) ≤ d.val ∧
        cl (E.symm j) (d.val - (bondDefects between (E.symm i) (E.symm j) +
          bondDefects horizontal (E.symm j) (E.symm j))) = (0 : Fin 43)
        then (1 : ℤ) else 0) = T (cl (E.symm i) d.val) 0 := by
    decide +kernel
  intro p d hp hc
  rw [← E.symm.sum_comp]
  simpa only [E.symm_apply_apply] using h (E p) d (by simpa only [E.symm_apply_apply])
    (by simpa only [E.symm_apply_apply])
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Probe
