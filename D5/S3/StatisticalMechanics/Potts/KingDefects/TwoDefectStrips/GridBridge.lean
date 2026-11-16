/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Row-list bond sums for the literal king grid. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229752.result)
defects_rows: proof_shape=content; consumers=literal_bridge
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid

/-! Row-list costs split into horizontal and between-row sums. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

theorem defects_rows {q k : ℕ} (H V : Finset (Fin k × Fin k)) (n : ℕ)
    (f : Fin (n + 1) → Row q k) :
    defects H V (List.ofFn f) =
      (∑ i, bondDefects H (f i) (f i)) +
      ∑ i : Fin n, bondDefects V (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ, defects, tailDefects]
  | succ n ih =>
    have h := ih (Fin.tail f)
    rw [List.ofFn_succ, List.ofFn_succ] at h ⊢
    simp only [defects, tailDefects] at h ⊢
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.tail, Fin.succ_zero_eq_one] at h ⊢
    omega

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
