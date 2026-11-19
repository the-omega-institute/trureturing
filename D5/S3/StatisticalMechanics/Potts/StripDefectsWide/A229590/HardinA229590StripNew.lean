/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripNew
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate
   digest: The one-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229590Strip.result)
cross_relabel: proof_shape=bind-only; consumers=quotient_rows
representative_rows: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=HardinA229590StripCut.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData

/-! Exact five-row one-defect class transfers and suffix counts. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripNew
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open HardinA229590StripData
set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem cross_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    cross (relabel e a) (column (relabel e b)) = cross a (column b) := by
  simp only [cross, bondDefects, column_relabel, e.injective.eq_iff]

set_option maxHeartbeats 0 in
private theorem representative_rows : ∀ i s : Fin 41,
    (∑ c : Col, if cross (representatives i) (column c) = 1 ∧ cls c = s
      then (1 : ℤ) else 0) = R i s := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem quotient_rows (b : Col) (s : Fin 41) :
    (∑ c : Col, if cross b (column c) = 1 ∧ cls c = s
      then (1 : ℤ) else 0) = R (cls b) s := by
  obtain ⟨e, he⟩ := class_rep b
  calc
    _ = ∑ c : Col, if cross (relabel e b) (column (relabel e c)) = 1 ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [cross_relabel, class_relabel]
    _ = ∑ c : Col, if cross (representatives (cls b)) (column c) = 1 ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if cross (representatives (cls b)) (column c) = 1 ∧ cls c = s
        then (1 : ℤ) else 0)
    _ = _ := representative_rows _ _

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripNew
