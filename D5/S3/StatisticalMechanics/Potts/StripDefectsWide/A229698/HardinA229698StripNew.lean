/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripNew
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripNew
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
representative_rows: proof_shape=bind-only; consumers=quotient_rows
quotient_rows: proof_shape=bind-only; consumers=HardinA229698StripCut.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripNew
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup6

/-! Exact three-colour counts on five-row HA strips with two defects. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229698StripData

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem representative_rows (i s : Fin 41) :
    (∑ c : Col, if HardinA229590StripData.cross (representatives i) (column c) = 2 ∧
      cls c = s then (1 : ℤ) else 0) = S i s := by
  fin_cases i
  · exact HardinA229698StripClassGroup0.representative_rows 0 s
  · exact HardinA229698StripClassGroup0.representative_rows 1 s
  · exact HardinA229698StripClassGroup0.representative_rows 2 s
  · exact HardinA229698StripClassGroup0.representative_rows 3 s
  · exact HardinA229698StripClassGroup0.representative_rows 4 s
  · exact HardinA229698StripClassGroup0.representative_rows 5 s
  · exact HardinA229698StripClassGroup1.representative_rows 0 s
  · exact HardinA229698StripClassGroup1.representative_rows 1 s
  · exact HardinA229698StripClassGroup1.representative_rows 2 s
  · exact HardinA229698StripClassGroup1.representative_rows 3 s
  · exact HardinA229698StripClassGroup1.representative_rows 4 s
  · exact HardinA229698StripClassGroup1.representative_rows 5 s
  · exact HardinA229698StripClassGroup2.representative_rows 0 s
  · exact HardinA229698StripClassGroup2.representative_rows 1 s
  · exact HardinA229698StripClassGroup2.representative_rows 2 s
  · exact HardinA229698StripClassGroup2.representative_rows 3 s
  · exact HardinA229698StripClassGroup2.representative_rows 4 s
  · exact HardinA229698StripClassGroup2.representative_rows 5 s
  · exact HardinA229698StripClassGroup3.representative_rows 0 s
  · exact HardinA229698StripClassGroup3.representative_rows 1 s
  · exact HardinA229698StripClassGroup3.representative_rows 2 s
  · exact HardinA229698StripClassGroup3.representative_rows 3 s
  · exact HardinA229698StripClassGroup3.representative_rows 4 s
  · exact HardinA229698StripClassGroup3.representative_rows 5 s
  · exact HardinA229698StripClassGroup4.representative_rows 0 s
  · exact HardinA229698StripClassGroup4.representative_rows 1 s
  · exact HardinA229698StripClassGroup4.representative_rows 2 s
  · exact HardinA229698StripClassGroup4.representative_rows 3 s
  · exact HardinA229698StripClassGroup4.representative_rows 4 s
  · exact HardinA229698StripClassGroup4.representative_rows 5 s
  · exact HardinA229698StripClassGroup5.representative_rows 0 s
  · exact HardinA229698StripClassGroup5.representative_rows 1 s
  · exact HardinA229698StripClassGroup5.representative_rows 2 s
  · exact HardinA229698StripClassGroup5.representative_rows 3 s
  · exact HardinA229698StripClassGroup5.representative_rows 4 s
  · exact HardinA229698StripClassGroup5.representative_rows 5 s
  · exact HardinA229698StripClassGroup6.representative_rows 0 s
  · exact HardinA229698StripClassGroup6.representative_rows 1 s
  · exact HardinA229698StripClassGroup6.representative_rows 2 s
  · exact HardinA229698StripClassGroup6.representative_rows 3 s
  · exact HardinA229698StripClassGroup6.representative_rows 4 s

set_option maxHeartbeats 0 in
theorem quotient_rows (b : Col) (s : Fin 41) :
    (∑ c : Col, if HardinA229590StripData.cross b (column c) = 2 ∧ cls c = s
      then (1 : ℤ) else 0) = S (cls b) s := by
  obtain ⟨e, he⟩ := class_rep b
  calc
    _ = ∑ c : Col, if HardinA229590StripData.cross (relabel e b) (column (relabel e c)) = 2 ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [HardinA229590StripNew.cross_relabel, class_relabel]
    _ = ∑ c : Col, if HardinA229590StripData.cross (representatives (cls b)) (column c) = 2 ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if HardinA229590StripData.cross (representatives (cls b)) (column c) = 2 ∧ cls c = s
        then (1 : ℤ) else 0)
    _ = _ := representative_rows _ _

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
