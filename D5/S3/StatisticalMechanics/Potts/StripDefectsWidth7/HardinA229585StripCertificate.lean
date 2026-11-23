/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate.structural_certificate
   digest: Width-7 structural, forward and polynomial certificate. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
tail_bound: proof_shape=bind-only; consumers=structural_certificate
structural_certificate: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts6
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts7
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts8
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

set_option profiler true

/-! Exact finite certificates for the width-seven one-defect strip. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
open D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

attribute [local irreducible] W T initial terminal cl

private theorem tail_bound (r : Row) :
    (Finset.univ.filter fun z : Fin 5 =>
      boundary r z.castSucc = boundary r z.succ).card ≤ bondDefects horizontal r r := by
  revert r
  decide +kernel

theorem structural_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 72, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro p d hp r hr
    have hd := hp.1
    have ht := tail_bound r
    constructor
    · omega
    · change _ ≤ 1 - (d.val - (cross p r + bondDefects horizontal r r))
      omega
  · intro r hr
    have ht := tail_bound r
    constructor
    · omega
    · change _ ≤ 1 - (1 - bondDefects horizontal r r)
      omega
  · intro s
    by_cases h0 : s.val < 8
    · exact Initial.HardinA229585StripCounts0.initial_counts s ⟨by omega, h0⟩
    by_cases h1 : s.val < 16
    · exact Initial.HardinA229585StripCounts1.initial_counts s ⟨by omega, h1⟩
    by_cases h2 : s.val < 24
    · exact Initial.HardinA229585StripCounts2.initial_counts s ⟨by omega, h2⟩
    by_cases h3 : s.val < 32
    · exact Initial.HardinA229585StripCounts3.initial_counts s ⟨by omega, h3⟩
    by_cases h4 : s.val < 40
    · exact Initial.HardinA229585StripCounts4.initial_counts s ⟨by omega, h4⟩
    by_cases h5 : s.val < 48
    · exact Initial.HardinA229585StripCounts5.initial_counts s ⟨by omega, h5⟩
    by_cases h6 : s.val < 56
    · exact Initial.HardinA229585StripCounts6.initial_counts s ⟨by omega, h6⟩
    by_cases h7 : s.val < 64
    · exact Initial.HardinA229585StripCounts7.initial_counts s ⟨by omega, h7⟩
    exact Initial.HardinA229585StripCounts8.initial_counts s ⟨by omega, s.isLt⟩
  · constructor
    · unfold W initial
      rfl
    · intro i
      change W ⟨i.val + 1, by omega⟩ = Matrix.vecMul (W ⟨i.val, by omega⟩) T
      by_cases h0 : i.val < 2
      · have h := ForwardChecks.HardinA229585StripForward0.forward_steps
          ⟨i.val - 0, by omega⟩
        simpa only [Fin.val_mk, show 0 + (i.val - 0) = i.val by omega] using h
      by_cases h1 : i.val < 4
      · have h := ForwardChecks.HardinA229585StripForward1.forward_steps
          ⟨i.val - 2, by omega⟩
        simpa only [Fin.val_mk, show 2 + (i.val - 2) = i.val by omega] using h
      by_cases h2 : i.val < 6
      · have h := ForwardChecks.HardinA229585StripForward2.forward_steps
          ⟨i.val - 4, by omega⟩
        simpa only [Fin.val_mk, show 4 + (i.val - 4) = i.val by omega] using h
      by_cases h3 : i.val < 8
      · have h := ForwardChecks.HardinA229585StripForward3.forward_steps
          ⟨i.val - 6, by omega⟩
        simpa only [Fin.val_mk, show 6 + (i.val - 6) = i.val by omega] using h
      have h := ForwardChecks.HardinA229585StripForward4.forward_steps
        ⟨i.val - 8, by omega⟩
      simpa only [Fin.val_mk, show 8 + (i.val - 8) = i.val by omega] using h
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripCertificate
