/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate.transition_counts
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
canonical_next: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=width-seven transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit6
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit7
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit8
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitTable
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

set_option profiler true

/-! Exact transition histograms from once-enumerated successor multisets. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
open HardinA229585StripData HardinA229585StripOrbit
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

private theorem canonical_next (p : Boundary) (d : Fin 2)
    (hp : Valid p d.val) (hn : Canonical p) :
    nextClasses p d.val = images (cl p d.val) := by
  by_cases h0 : (cl p d.val).val < 8
  · exact OrbitChecks.HardinA229585StripOrbit0.canonical_next p d hp hn ⟨by omega, h0⟩
  by_cases h1 : (cl p d.val).val < 16
  · exact OrbitChecks.HardinA229585StripOrbit1.canonical_next p d hp hn ⟨by omega, h1⟩
  by_cases h2 : (cl p d.val).val < 24
  · exact OrbitChecks.HardinA229585StripOrbit2.canonical_next p d hp hn ⟨by omega, h2⟩
  by_cases h3 : (cl p d.val).val < 32
  · exact OrbitChecks.HardinA229585StripOrbit3.canonical_next p d hp hn ⟨by omega, h3⟩
  by_cases h4 : (cl p d.val).val < 40
  · exact OrbitChecks.HardinA229585StripOrbit4.canonical_next p d hp hn ⟨by omega, h4⟩
  by_cases h5 : (cl p d.val).val < 48
  · exact OrbitChecks.HardinA229585StripOrbit5.canonical_next p d hp hn ⟨by omega, h5⟩
  by_cases h6 : (cl p d.val).val < 56
  · exact OrbitChecks.HardinA229585StripOrbit6.canonical_next p d hp hn ⟨by omega, h6⟩
  by_cases h7 : (cl p d.val).val < 64
  · exact OrbitChecks.HardinA229585StripOrbit7.canonical_next p d hp hn ⟨by omega, h7⟩
  exact OrbitChecks.HardinA229585StripOrbit8.canonical_next p d hp hn
    ⟨by omega, (cl p d.val).isLt⟩

theorem transition_counts (p : Boundary) (d : Fin 2)
    (hp : Valid p d.val) (hn : Canonical p) (s : Fin 72) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  calc
    _ = ((nextClasses p d.val).count s : ℤ) := sum_count p d.val s
    _ = ((images (cl p d.val)).count s : ℤ) := congrArg (fun z => (z.count s : ℤ))
      (canonical_next p d hp hn)
    _ = T (cl p d.val) s := HardinA229585StripOrbitTable.table_counts _ _

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
