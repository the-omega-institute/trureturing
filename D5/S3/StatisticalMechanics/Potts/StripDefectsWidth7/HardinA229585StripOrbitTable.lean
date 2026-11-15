/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitTable.table_counts
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
table_counts: proof_shape=bind-only; consumers=OrbitCertificate.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable5
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable6
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable7
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable8
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData

set_option profiler true

/-! The complete output multiplicity table. -/
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitTable
open HardinA229585StripData HardinA229585StripOrbit

theorem table_counts (q s : Fin 72) : ((images q).count s : ℤ) = T q s := by
  by_cases h0 : q.val < 8
  · exact TableChecks.HardinA229585StripTable0.table_counts q ⟨by omega, h0⟩ s
  by_cases h1 : q.val < 16
  · exact TableChecks.HardinA229585StripTable1.table_counts q ⟨by omega, h1⟩ s
  by_cases h2 : q.val < 24
  · exact TableChecks.HardinA229585StripTable2.table_counts q ⟨by omega, h2⟩ s
  by_cases h3 : q.val < 32
  · exact TableChecks.HardinA229585StripTable3.table_counts q ⟨by omega, h3⟩ s
  by_cases h4 : q.val < 40
  · exact TableChecks.HardinA229585StripTable4.table_counts q ⟨by omega, h4⟩ s
  by_cases h5 : q.val < 48
  · exact TableChecks.HardinA229585StripTable5.table_counts q ⟨by omega, h5⟩ s
  by_cases h6 : q.val < 56
  · exact TableChecks.HardinA229585StripTable6.table_counts q ⟨by omega, h6⟩ s
  by_cases h7 : q.val < 64
  · exact TableChecks.HardinA229585StripTable7.table_counts q ⟨by omega, h7⟩ s
  exact TableChecks.HardinA229585StripTable8.table_counts q ⟨by omega, q.isLt⟩ s

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitTable
