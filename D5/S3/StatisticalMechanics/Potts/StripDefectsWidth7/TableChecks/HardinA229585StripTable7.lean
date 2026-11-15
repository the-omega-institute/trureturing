/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable7
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable7.table_counts
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
table_counts: proof_shape=bind-only; consumers=HardinA229585StripOrbitTable.table_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData

set_option profiler true

/-! Output multiplicities for eight input classes. -/
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable7
open HardinA229585StripData HardinA229585StripOrbit

set_option profiler true in
theorem table_counts (q : Fin 72) (hq : 56 ≤ q.val ∧ q.val < 64) :
    ∀ s : Fin 72, ((images q).count s : ℤ) = T q s := by
  have h : q = 56 ∨ q = 57 ∨ q = 58 ∨ q = 59 ∨ q = 60 ∨ q = 61 ∨ q = 62 ∨ q = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable7
