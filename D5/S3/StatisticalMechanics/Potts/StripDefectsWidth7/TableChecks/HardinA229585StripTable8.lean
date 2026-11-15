/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable8
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable8
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable8.table_counts
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
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable8
open HardinA229585StripData HardinA229585StripOrbit

set_option profiler true in
theorem table_counts (q : Fin 72) (hq : 64 ≤ q.val ∧ q.val < 72) :
    ∀ s : Fin 72, ((images q).count s : ℤ) = T q s := by
  have h : q = 64 ∨ q = 65 ∨ q = 66 ∨ q = 67 ∨ q = 68 ∨ q = 69 ∨ q = 70 ∨ q = 71 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable8
