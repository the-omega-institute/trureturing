/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable0.table_counts
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
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable0
open HardinA229585StripData HardinA229585StripOrbit

set_option profiler true in
theorem table_counts (q : Fin 72) (hq : 0 ≤ q.val ∧ q.val < 8) :
    ∀ s : Fin 72, ((images q).count s : ℤ) = T q s := by
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable0
