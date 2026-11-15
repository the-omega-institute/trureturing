/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable6
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable6
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/TableChecks/HardinA229585StripTable6.table_counts
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
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable6
open HardinA229585StripData HardinA229585StripOrbit

set_option profiler true in
theorem table_counts (q : Fin 72) (hq : 48 ≤ q.val ∧ q.val < 56) :
    ∀ s : Fin 72, ((images q).count s : ℤ) = T q s := by
  have h : q = 48 ∨ q = 49 ∨ q = 50 ∨ q = 51 ∨ q = 52 ∨ q = 53 ∨ q = 54 ∨ q = 55 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.TableChecks.HardinA229585StripTable6
