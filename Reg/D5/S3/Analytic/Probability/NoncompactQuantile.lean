import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport
import D5.S3.Analytic.Probability.NoncompactQuantile

/-! Typed reconstruction of the complete source telescopes for integrable martingale transport.
The source bridges and actual laws do not establish variation, sensitivity,
observational dependence or a four-slot registration. -/

open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Probability.NoncompactQuantile

namespace absolute_tail_le
abbrev arena : Arena where
  signature := ScalarMeasure
  Law r := source_law% Econlib.Probability.NoncompactQuantile.absolute_tail_le
    replacing (@ProbabilityMeasure.toMeasure ℝ inferInstance)
    with (r.readout () ())

theorem source_bridge :
    (type_of% @Econlib.Probability.NoncompactQuantile.absolute_tail_le) ↔ arena.Law scalarMeasureActual := Iff.rfl

theorem actual_law : arena.Law scalarMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.NoncompactQuantile.absolute_tail_le
end absolute_tail_le

namespace exists_martingale_approximations
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.NoncompactQuantile.exists_martingale_approximations
    replacing (@DiscreteLaw.condMeanAtomize)
    with (fun μ n hn => r.readout () μ ⟨n, hn⟩)

theorem source_bridge :
    (type_of% @Econlib.Probability.NoncompactQuantile.exists_martingale_approximations) ↔ arena.Law atomizationActual := Iff.rfl

theorem actual_law : arena.Law atomizationActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.NoncompactQuantile.exists_martingale_approximations
end exists_martingale_approximations

namespace tested_measurable_of_continuous
abbrev arena : Arena where
  signature := JointMeasure
  Law r := source_law% Econlib.Probability.NoncompactQuantile.tested_measurable_of_continuous
    replacing (@ProbabilityMeasure.toMeasure (ℝ × ℝ) inferInstance)
    with (r.readout () ())

theorem source_bridge :
    (type_of% @Econlib.Probability.NoncompactQuantile.tested_measurable_of_continuous) ↔ arena.Law jointMeasureActual := Iff.rfl

theorem actual_law : arena.Law jointMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.NoncompactQuantile.tested_measurable_of_continuous
end tested_measurable_of_continuous

end Reg.D5.S3.Analytic.Probability.NoncompactQuantile
end
