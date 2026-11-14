import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport
import D5.S3.Analytic.Probability.NoncompactStrassen

/-! Typed reconstruction of the complete source telescopes for integrable martingale transport.
The source bridges and actual laws do not establish variation, sensitivity,
observational dependence or a four-slot registration. -/

open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Probability.NoncompactStrassen

namespace strassen_iff
abbrev arena : Arena where
  signature := ScalarMeasure
  Law r := source_law% Econlib.Probability.NoncompactStrassen.strassen_iff
    replacing (@ProbabilityMeasure.toMeasure ℝ inferInstance)
    with (r.readout () ())

theorem source_bridge :
    (type_of% @Econlib.Probability.NoncompactStrassen.strassen_iff) ↔ arena.Law scalarMeasureActual := Iff.rfl

theorem actual_law : arena.Law scalarMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.NoncompactStrassen.strassen_iff
end strassen_iff

end Reg.D5.S3.Analytic.Probability.NoncompactStrassen
end
