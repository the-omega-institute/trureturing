import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport
import D5.S3.Analytic.Probability.FirstMomentWeakLimit

/-!
Typed reconstruction of the full varying-law displacement convergence statement.
The joint-measure observation retains the arbitrary sequence, limit, coordinate
integrability, uniform absolute tails and every bounded continuous scalar test.
The source equivalence and actual law below do not supply the variation,
sensitivity, observational-dependence or source-selection evidence needed for a
four-slot registration.
-/

open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit

noncomputable section

namespace Reg.D5.S3.Analytic.Probability.FirstMomentWeakLimit

abbrev arena : Arena where
  signature := JointMeasure
  Law r := source_law%
    D5.S3.Analytic.Probability.FirstMomentWeakLimit.tendsto_integral_displacement
    replacing (@ProbabilityMeasure.toMeasure (ℝ × ℝ) inferInstance)
    with (r.readout () ())

theorem source_bridge :
    (type_of% @_root_.D5.S3.Analytic.Probability.FirstMomentWeakLimit.tendsto_integral_displacement)
      ↔ arena.Law jointMeasureActual := Iff.rfl

theorem actual_law : arena.Law jointMeasureActual := by
  apply source_bridge.mp
  exact @_root_.D5.S3.Analytic.Probability.FirstMomentWeakLimit.tendsto_integral_displacement

end Reg.D5.S3.Analytic.Probability.FirstMomentWeakLimit

end
