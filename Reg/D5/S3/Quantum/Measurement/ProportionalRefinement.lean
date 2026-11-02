import D5.S3.Quantum.Measurement.ProportionalRefinement

/-!
  The proportional-refinement declarations are finite algebraic identities whose
  source terms are inspected directly by the scoped Lean report.  No dependent
  observational registration is introduced here: the atom has no external
  information-escape claim, and the abstract quadratic readouts deliberately
  retain the source convention as hypotheses.
-/

namespace Reg.D5.S3.Quantum.Measurement.ProportionalRefinement

open _root_.D5.S3.Quantum.Measurement.ProportionalRefinement

#print axioms quadratic_budgets
#print axioms min_coordinate_budget_preserved
#print axioms quartic_budgets
#print axioms actual_channel_preserved_rectangular
#print axioms completeness_preserved

end Reg.D5.S3.Quantum.Measurement.ProportionalRefinement
