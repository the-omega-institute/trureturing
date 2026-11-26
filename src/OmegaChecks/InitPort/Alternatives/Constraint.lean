module
public import Init.Omega.Constraint

open Lean.Omega

namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Omega.Constraint.not_sat_of_isImpossible :
    type_of% @_root_.Lean.Omega.Constraint.not_sat_of_isImpossible := by
  intro ⟨lo, hi⟩ impossible t satisfied
  cases lo with
  | none => exact Bool.noConfusion impossible
  | some l =>
    cases hi with
    | none => exact Bool.noConfusion impossible
    | some u =>
      have bounds : decide (l ≤ t) = true ∧ decide (t ≤ u) = true :=
        of_decide_eq_true satisfied
      exact Int.not_le_of_gt (of_decide_eq_true impossible)
        (Int.le_trans (of_decide_eq_true bounds.1) (of_decide_eq_true bounds.2))

end OmegaChecks.InitPort.Alternatives
