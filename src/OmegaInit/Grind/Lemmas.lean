module
public import Init.Grind.Lemmas
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Lean.Grind
export _root_.Lean.Grind (eqNDRec_heq eqRecOn_heq eqRec_heq eval_congr₁ eval_congr₂ heq_congr rfl_true)
end Omega.Lean.Grind

namespace Omega.Lean.Grind.Bool
export _root_.Lean.Grind.Bool (
  and_eq_of_eq_false_left and_eq_of_eq_false_right and_eq_of_eq_true_left and_eq_of_eq_true_right
  eq_false_of_not_eq_true eq_false_of_not_eq_true' eq_false_of_or_eq_false_left eq_false_of_or_eq_false_right
  eq_true_of_and_eq_true_left eq_true_of_and_eq_true_right eq_true_of_not_eq_false eq_true_of_not_eq_false'
  false_of_not_eq_self not_eq_of_eq_false not_eq_of_eq_true
  or_eq_of_eq_false_left or_eq_of_eq_false_right or_eq_of_eq_true_left or_eq_of_eq_true_right)
end Omega.Lean.Grind.Bool
