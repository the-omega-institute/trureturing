module
public import Init.Grind.Lemmas
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Lean.Grind
export _root_.Lean.Grind (eqNDRec_heq eqRecOn_heq eqRec_heq eval_congr₁ eval_congr₂ heq_congr rfl_true)
end Omega.Lean.Grind
