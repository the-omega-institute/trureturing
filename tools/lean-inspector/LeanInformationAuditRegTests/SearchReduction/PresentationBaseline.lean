import Mathlib.Tactic

/-! Immutable baseline statements for presentation-certification calibration. -/
namespace LeanInformationAudit.Tests.SearchReduction.PresentationBaseline

def ramp : Nat → Nat
  | 0 => 0
  | n + 1 => 3 + ramp n

theorem ramp_value (n : Nat) : ramp n = n + n + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ramp, ih]; omega

end LeanInformationAudit.Tests.SearchReduction.PresentationBaseline
