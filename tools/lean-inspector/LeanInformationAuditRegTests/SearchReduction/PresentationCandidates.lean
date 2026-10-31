import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline

/-! The scalar arithmetic presentation needs the baseline induction theorem;
it is not a registered hint or a target-owned simp lemma. -/
namespace LeanInformationAudit.Tests.SearchReduction.PresentationCandidates
open PresentationBaseline

def triple (n : Nat) : Nat := 3 * n

theorem arithmetic (n : Nat) : ramp n = 3 * n := by
  have h := ramp_value n
  omega

theorem packaged (n : Nat) : ramp n = 3 * n ∧ 0 ≤ n :=
  ⟨arithmetic n, Nat.zero_le n⟩

theorem renamed (n : Nat) : ramp n = triple n := arithmetic n

theorem iffForward (P Q : Prop) : P ∧ Q → Q ∧ P := and_comm.mp

theorem iffBackward (P Q : Prop) : Q ∧ P → P ∧ Q := and_comm.mpr

end LeanInformationAudit.Tests.SearchReduction.PresentationCandidates
