import Init

/-! Independent checked propositions for scheduler boundary tests. -/
namespace LeanInformationAudit.Tests.SearchReduction.ExecutionChainCandidates
inductive Side : Prop where | intro : Side
inductive Helper (n : Nat) : Prop where | intro : Helper n
inductive Target (n : Nat) : Prop where | intro : Target n
theorem slow (n : Nat) : Side → Target n := fun _ => .intro
theorem easy (n : Nat) : Target n := .intro
theorem helperSlow (n : Nat) : Side → Helper n := fun _ => .intro
theorem viaHelper (n : Nat) : Helper n → Target n := fun _ => .intro
end LeanInformationAudit.Tests.SearchReduction.ExecutionChainCandidates
