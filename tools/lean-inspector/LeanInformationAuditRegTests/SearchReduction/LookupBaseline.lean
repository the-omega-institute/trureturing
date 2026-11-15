import Init

/-! A small independent basis for retrieval and nonrecursive inference tests. -/
namespace LeanInformationAudit.Tests.SearchReduction.LookupBaseline

inductive Mark (n : Nat) : Prop where | intro : Mark n
inductive Left : Prop where | intro : Left
inductive Right : Prop where | intro : Right
inductive Side : Prop where | intro : Side
inductive Finish : Prop where | intro : Finish
inductive Combined (m n : Nat) : Prop where | intro : Combined m n

inductive PrivateMark (n : Nat) : Prop where | intro : PrivateMark n
private theorem hiddenMember (n : Nat) : PrivateMark n := .intro

theorem pair (n : Nat) : Mark n ∧ Side := ⟨.intro, .intro⟩
theorem direction : Left ↔ Right := ⟨fun _ => .intro, fun _ => .intro⟩
theorem reordered (m n : Nat) (h : Mark m) : Combined m n := .intro
theorem conditional (n : Nat) (h : Mark n) : Finish := .intro

inductive DataMark (n : Nat) : Prop where | intro : DataMark n
abbrev certifiedData (n : Nat) : {k : Nat // DataMark k} := ⟨n, .intro⟩

class Certified (n : Nat) : Prop where
  evidence : Mark n

instance : Certified 7 := ⟨.intro⟩
inductive InstanceMark (n : Nat) : Prop where | intro : InstanceMark n
theorem instanceForm (n : Nat) [Certified n] : InstanceMark n := .intro

class OutputCertified (n : outParam Nat) : Prop where
  evidence : Mark n

instance : OutputCertified 7 := ⟨.intro⟩
inductive HiddenFinish : Prop where | intro : HiddenFinish
theorem instanceHiddenForm (n : Nat) [OutputCertified n] : HiddenFinish := .intro
theorem unusedData (_n : Nat) : HiddenFinish := .intro

inductive First : Prop where | intro : First
inductive Middle : Prop where | intro : Middle
inductive Last : Prop where | intro : Last
theorem firstMiddle : First → Middle := fun _ => .intro
theorem middleLast : Middle → Last := fun _ => .intro

end LeanInformationAudit.Tests.SearchReduction.LookupBaseline
