namespace LeanInformationAudit.Tests.InlineProofHelper

universe u

theorem witness_self {α : Type u} [Nonempty α] (x : α) : ∃ y : α, y = x :=
  ⟨x, rfl⟩

end LeanInformationAudit.Tests.InlineProofHelper
