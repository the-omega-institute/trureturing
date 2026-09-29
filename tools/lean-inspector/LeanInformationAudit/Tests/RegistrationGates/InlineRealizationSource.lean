import LeanInformationAudit.Tests.RegistrationGates.InlineProofHelper

namespace LeanInformationAudit.Tests.InlineRealizationSource

universe u v

theorem quantified {α : Type u} [Nonempty α] (x : α) : ∃ y : α, y = x :=
  LeanInformationAudit.Tests.InlineProofHelper.witness_self x

theorem readoutQuantified {α : Type u} [Nonempty α] (x : α) : ∃ y : α, y = x :=
  LeanInformationAudit.Tests.InlineProofHelper.witness_self x

theorem occurrenceQuantified {α : Type u} [Nonempty α] (x : α) : ∃ y : α, y = x :=
  LeanInformationAudit.Tests.InlineProofHelper.witness_self x

theorem twoUniverses {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    (x : β) : ∃ y : β, y = x :=
  LeanInformationAudit.Tests.InlineProofHelper.witness_self x

end LeanInformationAudit.Tests.InlineRealizationSource
