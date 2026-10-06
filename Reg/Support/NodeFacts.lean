import LeanInformationAuditInterface.Contract.NodeFactsCore

namespace Reg.Support.NodeFacts
universe u

/-- Two truth values rule out every fixed proposition for the whole Law. -/
theorem excludeFixed {T : Type u} (law : T → Prop) (statement : Prop)
    (positive negative : T) (holds : law positive) (fails : ¬ law negative) :
    ¬ ∀ x, law x ↔ statement := by
  intro fixed
  exact fails ((fixed negative).mpr ((fixed positive).mp holds))

end Reg.Support.NodeFacts
