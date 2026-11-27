module
public import Init.Prelude

namespace OmegaChecks.InitPort.Alternatives

/-- Heap-allocated natural indices take the same failure branch as a read on an empty array. -/
public def Array.get!InternalBorrowed {α : Type u} [Inhabited α] (xs : _root_.Array α) (i : Nat) : α :=
  if i < USize.size / 2 then xs.get!Internal i else (_root_.Array.mk []).get!Internal 0

end OmegaChecks.InitPort.Alternatives
