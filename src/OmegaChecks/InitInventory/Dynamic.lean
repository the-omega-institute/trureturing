module
public import Init.Dynamic

namespace OmegaChecks.InitBoundaries.DynamicRoundTrip

/-- A monomorphic type that can be stored in a native Dynamic. -/
public structure Query where
  apply : Dynamic → Bool

private def observe (tag : TypeName Query) (read : type_of% (@Dynamic.get?.{0})) (d : Dynamic) : Bool :=
  match @read Query d tag with
  | some f => f.apply d
  | none => false

/-- Storing and retrieving every callback would let a callback negate its own answer.
The writer, reader, and common type tag are parameters of the proof. -/
public theorem noRoundTrip (pack : type_of% (@Dynamic.mk.{0})) (read : type_of% (@Dynamic.get?.{0}))
    (tag : TypeName Query) (roundTrip : ∀ f : Query, @read Query (@pack Query tag f) tag = some f) : False := by
  let negate : Query := ⟨fun d => !(observe tag (@read) d)⟩
  let d := @pack Query tag negate
  have fixed : observe tag (@read) d = !(observe tag (@read) d) := by
    conv => lhs; unfold observe; rw [roundTrip negate]
  cases h : observe tag (@read) d <;> rw [h] at fixed <;> cases fixed

end OmegaChecks.InitBoundaries.DynamicRoundTrip
