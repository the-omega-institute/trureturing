import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

namespace AllowlistBoundaries

theorem target : (137 : Nat) = 137 := rfl
theorem harmless : (2 : Nat) ∣ 4 := ⟨2, rfl⟩
def keep {p : Prop} (_ : p) (x : Bool) : Bool := x
def plain (_ : Unit) (state : Bool) : Bool := state
def proofArgument (_ : Unit) (state : Bool) : Bool := keep harmless state
def forbiddenArgument (_ : Unit) (state : Bool) : Bool := keep target state
structure Hidden where
  bit : Bool
  certificate : (137 : Nat) = 137
def hiddenPayload (_ : Unit) (state : Bool) : Bool := (Hidden.mk state rfl).bit

end AllowlistBoundaries
