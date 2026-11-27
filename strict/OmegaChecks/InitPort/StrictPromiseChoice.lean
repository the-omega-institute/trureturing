module
prelude
public import StrictReferenceChoice
public import OmegaInit.System.Promise
import all OmegaInit.System.Promise

namespace OmegaStrictReference

/-- A shared concrete promise handle allows any nonempty payload type.
The total result task would supply a value of that type. -/
public noncomputable def IO.Promise.result!
    (result : {α : Type} → Omega.IO.Promise α → Omega.Task α) : Choice :=
  fun α h => (result (α := α) ⟨Omega.IO.Promise.logicalToken.snd, h⟩).get

end OmegaStrictReference
