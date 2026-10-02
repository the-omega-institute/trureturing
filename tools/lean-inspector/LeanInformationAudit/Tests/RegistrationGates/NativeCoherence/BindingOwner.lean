import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace LeanInformationAudit.Tests.NativeBindingOwner
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- Only BindingChecks imports this native artifact and temporarily replaces it.
-- Other binding probes keep their own immutable input closures.
test_assess in register_information_template cutRealization

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

test_assess in information_theorem validated in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

end LeanInformationAudit.Tests.NativeBindingOwner
