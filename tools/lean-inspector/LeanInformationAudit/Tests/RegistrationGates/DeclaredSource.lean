import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredSource
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

register_information_template cutRealization

-- Mathematics is compiled independently of its downstream declaration.
theorem original : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

end LeanInformationAudit.Tests.DeclaredSource
