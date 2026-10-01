import LeanInformationAudit.Tests.RegistrationGates.DeclaredSource
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace LeanInformationAudit.Tests.DeclaredRegistration
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit.Tests.DeclaredSource

test_assess in register_information_theorem original in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)).toPrimitiveBundle
  realization inline (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)) :=
    ⟨⟨fun h => h, fun h => h⟩⟩

end LeanInformationAudit.Tests.DeclaredRegistration
