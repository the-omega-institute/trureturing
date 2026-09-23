import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import LeanInformationAuditInterface.RootContract
import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline

namespace Reg.Support.InformationRootContract
open Lean LeanInformationAudit

-- Independent production expectations, supplied before this root is sealed.
def rootId : Name := `Reg.Catalogs.InformationRoot

def contract : RootCatalogContract := {
  rootId
  expected := frozenInformationRootBaseline
  source := fixedInformationSourceSnapshot.occurrences
  baseline := frozenInformationRootBaseline
  companionPrefix := some rootId }

-- Accepted seal reference with only the four generated-name fields relocated.
def expectedSealDigest : String :=
  "288b65e8c041d47a8258b7098409e202dc26cd7df1c478086bdc777eab538b09"

end Reg.Support.InformationRootContract

section
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

#check (homogeneousPointwiseEq_sensitivity (Arena.ofFintype (Fin 3))
  (0 : Fin 3) (0 : Fin 3) 1 (by decide) :
  LeanInformationAudit.FiniteLawVariation
    (homogeneousPointwiseEqArena (Arena.ofFintype (Fin 3)) (Fin 3)))
end
