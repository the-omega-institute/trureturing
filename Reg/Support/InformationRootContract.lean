import LeanInformationAuditInterface.RootContract
import Reg.Support.FixedSnapshot
import Reg.Support.FrozenBaseline

namespace Reg.Support.InformationRootContract
open Lean LeanInformationAudit

-- Independent production expectations, supplied before this root is sealed.
def rootId : Name := `Reg.Catalogs.InformationRoot

def contract : RootCatalogContract := {
  rootId
  expected := Reg.Support.frozenInformationRootBaseline
  source := Reg.Support.fixedInformationSourceSnapshot.occurrences
  baseline := Reg.Support.frozenInformationRootBaseline
  companionPrefix := some rootId }

-- Accepted seal reference with only the four generated-name fields relocated.
def expectedSealDigest : String :=
  "288b65e8c041d47a8258b7098409e202dc26cd7df1c478086bdc777eab538b09"

end Reg.Support.InformationRootContract
