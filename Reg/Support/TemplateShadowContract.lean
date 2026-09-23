import LeanInformationAuditInterface.RootContract
import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline

namespace Reg.Support.TemplateShadowContract
open Lean LeanInformationAudit

def rootId : Name := `Reg.Catalogs.TemplateShadow

-- TemplateShadow supplies the same ten mathematical occurrences as the
-- independent baseline, excluding SystemUnit. Only the producer differs.
-- Statement identities retain theoremStatementIdentity's toString-type hash.
def occurrences : Array SnapshotOccurrence :=
  (frozenInformationRootBaseline.filter fun row => row.objectArenaName !=
    `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena).map fun row =>
      { row with registrationModuleName :=
          `D5.S3.ConceptDynamics.InformationEscape.TemplateShadow }

def contract : RootCatalogContract := {
  rootId
  expected := occurrences
  source := occurrences
  baseline := occurrences
  companionPrefix := some rootId }

-- Independently translated from the existing D5 seal: only catalog, verdict,
-- unit and certificate names change to this root's generated names.
def expectedSealDigest : String :=
  "ef013c5f573c8bfe35cdc82d8422fb8674b69d82925938ad809316a289bf146f"

end Reg.Support.TemplateShadowContract
