import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

-- The defining module belongs to a separate repository library; its declaration
-- namespace deliberately matches neither the library nor the protected roots.
namespace ImportedAllowlistSources

private theorem evidence : (137 : Nat) = 137 := rfl
private def relay (_ : Unit) (x : Bool) : Bool := let _ := evidence; x
def proofRead (_ : Unit) (x : Bool) : Bool := relay () x
def cleanRead (_ : Unit) (x : Bool) : Bool := x

end ImportedAllowlistSources
