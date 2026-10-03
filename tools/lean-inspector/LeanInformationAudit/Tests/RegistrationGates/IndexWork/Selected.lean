import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
namespace DTRIndex.A

def selected {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

test_assess in register_information_template selected
end DTRIndex.A
