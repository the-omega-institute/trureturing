import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.Syntax

open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
namespace DTRIndex.A

def selected {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

register_information_template selected
end DTRIndex.A
