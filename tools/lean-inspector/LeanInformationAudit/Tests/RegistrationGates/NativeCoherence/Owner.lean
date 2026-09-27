import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Helper
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace DTRNativeFixture
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def template (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x => helper f x)

end DTRNativeFixture
