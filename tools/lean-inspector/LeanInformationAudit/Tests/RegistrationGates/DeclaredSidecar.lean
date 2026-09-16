import LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecarSource

namespace LeanInformationAudit.Tests.DeclaredSidecar
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit.Tests.DeclaredSidecarSource

register_information_template cutRealization

declare_information_template_binding original in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))

end LeanInformationAudit.Tests.DeclaredSidecar
