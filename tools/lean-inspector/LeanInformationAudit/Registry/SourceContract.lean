import LeanInformationAudit.Registry.SourceOperands
import LeanInformationAudit.CompiledSourceContract

namespace LeanInformationAudit.SourceFinite
open Lean

/-- Compilation clients delegate the complete finite/source correspondence. -/
def validate (event : TemplateOccurrenceEvent) (arena signature actual : Expr)
    (bridgeName : Name) : SourceScope.M Unit := fun fuel =>
  TemplateAudit.runCompiled
    ((CompiledSourceFinite.validate event arena signature actual bridgeName).run fuel)

end LeanInformationAudit.SourceFinite

namespace LeanInformationAudit.SourceContract
open Lean

def validate (event : TemplateOccurrenceEvent) (descriptor : Expr)
    (plan : TemplateAudit.TemplatePlanData) (input : EscapeRecordInput) :
    Meta.MetaM TemplateBindingCertificate := do
  let certificate ← TemplateAudit.runCompiled (CompiledSourceContract.validate event descriptor plan input)
  TemplateAudit.NativeCoherence.validate (#[plan.definitionOwner, plan.enrollmentOwner,
    event.key.registrationModule] ++ certificate.extractionInputs.map (·.owner))
  return certificate

end LeanInformationAudit.SourceContract
