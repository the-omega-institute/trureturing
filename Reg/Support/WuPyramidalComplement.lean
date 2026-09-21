import LeanInformationAudit.Syntax
import D5.S3.Arith.WuPyramidalComplement

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
attribute [local instance] _root_.D5.S3.Arith.WuPyramidalComplement.instDecidable_d5
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
register_information_template branchRealization
end
