import Reg.Catalogs.UnifiedCausalRegistration
import Reg.Catalogs.InformationRoot
import Reg.Support.SharedInformationRootContract
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.SharedInformationRootContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Seal the existing finite catalogs under the production seal limit.
#seal_information_theory
