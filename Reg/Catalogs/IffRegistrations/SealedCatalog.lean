import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

namespace Reg.Catalogs.IffRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled), theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { statement := (_), proof := (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff), theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, statementIdentity := some "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f", registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.IffRegistrations } }

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.IffRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.IffRegistrations.SealedCatalog
