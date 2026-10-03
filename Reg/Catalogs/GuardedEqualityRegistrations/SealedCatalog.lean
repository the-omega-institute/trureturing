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
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
import Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

namespace Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, statementIdentity := some "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { statement := (_), proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer), theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, statementIdentity := some "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1", registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model), theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, statementIdentity := some "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58", registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { statement := (_), proof := (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer), theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, statementIdentity := some "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1", registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.GuardedEqualityRegistrations } }

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.GuardedEqualityRegistrations.SealedCatalog
