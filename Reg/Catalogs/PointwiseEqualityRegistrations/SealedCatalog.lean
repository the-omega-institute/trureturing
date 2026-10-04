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
import Reg.D5.S0.Tower.DBonacci.Substitution
import Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

namespace Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  source := #[{ statement := (_), proof := (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible), theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, statementIdentity := some "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0", registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { statement := (_), proof := (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction), theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, statementIdentity := some "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc", registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }],
  baseline := #[],
  companionPrefix := some `Reg.Catalogs.PointwiseEqualityRegistrations } }

def «seal» : Contract.Seal := { rootId := `Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog, options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.Catalogs.PointwiseEqualityRegistrations.SealedCatalog
