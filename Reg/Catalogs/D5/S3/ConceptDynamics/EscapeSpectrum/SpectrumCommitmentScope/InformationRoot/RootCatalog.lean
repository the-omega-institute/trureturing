import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot
import Reg.Support.LegacySpectrum

namespace Reg.Catalogs.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective), theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective, objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, statementIdentity := some "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3", registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot } }

end Reg.Catalogs.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.InformationRoot.RootCatalog
