import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective,
      statementIdentity := "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena, theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective,
      statementIdentity := "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open FirstThreeArenas

register_information_theorem _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective in spectrumArena
  primitives spectrumRealization.toPrimitiveBundle realization spectrum_bridge
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open FirstThreeArenas
example : _root_.Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective.__information_unit.Statement =
    (D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.spectrum_atom_index_bijective_realization.toTheoremUnit
      spectrum_atom_index_bijective).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow
