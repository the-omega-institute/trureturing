import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacySpectrum
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow



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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective) (type_of% (@RegistrationTemplates.cutRealization SpectrumAtom (Fin 5) (inferInstanceAs (DecidableEq (Fin 5))) (fun atom => Reg.Support.LegacySpectrum.indexReadout atom))) (type_of% (SpectrumAtom)) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective.__information_unit,
  realizationName := `Reg.Support.LegacySpectrum.bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(spectrumArena)⟩,
  objectArena := .law ⟨(spectrumArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (spectrumArena) (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) fun (atom : D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) => Reg.Support.LegacySpectrum.indexReadout atom) (spectrumRealization.toPrimitiveBundle) ⟨(Reg.Support.LegacySpectrum.bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (Reg.Support.LegacySpectrum.bridge) (@_root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((spectrumRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@RegistrationTemplates.cutRealization SpectrumAtom (Fin 5) (inferInstanceAs (DecidableEq (Fin 5))) (fun atom => Reg.Support.LegacySpectrum.indexReadout atom)),
  variation := .evidence ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.spectrum_lawSensitive)⟩ (by first | exact (_root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.spectrum_lawSensitive) | exact ⟨_, _, (_root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.spectrum_lawSensitive)⟩),
  sensitivity := .evidence ⟨(Reg.Support.LegacySpectrum.sensitivity)⟩ (by exact (Reg.Support.LegacySpectrum.sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (SpectrumAtom),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
example : (_root_.Reg.Support.LegacySpectrum.bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective).Statement =
    (D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.spectrum_atom_index_bijective_realization.toTheoremUnit
      spectrum_atom_index_bijective).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow
