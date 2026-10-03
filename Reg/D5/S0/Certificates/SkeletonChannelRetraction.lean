import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
import Reg.Support.PointwiseDisequalityRegistrations



namespace Reg.D5.S0.Certificates.SkeletonChannelRetraction

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction

noncomputable def _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena (∀ (d : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))), @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract d) (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)))) D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrent_bridge D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) (type_of% (digitArena)) (type_of% (digitArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentReadout d) (fun _ => digitTwo))) (type_of% (recurrent_lawSensitive)) (type_of% (digit_slotSensitive)) (type_of% (Fin 4)) (type_of% (recurrentResidual)) (Unit) := {
  unitName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrent_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(digitArena)⟩,
  objectArena := ⟨(digitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (digitArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization) (recurrentRealization.toPrimitiveBundle) ⟨(recurrent_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentReadout d) (fun _ => digitTwo)),
  variation := some ⟨(recurrent_lawSensitive)⟩,
  sensitivity := some ⟨(digit_slotSensitive)⟩,
  escapeFrom := some (Fin 4),
  sourceSelection := none,
  continuation := .evidence ⟨(recurrentResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction

noncomputable def _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena (∀ (d : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))), @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (D5.S0.Certificates.SkeletonChannelRetraction.transientRetract d) (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))) D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transient_bridge D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) (type_of% (digitArena)) (type_of% (digitArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientReadout d) (fun _ => digitZero))) (type_of% (transient_lawSensitive)) (type_of% (digit_slotSensitive)) (type_of% (Fin 4)) (type_of% (transientResidual)) (Unit) := {
  unitName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transient_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(digitArena)⟩,
  objectArena := ⟨(digitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (digitArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization) (transientRealization.toPrimitiveBundle) ⟨(transient_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientReadout d) (fun _ => digitZero)),
  variation := some ⟨(transient_lawSensitive)⟩,
  sensitivity := some ⟨(digit_slotSensitive)⟩,
  escapeFrom := some (Fin 4),
  sourceSelection := none,
  continuation := .evidence ⟨(transientResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction
example : _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two.__information_unit.Statement =
    (∀ d : Fin 4, recurrentRetract d ≠ 2) := rfl
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction
example : _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero.__information_unit.Statement =
    (∀ d : Fin 4, transientRetract d ≠ 0) := rfl
end

end Reg.D5.S0.Certificates.SkeletonChannelRetraction
