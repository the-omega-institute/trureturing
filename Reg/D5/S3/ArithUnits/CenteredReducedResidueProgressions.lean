import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ArithUnits.CenteredReducedResidueProgressions
import Reg.Support.CenteredReducedResidueProgressions



namespace Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.instDecidableEqStateSourceCorrectionArena in

theorem _root_.Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ArithUnits.CenteredReducedResidueProgressions.sourceCorrectionArena
  (∀ (n : Nat),
    @Even.{0} Nat instAddNat n →
      @Squarefree.{0} Nat Nat.instMonoid n →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Finset.card.{0} Nat (Nat.primeFactors n)) →
          @LT.lt.{0} Nat instLTNat (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n (D5.S3.ArithUnits.CenteredReducedResidueProgressions.GreatestPrimeFactor n)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (D5.S3.ArithUnits.CenteredReducedResidueProgressions.GreatestPrimeFactor n)) →
            have p : Nat := D5.S3.ArithUnits.CenteredReducedResidueProgressions.GreatestPrimeFactor n;
            have d : Nat := @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n p;
            And (@IsGreatest.{0} Nat instLENat (@Set.ofPred.{0} Nat fun (s : Nat) => D5.S3.ArithUnits.CenteredReducedResidueProgressions.AdmissibleLength n s) (D5.S3.ArithUnits.CenteredReducedResidueProgressions.decodeSourceCorrection D5.S3.ArithUnits.CenteredReducedResidueProgressions.SourceCorrection p (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p) d))) (@Eq.{1} Int (@Int.floor.{0} Rat (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) (@Nat.cast.{0} Rat Rat.instNatCast p) (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) (@Nat.cast.{0} Rat Rat.instNatCast p)) (@Nat.cast.{0} Rat Rat.instNatCast d)))) (@Nat.cast.{0} Int instNatCastInt (D5.S3.ArithUnits.CenteredReducedResidueProgressions.decodeSourceCorrection D5.S3.ArithUnits.CenteredReducedResidueProgressions.SourceCorrection p (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p) d)))))
  D5.S3.ArithUnits.CenteredReducedResidueProgressions.actualSourceCorrectionRealization := by exact ⟨Iff.rfl⟩

attribute [local instance] _root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.instDecidableEqStateSourceCorrectionArena in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result) (type_of% (sourceCorrectionRealization (fun x : Bool => x))) (type_of% (SourceCorrection)) (Unit) := {
  unitName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result.__information_unit,
  realizationName := `Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(sourceCorrectionArena)⟩,
  objectArena := .law ⟨(sourceCorrectionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (sourceCorrectionArena) ((actualSourceCorrectionRealization)) ((actualSourceCorrectionRealization).toPrimitiveBundle) ⟨(Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result.__primitive_realization) (@_root_.D5.S3.ArithUnits.CenteredReducedResidueProgressions.result))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change (((actualSourceCorrectionRealization).toPrimitiveBundle)).Nonempty; decide),
  readout := some (sourceCorrectionRealization (fun x : Bool => x)),
  variation := .evidence ⟨(sourceCorrection_variation)⟩ (by first | exact (sourceCorrection_variation) | exact ⟨_, _, (sourceCorrection_variation)⟩),
  sensitivity := .evidence ⟨(sourceCorrection_sensitivity)⟩ (by exact (sourceCorrection_sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (SourceCorrection),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ArithUnits.CenteredReducedResidueProgressions
