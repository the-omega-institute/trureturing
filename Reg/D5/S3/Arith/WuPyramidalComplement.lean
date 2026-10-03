import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Arith.WuPyramidalComplement
import Reg.Support.WuPyramidalComplement



namespace Reg.D5.S3.Arith.WuPyramidalComplement

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

theorem _root_.Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.Arith.WuPyramidalComplement.branchArena
  (∀ (k n : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) k →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
        @Eq.{1} Nat (Nat.nth (D5.S3.Arith.WuPyramidalComplement.complement k) (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (have h : Nat := @Nat.floor.{0} Real Real.semiring Real.partialOrder (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (@Nat.cast.{0} Real Real.instNatCast (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)) (@Nat.cast.{0} Real Real.instNatCast (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) (@Inv.inv.{0} Real Real.instInv (@OfNat.ofNat.{0} Real (nat_lit 3) (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))));
          D5.S3.Arith.WuPyramidalComplement.evaluateBranch (D5.S3.Arith.WuPyramidalComplement.branchSelector (@Option.some.{0} Bool Bool.true) (@Option.some.{0} Bool Bool.false) (@Option.none.{0} Bool) k n h) n h))
  D5.S3.Arith.WuPyramidalComplement.identityReadout := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one) (type_of% (branchArena)) (type_of% (branchArena)) (type_of% (branchRealization (fun branch : Option.{0} Bool => branch))) (type_of% (branchVariation)) (type_of% (branchSensitivity)) (type_of% (some.{0} true)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__information_unit,
  realizationName := `Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := ⟨(branchArena)⟩,
  objectArena := ⟨(branchArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (branchArena) ((identityReadout)) ((identityReadout).toPrimitiveBundle) ⟨(Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization)⟩,
  readout := some (branchRealization (fun branch : Option.{0} Bool => branch)),
  variation := some ⟨(branchVariation)⟩,
  sensitivity := some ⟨(branchSensitivity)⟩,
  escapeFrom := some (some.{0} true),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
attribute [local instance] _root_.D5.S3.Arith.WuPyramidalComplement.instDecidable_d5
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
end

end Reg.D5.S3.Arith.WuPyramidalComplement
