import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one) (type_of% (branchRealization (fun branch : Option.{0} Bool => branch))) (type_of% (some.{0} true)) (Unit) := {
  unitName := `Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__information_unit,
  realizationName := `Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(branchArena)⟩,
  objectArena := .law ⟨(branchArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (branchArena) ((identityReadout)) ((identityReadout).toPrimitiveBundle) ⟨(Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (Reg.D5.S3.Arith.WuPyramidalComplement.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one.__primitive_realization) (@_root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change (((identityReadout).toPrimitiveBundle)).Nonempty; decide),
  readout := some (branchRealization (fun branch : Option.{0} Bool => branch)),
  variation := .evidence ⟨(branchVariation)⟩ (by first | exact (branchVariation) | exact ⟨_, _, (branchVariation)⟩),
  sensitivity := .evidence ⟨(branchSensitivity)⟩ (by exact (branchSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (some.{0} true),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.WuPyramidalComplement, declaration := `D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

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


noncomputable def Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.Arith.WuPyramidalComplement.branchArena
noncomputable def Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"WuPyramidalComplement\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"WuPyramidalComplement\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.Arith.WuPyramidalComplement.branchArena
noncomputable def Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"WuPyramidalComplement\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"WuPyramidalComplement\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.WuPyramidalComplement, declaration := `Reg.D5.S3.Arith.WuPyramidalComplement.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
