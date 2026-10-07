import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage

noncomputable section

abbrev Role := Bool

abbrev signature : Signature where
  Params := ℕ
  State := fun n => ℤ × (Fin n → ℤ)
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ n => ℤ × (Fin n → ℤ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e)

/-- Each intervention changes one role and leaves the other at its actual value. -/
def rejected (i : Role) : Realization signature := realize signature
  (fun j n x => if j = i then (1, fun _ => 0) else actual.readout j n x)
  (fun e => nomatch e)

/-- All source occurrences remain except the first outer trace and the final reconstruction. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (y : ℤ × (Fin n → ℤ)),
    (∀ i, (2 * (n : ℤ) + 3) ∣ y.2 i - 2 * y.1) ↔
      R.readout false n (reconstruct n y) = y ∧
        ∀ x, traceGram n x = y → x = R.readout true n y

theorem rejected_law (i : Role) : ¬ arena.Law (rejected i) := by
  intro h
  have hh := (h 0 (0, fun _ => 0)).mp (by intro j; exact Fin.elim0 j)
  cases i
  · have he := congrArg Prod.fst hh.1
    norm_num [rejected, realize] at he
  · have he := congrArg Prod.fst (hh.2 (0, fun _ => 0) (by simp [traceGram]))
    norm_num [rejected, realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using integral_image,
    rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j h
      funext n x
      simp [rejected, realize, h]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨0, (0, fun _ => 0), (1, fun _ => 0), ?_⟩
    intro he
    have hfirst := congrArg Prod.fst he
    cases i <;> norm_num [actual, realize, traceGram, reconstruct] at hfirst

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Lattices") "PrimeCyclotomicTraceImage") "integral_image") "Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage/Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun i n => match i with
    | false => traceGram n
    | true => reconstruct n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }, { path := #["body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observationFact0, `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observationFact1, `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage


noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.arena
noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.arena
noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.arena) (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).actual

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"integral_image\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).bridge

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Bool) where
  values := [Bool.true, Bool.false]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observation0 : (n : Nat) →
  (y x : Prod.{0, 0} Int (Fin n → Int)) →
    @Eq.{1} (Prod.{0, 0} Int (Fin n → Int)) (D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.traceGram n x) y →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.signature Bool.true n :=
  fun (n : Nat) (y x : Prod.{0, 0} Int (Fin n → Int))
    (a : @Eq.{1} (Prod.{0, 0} Int (Fin n → Int)) (D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.traceGram n x) y) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.signature
    Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.actual Bool.true n y

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"integral_image\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image, part := .type, path := [.body, .body, .argument, .argument, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observation1 : (n : Nat) →
  (y : Prod.{0, 0} Int (Fin n → Int)) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.signature Bool.false n :=
  fun (n : Nat) (y : Prod.{0, 0} Int (Fin n → Int)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.signature
    Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.actual Bool.false n
    (D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.reconstruct n y)

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"integral_image\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image, part := .type, path := [.body, .body, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"integral_image\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.integral_image, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).actual (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).variation.2.choose (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).variation.1 (Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PrimeCyclotomicTraceImage\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage, declaration := `Reg.D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
