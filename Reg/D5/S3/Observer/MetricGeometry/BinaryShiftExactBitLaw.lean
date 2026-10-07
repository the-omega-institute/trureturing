import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw

open _root_.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ) (ε : ℝ) (_hε : 0 ≤ ε) (_hε1 : ε < 1),
    IsLeast {s : ℕ | HasFiniteHorizonPredictor
      (fun (_ : Unit) (x : ℕ → Bool) j => x (j + 1)) binaryObservation H ε s}
      (R.readout () () H) ∧
    Nat.clog 2 (2 ^ (H + 1)) = H + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (binary_shift_exact_bit_law 0 0 le_rfl zero_lt_one).1.2
    (h 0 0 le_rfl zero_lt_one).1.1
  norm_num [rejected, realize, signature] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨binary_shift_exact_bit_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    exact (by decide : (2 : ℕ) ^ (0 + 1) ≠ 2 ^ (1 + 1))

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "MetricGeometry") "BinaryShiftExactBitLaw") "binary_shift_exact_bit_law") "Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw/Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => 2 ^ (H + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.observationFact0, `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw


noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.arena
noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.arena
noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.arena) (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).actual

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"binary_shift_exact_bit_law\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).bridge

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.observation0 : (H : Nat) →
  (ε : Real) →
    (hε : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε) →
      (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (H : Nat) (ε : Real)
    (hε : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.signature
    Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.actual PUnit.unit.{1} PUnit.unit.{1} H

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"binary_shift_exact_bit_law\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law, part := .type, path := [.body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"binary_shift_exact_bit_law\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.binary_shift_exact_bit_law, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).actual (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).variation.2.choose (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).variation.1 (Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"BinaryShiftExactBitLaw\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw, declaration := `Reg.D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
