import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.ReverseClauseConversion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.ReverseClauseConversion
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
open _root_.PredictiveThermodynamic.ConventionalReverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Turing StateTransition LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => explicitRawCount w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    Nonempty (EvalsToInTime reverseMachine.step (initList reverseMachine w)
      (some (haltList reverseMachine (convertedWord w))) (10*w.length^2+41*w.length+33)) ∧
    (convertedWord w).length ≤ 4*w.length^2+14*w.length+6 ∧
    Conventional.readWord (convertedWord w) = some (saturatedFormula (preparedFormula w).2) ∧
    Conventional.rawCount (convertedWord w) = R.readout () () w

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h dummySource).2.2.2
  have good := (reverse_word_run dummySource).2.2.2
  have decoded : explicitRawCount dummySource = 0 := by
    change unaryCount ([[]] : UnaryFormula 0) = 0
    simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
  rw [decoded] at good
  have equal : (0 : Nat) = 3 := good.symm.trans bad
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reverse_word_run,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),sourceWord ([] : UnaryFormula 0),dummySource,?_⟩
    have decoded : explicitRawCount dummySource = 0 := by
      change unaryCount ([[]] : UnaryFormula 0) = 0
      simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
    change explicitRawCount (sourceWord ([] : UnaryFormula 0)) ≠ explicitRawCount dummySource
    rw [decoded]
    change unaryCount ([] : UnaryFormula 0) ≠ 0
    simp [unaryCount,unaryStandard,Std.Sat.CNF.eval]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.PredictiveThermodynamic.ConventionalReverse.reverse_word_run) (type_of% (realize signature (fun _ _ w => explicitRawCount w) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Computability.ReverseClauseConversion.informationUnit,
  realizationName := `Reg.D5.S0.Computability.ReverseClauseConversion.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ w => explicitRawCount w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.ReverseClauseConversion, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body","arg","arg","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.ReverseClauseConversion, declaration := `PredictiveThermodynamic.ConventionalReverse.reverse_word_run, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.sourceBridgeFact, `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.anchorEnumeration }

end Reg.D5.S0.Computability.ReverseClauseConversion


noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Computability.ReverseClauseConversion.arena
noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Computability.ReverseClauseConversion.arena
noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S0.Computability.ReverseClauseConversion.arena) (Reg.D5.S0.Computability.ReverseClauseConversion.registration).actual

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"PredictiveThermodynamic\",\"ConventionalReverse\",\"reverse_word_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S0.Computability.ReverseClauseConversion, declaration := `PredictiveThermodynamic.ConventionalReverse.reverse_word_run, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S0.Computability.ReverseClauseConversion.registration).bridge

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"PredictiveThermodynamic\",\"ConventionalReverse\",\"reverse_word_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S0.Computability.ReverseClauseConversion, declaration := `PredictiveThermodynamic.ConventionalReverse.reverse_word_run, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.Computability.ReverseClauseConversion.registration).actual (Reg.D5.S0.Computability.ReverseClauseConversion.registration).variation.2.choose (Reg.D5.S0.Computability.ReverseClauseConversion.registration).variation.1 (Reg.D5.S0.Computability.ReverseClauseConversion.registration).variation.2.choose_spec

noncomputable def Reg.D5.S0.Computability.ReverseClauseConversion.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ReverseClauseConversion\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ReverseClauseConversion, declaration := `Reg.D5.S0.Computability.ReverseClauseConversion.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
