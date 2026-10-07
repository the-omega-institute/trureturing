import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.DenseClauseMachine
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.DenseClauseMachine
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.BinaryNames
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Turing StateTransition LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option Conventional.Formula
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => Conventional.readWord w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => some []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : List Bool,
    Nonempty (EvalsToInTime denseMachine.step
      (initList denseMachine w)
      (some ⟨some .parseReturn, denseLocal,
        denseParserStacks (Conventional.parseStacks w [] (Conventional.decodedOccurrences w)
          [(Conventional.readWord w).isSome] [])⟩) (4*w.length+5)) ∧
    (∀ F : Conventional.Formula, R.readout () () w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3)

def rejected_law : ¬ arena.Law rejected := by
  intro h
  have falseSpelling := ((h Conventional.comparisonSource).2 [] rfl).1
  have different : Conventional.comparisonSource ≠ Conventional.formulaWord [] := by decide
  exact different falseSpelling

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dense_parser_run,rejected,rejected_law⟩
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
    refine ⟨(),Conventional.comparisonSource,[],?_⟩
    change Conventional.readWord Conventional.comparisonSource ≠ Conventional.readWord []
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.PredictiveThermodynamic.BinaryNames.dense_parser_run) (type_of% (realize signature (fun _ _ w => Conventional.readWord w) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Computability.DenseClauseMachine.informationUnit,
  realizationName := `Reg.D5.S0.Computability.DenseClauseMachine.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ w => Conventional.readWord w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.DenseClauseMachine, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body","arg","body","domain","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.DenseClauseMachine, declaration := `PredictiveThermodynamic.BinaryNames.dense_parser_run, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.sourceBridgeFact, `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.anchorEnumeration }

end Reg.D5.S0.Computability.DenseClauseMachine


noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Computability.DenseClauseMachine.arena
noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Computability.DenseClauseMachine.arena
noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S0.Computability.DenseClauseMachine.arena) (Reg.D5.S0.Computability.DenseClauseMachine.registration).actual

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"PredictiveThermodynamic\",\"BinaryNames\",\"dense_parser_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S0.Computability.DenseClauseMachine, declaration := `PredictiveThermodynamic.BinaryNames.dense_parser_run, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S0.Computability.DenseClauseMachine.registration).bridge

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.Computability.DenseClauseMachine.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"PredictiveThermodynamic\",\"BinaryNames\",\"dense_parser_run\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S0.Computability.DenseClauseMachine, declaration := `PredictiveThermodynamic.BinaryNames.dense_parser_run, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.Computability.DenseClauseMachine.registration).actual (Reg.D5.S0.Computability.DenseClauseMachine.registration).variation.2.choose (Reg.D5.S0.Computability.DenseClauseMachine.registration).variation.1 (Reg.D5.S0.Computability.DenseClauseMachine.registration).variation.2.choose_spec

noncomputable def Reg.D5.S0.Computability.DenseClauseMachine.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"DenseClauseMachine\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.DenseClauseMachine, declaration := `Reg.D5.S0.Computability.DenseClauseMachine.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
