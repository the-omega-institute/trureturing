import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.GreedyBrick.RestBlock
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GreedyBrick.SuccessorBand
open _root_.D5.S3.Combinatorics.GreedyBrick.RestBlock

namespace Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock

abbrev signature : Signature where
  Params := Unit
  State _ := RestState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ s => placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ s : RestState, ∃ t : RestState,
    RestEventStep s t (firstZeroBin s.capacity) ∧ r.readout () () s = t.capacity.reverse

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht, he⟩ := h ⟨0, [], by simp⟩
  change [] = t.capacity.reverse at he
  have hl := congrArg List.length he
  have hh := ht.height_eq
  simp only [List.length_nil, List.length_reverse] at hl
  simp only [List.length_nil, firstZeroBin, max_eq_right (by omega : 0 ≤ 1)] at hh
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), ⟨0, [], by simp⟩, ⟨1, [], by simp⟩, ?_⟩
  change placeBricks 0 [] 1 ≠ placeBricks 1 [] 1
  decide

def registration : Registration arena
    (∀ s : RestState, ∃ t : RestState,
      RestEventStep s t (firstZeroBin s.capacity) ∧
        placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity) =
          t.capacity.reverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_rest_block, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ s => placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "GreedyBrick") "RestBlock") "literal_rest_block") "Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock/Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration,
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
    (fun _ _ s => placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.arena) (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).actual

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"literal_rest_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).bridge

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.observation0 : (s t : D5.S3.Combinatorics.GreedyBrick.SuccessorBand.RestState) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (s t : D5.S3.Combinatorics.GreedyBrick.SuccessorBand.RestState) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.signature Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.actual
    PUnit.unit.{1} PUnit.unit.{1} s

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"literal_rest_block\"],\"part\":\"type\",\"path\":[\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block, part := .type, path := [.body, .argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"literal_rest_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `D5.S3.Combinatorics.GreedyBrick.RestBlock.literal_rest_block, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).actual (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).variation.2.choose (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).variation.1 (Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"RestBlock\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.RestBlock.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
