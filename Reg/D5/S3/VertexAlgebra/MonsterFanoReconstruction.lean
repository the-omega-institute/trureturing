import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.MonsterFanoReconstruction
import Reg.Support.DependentFamily

set_option autoImplicit false

open Finset LeanInformationAudit
open scoped symmDiff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction

abbrev signature : Signature where
  Params := Finset (Fin 7)
  State _ := Finset (Fin 7)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset (Fin 7)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ block other => univ \ (block ∆ other)) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (blocks : Finset (Finset (Fin 7))),
    (∀ A ∈ blocks, A.card = 3) →
    (∀ i j : Fin 7, i ≠ j → ∃! A : Finset (Fin 7), A ∈ blocks ∧ i ∈ A ∧ j ∈ A) →
    ∀ {A B : Finset (Fin 7)}, A ∈ blocks → B ∈ blocks → A ≠ B →
      readout.readout () A B ∈ blocks

def sampleBlocks : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

set_option maxRecDepth 4096 in
theorem sampleCard : ∀ A ∈ sampleBlocks, A.card = 3 := by decide

set_option maxRecDepth 4096 in
theorem samplePair : ∀ i j : Fin 7, i ≠ j →
    ∃! A : Finset (Fin 7), A ∈ sampleBlocks ∧ i ∈ A ∧ j ∈ A := by
  have bounded : ∀ i j : Fin 7, i ≠ j →
      ∃ A ∈ sampleBlocks, i ∈ A ∧ j ∈ A ∧
        ∀ B ∈ sampleBlocks, i ∈ B → j ∈ B → B = A := by decide
  intro left right hne
  obtain ⟨line, hline, hl, hr, unique⟩ := bounded left right hne
  exact ⟨line, ⟨hline, hl, hr⟩, fun other ho => unique other ho.1 ho.2.1 ho.2.2⟩

theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have bad := law sampleBlocks sampleCard samplePair
    (A := {0, 1, 2}) (B := {0, 3, 4}) (by decide) (by decide) (by decide)
  change (∅ : Finset (Fin 7)) ∈ sampleBlocks at bad
  exact (by decide : (∅ : Finset (Fin 7)) ∉ sampleBlocks) bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem,
    rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨∅, ∅, {0}, ?_⟩
    change univ \ ((∅ : Finset (Fin 7)) ∆ ∅) ≠ univ \ ((∅ : Finset (Fin 7)) ∆ {0})
    intro heq
    have hzero : (0 : Fin 7) ∈ univ \ ((∅ : Finset (Fin 7)) ∆ ∅) := by simp
    rw [heq] at hzero
    simp [mem_symmDiff] at hzero

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ block other => univ.{0} \ (block ∆ other))
    (fun empty => nomatch empty))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "VertexAlgebra") "MonsterFanoReconstruction") "complement_symmDiff_mem") "Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction/Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ block other => univ.{0} \ (block ∆ other))
    (fun empty => nomatch empty)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalArenaFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.sourceBridgeFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.observationFact0, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.anchorEnumeration }


#print axioms registration

namespace Intersection

abbrev signature : Signature where
  Params := Finset (Fin 7)
  State _ := Finset (Fin 7)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ block other => (block ∩ other).card)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (blocks : Finset (Finset (Fin 7))),
    (∀ i j : Fin 7, i ≠ j →
      ∃! A : Finset (Fin 7), A ∈ blocks ∧ i ∈ A ∧ j ∈ A) →
    ∀ {A B : Finset (Fin 7)}, A ∈ blocks → B ∈ blocks → A ≠ B →
      readout.readout () A B ≤ 1

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have bad := law sampleBlocks samplePair
    (A := {0, 1, 2}) (B := {0, 3, 4})
    (by simp [sampleBlocks]) (by simp [sampleBlocks]) (by
      intro heq
      have hmem : (1 : Fin 7) ∈ ({0, 1, 2} : Finset (Fin 7)) := by simp
      rw [heq] at hmem
      simpa using hmem)
  change 2 ≤ 1 at bad
  exact Nat.not_succ_le_self 1 bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one,
    rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨{0}, ∅, {0}, ?_⟩
    change (({0} : Finset (Fin 7)) ∩ ∅).card ≠
      (({0} : Finset (Fin 7)) ∩ {0}).card
    simp

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ block other => (block ∩ other).card.{0})
    (fun empty => nomatch empty))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "VertexAlgebra") "MonsterFanoReconstruction") "block_intersection_le_one") "Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction/Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ block other => (block ∩ other).card.{0})
    (fun empty => nomatch empty)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalArenaFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.sourceBridgeFact, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.observationFact0, `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.anchorEnumeration }


#print axioms registration

end Intersection

end Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction


noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.arena
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.arena
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.arena
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.arena
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.arena) (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).actual

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"complement_symmDiff_mem\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).bridge

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.observation0 : (blocks : Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) →
  (hcard :
      ∀ (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))),
        @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              (@Finset.instSetLike.{0}
                (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
            blocks A →
          @Eq.{1} Nat (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) A)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
    (hpair :
        ∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
          @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) i j →
            @ExistsUnique.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              fun (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) =>
              And
                (@Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (@Finset.instSetLike.{0}
                      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  blocks A)
                (And
                  (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (@SetLike.instMembership.{0, 0}
                      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                    A i)
                  (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (@SetLike.instMembership.{0, 0}
                      (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                    A j))) →
      {A B : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))} →
        (hA :
            @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
              (@SetLike.instMembership.{0, 0}
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (@Finset.instSetLike.{0}
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
              blocks A) →
          (hB :
              @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@Finset.instSetLike.{0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                blocks B) →
            (hne : @Ne.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) A B) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.signature PUnit.unit.{1} A :=
  fun (blocks : Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
    (hcard :
      ∀ (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))),
        @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              (@Finset.instSetLike.{0}
                (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
            blocks A →
          @Eq.{1} Nat (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) A)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (hpair :
      ∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) i j →
          @ExistsUnique.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            fun (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) =>
            And
              (@Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@Finset.instSetLike.{0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                blocks A)
              (And
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A i)
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A j)))
    {A B : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))}
    (hA :
      @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
        (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (@Finset.instSetLike.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        blocks A)
    (hB :
      @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
        (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (@Finset.instSetLike.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        blocks B)
    (hne : @Ne.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) A B) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.signature Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.actual
    PUnit.unit.{1} A B

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"complement_symmDiff_mem\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"complement_symmDiff_mem\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).actual (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).variation.2.choose (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).variation.1 (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.arena) (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).actual

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"block_intersection_le_one\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).bridge

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.observation0 : (blocks : Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) →
  (hpair :
      ∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) i j →
          @ExistsUnique.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            fun (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) =>
            And
              (@Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@Finset.instSetLike.{0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                blocks A)
              (And
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A i)
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A j))) →
    {A B : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))} →
      (hA :
          @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
              (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              (@Finset.instSetLike.{0}
                (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
            blocks A) →
        (hB :
            @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
              (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
              (@SetLike.instMembership.{0, 0}
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (@Finset.instSetLike.{0}
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
              blocks B) →
          (hne : @Ne.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) A B) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.signature PUnit.unit.{1} A :=
  fun (blocks : Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
    (hpair :
      ∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))),
        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) i j →
          @ExistsUnique.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
            fun (A : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) =>
            And
              (@Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@Finset.instSetLike.{0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                blocks A)
              (And
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A i)
                (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
                  A j)))
    {A B : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))}
    (hA :
      @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
        (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (@Finset.instSetLike.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        blocks A)
    (hB :
      @Membership.mem.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
        (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (@Finset.instSetLike.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
        blocks B)
    (hne : @Ne.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) A B) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.signature
    Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.actual PUnit.unit.{1} A B

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"block_intersection_le_one\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"block_intersection_le_one\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).actual (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).variation.2.choose (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).variation.1 (Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"VertexAlgebra\",\"MonsterFanoReconstruction\",\"Intersection\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction, declaration := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
