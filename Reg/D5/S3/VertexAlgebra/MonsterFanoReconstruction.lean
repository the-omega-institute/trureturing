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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.complement_symmDiff_mem) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ block other => univ.{0} \ (block ∆ other))
    (fun empty => nomatch empty))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "VertexAlgebra") "MonsterFanoReconstruction") "complement_symmDiff_mem") "Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction/Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ block other => univ.{0} \ (block ∆ other))
    (fun empty => nomatch empty)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, definition := none, coordinates := #[3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.VertexAlgebra.MonsterFanoReconstruction.block_intersection_le_one) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ block other => (block ∩ other).card.{0})
    (fun empty => nomatch empty))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "VertexAlgebra") "MonsterFanoReconstruction") "block_intersection_le_one") "Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction/Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction.Intersection.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ block other => (block ∩ other).card.{0})
    (fun empty => nomatch empty)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.VertexAlgebra.MonsterFanoReconstruction, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Intersection

end Reg.D5.S3.VertexAlgebra.MonsterFanoReconstruction
