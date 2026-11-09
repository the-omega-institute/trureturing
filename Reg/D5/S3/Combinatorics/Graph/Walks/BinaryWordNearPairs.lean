import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs
import Reg.Support.DependentFamily

/-! Full-telescope source registrations for physical representation and count. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
open _root_.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs

namespace Representation

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := Sym2 Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q p => Near q.1 q.2 p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ L D : ℕ, Function.Injective Code.pair ∧
    ∀ p : Sym2 Word, r.readout () (L, D) p ↔
      ∃! c : Code, c.Valid L D ∧ c.pair = p

private theorem not_diagonal (L D : ℕ) (w : Word) : ¬ Near L D s(w, w) := by
  rintro ⟨u, v, hp, hn, _⟩
  rcases Sym2.eq_iff.mp hp with h | h
  · exact hn (h.1.symm.trans h.2)
  · exact hn (h.2.symm.trans h.1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr := (h 0 0).2 s([], []) |>.mp True.intro
  exact not_diagonal 0 0 [] ((canonical_representation 0 0).2 _ |>.mpr hr)

def source_registration : Registration arena (type_of% canonical_representation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨canonical_representation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1, 1), s([], []), s([], [true]), ?_⟩
    change Near 1 1 s([], []) ≠ Near 1 1 s([], [true])
    intro h
    apply not_diagonal 1 1 []
    apply Eq.mpr h
    exact ⟨[], [true], rfl, by decide, by decide, by decide,
      by simp [distance, lcp]⟩

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_representation) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs.Representation.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs.Representation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q p => Near q.1 q.2 p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Representation

namespace Counting

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ L D => pairCount L D) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ L D : ℕ, r.readout () L D = sourceSum L D

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  change 1 = sourceSum 0 0 at hh
  norm_num [sourceSum] at hh

noncomputable def source_registration : Registration arena (type_of% exact_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change pairCount 1 0 ≠ pairCount 1 1
    rw [exact_count, exact_count]
    norm_num [sourceSum] <;> omega

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_count) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs.Counting.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs.Counting.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L D => pairCount L D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Counting

#print axioms Representation.source_registration
#print axioms Counting.source_registration

end Reg.D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs
