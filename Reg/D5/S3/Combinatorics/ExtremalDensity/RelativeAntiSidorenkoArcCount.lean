import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount
import Reg.Support.DependentFamily

/-! The arc count of each candidate pattern is observed in the exact existential law. -/

namespace Reg.D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount

open _root_.D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := ℕ
  State n := Digraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ D => arcCount D) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the occurrence of the arc count in the residue clause is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ (n : ℕ) (D : Digraph (Fin n)),
    Oriented D ∧ D.toSimpleGraphInclusive.Connected ∧
      r.readout () n D % 4 = 3 ∧ RelativelyAntiSidorenko.{u} D

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  rintro ⟨n, D, _, _, h, _⟩
  change 0 % 4 = 3 at h
  exact (by decide : ¬ 0 % 4 = (3 : ℕ)) h

theorem arc_count_varies :
    ∃ (D E : Digraph (Fin 2)), arcCount D ≠ arcCount E := by
  let D : Digraph (Fin 2) := ⟨fun _ _ => False⟩
  let E : Digraph (Fin 2) := ⟨fun a b => a = 0 ∧ b = 1⟩
  have hD : IsEmpty {p : Fin 2 × Fin 2 // D.Adj p.1 p.2} := ⟨fun p => p.property⟩
  have hE : Nonempty {p : Fin 2 × Fin 2 // E.Adj p.1 p.2} := ⟨⟨(0, 1), rfl, rfl⟩⟩
  exact ⟨D, E, by
    rw [show arcCount D = 0 from Nat.card_of_isEmpty]
    exact (Nat.ne_of_gt (Nat.card_pos (α := {p : Fin 2 × Fin 2 // E.Adj p.1 p.2}))).symm⟩

def source_registration : Registration arena.{u} (type_of% @question_5_3.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨question_5_3.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨D, E, h⟩ := arc_count_varies
    exact ⟨2, D, E, h⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@question_5_3.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount.unit
  realizationName := `Reg.D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ D => arcCount D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount
