import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

/-! Source audit of diagram area in the square-modulus congruence. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP

abbrev signature : Signature where
  Params := Unit
  State _ := YoungDiagram
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ μ => (μ.card : ℤ)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law observed := ∀ (m : ℕ) (μ : YoungDiagram), IsCMP m μ →
    0 < μ.rowLen 0 → μ.transpose = μ →
      ((m : ℤ) - 1) ^ 2 ∣ observed.readout () () μ - (2 * (μ.rowLen 0 : ℤ) - 1)

private def oneCell : YoungDiagram where
  cells := {(0, 0)}
  isLowerSet := by
    intro b a hab hb
    change b ∈ ({(0, 0)} : Finset (ℕ × ℕ)) at hb
    change a ∈ ({(0, 0)} : Finset (ℕ × ℕ))
    rw [Finset.mem_singleton] at hb ⊢
    subst b
    exact Prod.ext (Nat.eq_zero_of_le_zero hab.1) (Nat.eq_zero_of_le_zero hab.2)

private theorem oneCell_mem (i j : ℕ) : (i, j) ∈ oneCell ↔ i = 0 ∧ j = 0 := by
  change (i, j) ∈ ({(0, 0)} : Finset (ℕ × ℕ)) ↔ _
  simp

private theorem oneCell_transpose : oneCell.transpose = oneCell := by
  apply SetLike.ext
  intro ⟨i, j⟩
  rw [YoungDiagram.mem_transpose]
  exact (oneCell_mem j i).trans (and_comm.trans (oneCell_mem i j).symm)

private theorem oneCell_top : oneCell.rowLen 0 = 1 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, oneCell_mem, Nat.lt_one_iff]
  simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmary : IsMAry 3 oneCell := by
    intro i hi
    have hcell : (i, 0) ∈ oneCell := YoungDiagram.mem_iff_lt_rowLen.mpr hi
    have hzero := ((oneCell_mem i 0).mp hcell).1
    subst i
    exact ⟨0, oneCell_top⟩
  have hcmp : IsCMP 3 oneCell := ⟨hmary, oneCell_transpose ▸ hmary⟩
  have hbad := h 3 oneCell hcmp (by simp [oneCell_top]) oneCell_transpose
  norm_num [rejected, realize, oneCell_top] at hbad

def familyRegistration : Registration arena (type_of% (@square_modulus)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨square_modulus, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro role
    cases role
    refine ⟨(), ⊥, oneCell, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@square_modulus) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP.square_modulus.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Combinatorics.Partitions.OddPowerSelfConjugateCMP
