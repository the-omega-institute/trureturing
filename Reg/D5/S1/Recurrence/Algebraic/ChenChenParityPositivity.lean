import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
import Reg.Support.DependentFamily

/-! Source-bound observations for the full integer-step positivity theorem. -/

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.ChenChenParityPositivity

open _root_.D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℤ × (ℕ → ℕ → ℤ) × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => p.2.1 p.2.2 k) (fun e => nomatch e)

/-- The complete integer-step theorem, with its recurrence and all index bounds. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℤ), 3 ≤ r → ∀ (T : ℕ → ℕ → ℤ), Source (-r) T →
    ∀ (n : ℕ), 1 ≤ n → Even n → ∀ (k : ℕ), 1 ≤ k → k ≤ n →
      0 < R.readout () (r, T, n) k

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  obtain ⟨T, h⟩ := result.1.1
  have hh := bad 3 (by omega) T h 2 (by omega) (by decide) 1 (by omega) (by omega)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% even_rows_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨even_rows_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨T, h⟩ := result.1.1
    refine ⟨(3, T, 3), 1, 2, ?_⟩
    change T 3 1 ≠ T 3 2
    have hl := (h.1 3 (by omega)).1
    have hr := h.2 3 2 (by omega) (by omega)
    norm_num [(h.1 2 (by omega)).1, (h.1 2 (by omega)).2] at hr
    omega

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    even_rows_positive (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity.even_rows_positive
    "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.ChenChenParityPositivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- At step minus two the fourth row has a negative second entry. -/
private theorem not_minus_two : ¬ ParityPositivity (-2) := by
  intro hp
  obtain ⟨T, h⟩ := hp.1
  have h₃ := h.2 3 2 (by omega) (by omega)
  norm_num [(h.1 2 (by omega)).1, (h.1 2 (by omega)).2] at h₃
  have h₄ := h.2 4 2 (by omega) (by omega)
  norm_num [(h.1 3 (by omega)).1, h₃] at h₄
  have hp₄ := hp.2 T h 4 (by omega) (by decide) 2 (by omega) (by omega)
  omega

abbrev resultSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def resultActual : Realization resultSignature :=
  realize resultSignature
    (fun _ _ m => @decide (ParityPositivity m) (Classical.propDecidable _))
    (fun e => nomatch e)

def resultRejected : Realization resultSignature :=
  realize resultSignature
    (fun _ _ m => @decide (¬ ParityPositivity m) (Classical.propDecidable _))
    (fun e => nomatch e)

/-- Observe the whole first parameter predicate and preserve the other two clauses. -/
abbrev resultArena : Arena where
  signature := resultSignature
  Law R := R.readout () () (-3) = true ∧
    ParityPositivity (-4) ∧ ParityPositivity (-5)

private theorem result_rejected_law : ¬ resultArena.Law resultRejected := by
  intro h
  have hn : ¬ ParityPositivity (-3) :=
    @of_decide_eq_true (¬ ParityPositivity (-3)) (Classical.propDecidable _) h.1
  exact hn result.1

def resultFamily : Registration resultArena claim where
  actual := resultActual
  bridge := by simp [resultActual, realize, claim]
  variation := ⟨by simpa [resultActual, realize, claim] using result,
    resultRejected, result_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨resultRejected, ?_, rfl, result_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (-3 : ℤ), (-2 : ℤ), ?_⟩
    simp [resultActual, realize, result.1, not_minus_two]

def resultRegistration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    result (Realization resultSignature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity.result "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.ChenChenParityPositivity.resultFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resultArena⟩
  objectArena := .source ⟨resultArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resultArena ⟨resultFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize resultSignature resultActual.readout resultActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
      name := `D5.S1.Recurrence.Algebraic.ChenChenParityPositivity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
