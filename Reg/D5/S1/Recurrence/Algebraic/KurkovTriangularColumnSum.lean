import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum

open _root_.D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

abbrev signature : Signature where
  Params := ℕ → ℕ → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A n => A n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

/-- The existence conjunct, lawful-array hypotheses and every sum index are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∃ A : ℕ → ℕ → ℕ, IsArray A) ∧
    ∀ A : ℕ → ℕ → ℕ, IsArray A → ∀ n k : ℕ, 1 ≤ k →
      (R.readout () A n (k + f k + 1) : ℚ) =
        ∑ j ∈ range (n + 1), (A j k : ℚ) *
          ((n + f k).factorial : ℚ) / ((f k + j).factorial : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA⟩ := h.1
  have he := h.2 A hA 0 1 (by decide)
  simp only [rejected, realize, sum_range_one, hA.1, Nat.cast_one,
    Nat.cast_zero, Nat.zero_add, Nat.add_zero, one_mul] at he
  have hz : ((f 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (f 1)
  rw [div_self hz] at he
  exact zero_ne_one he

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    obtain ⟨A, hA⟩ := result.1
    refine ⟨A, 0, 1, ?_⟩
    intro he
    have h := congrFun he 0
    change A 0 0 = A 1 0 at h
    rw [hA.1, hA.2.1 1 (by decide)] at h
    exact one_ne_zero h

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    result (Realization signature) Unit Unit where
  unitName :=
    `D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum.result.__information_unit
  realizationName :=
    `Reg.D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum.family
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
    owner := `D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum
