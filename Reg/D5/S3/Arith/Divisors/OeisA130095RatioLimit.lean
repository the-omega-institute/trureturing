import D5.S3.Arith.Divisors.OeisA130095RatioLimit
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The full epsilon telescope, varying the observed sequence as one whole family. -/

namespace Reg.D5.S3.Arith.Divisors.OeisA130095RatioLimit

open _root_.D5.S3.Arith.Divisors.OeisA130095RatioLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature (fun i _ n => if i = role then 0 else a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    |(R.readout false () n : ℝ) / R.readout true () (n - 1) -
      ((1 + Real.sqrt 5) / 2) ^ 2| < ε

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  obtain ⟨N, _, hN⟩ := h 1 (by norm_num)
  have hh := hN N le_rfl
  have hz : |(0 : ℝ) - ((1 + Real.sqrt 5) / 2) ^ 2| < 1 := by
    cases role <;> simpa [rejected, realize] using hh
  have he : ((1 + Real.sqrt 5) / 2) ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  rw [he, abs_of_neg (by linarith [Real.one_lt_goldenRatio])] at hz
  linarith [Real.one_lt_goldenRatio]

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext p n
      simp [actual, rejected, realize, hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change a 1 ≠ a 2
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Arith.Divisors.OeisA130095RatioLimit.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Divisors.OeisA130095RatioLimit.unit
  realizationName := `Reg.D5.S3.Arith.Divisors.OeisA130095RatioLimit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.OeisA130095RatioLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.OeisA130095RatioLimit
