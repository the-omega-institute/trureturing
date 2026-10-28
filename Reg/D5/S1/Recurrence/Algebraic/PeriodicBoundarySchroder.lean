import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder
import Reg.Support.DependentFamily

/-! The two original array observations are retained over every natural diagonal index. -/

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder

open _root_.D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role _ n => if role then P f2 (n + 1) (n + 1) else P f3 (n + 1) (n + 1))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout true () n = Nat.largeSchroder n ∧
    R.readout false () n = Nat.largeSchroder n

def rejected (role : Bool) : Realization signature := realize signature
  (fun r p n => if r = role then 0 else actual.readout r p n)
  (fun e => nomatch e)

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h 0
  cases role <;> simp [rejected, realize] at hh

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected true, rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p n
      simp [rejected, realize, hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    cases i
    · change P f3 (0 + 1) (0 + 1) ≠ P f3 (1 + 1) (1 + 1)
      rw [(result 0).2, (result 1).2]
      norm_num
    · change P f2 (0 + 1) (0 + 1) ≠ P f2 (1 + 1) (1 + 1)
      rw [(result 0).1, (result 1).1]
      norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    result (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder.result "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder.family
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
    owner := `D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder
