import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ThirtyWheelSquarefree
import Reg.Support.DependentFamily

set_option autoImplicit false
open Finset
open scoped BigOperators
open _root_.D5.S3.Weil.Mertens.ThirtyWheelSquarefree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.ThirtyWheelSquarefree
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun role _ X => if role then ∑ d ∈ good X, (d:ℚ) else ((good X).card:ℚ))
    (fun e => nomatch e)

def changed (i : Bool) : Realization signature :=
  realize signature
    (fun role _ X => if role = i then -2 else actual.readout role () X)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ,
    (170*(X:ℚ)-168*(Nat.sqrt X:ℚ)-1083)/675 ≤ R.readout false () X ∧
    (85*(X:ℚ)^2-192*(X:ℚ)*Nat.sqrt X-402*(X:ℚ)-675)/675 ≤ R.readout true () X

private theorem changed_law (i : Bool) : ¬ arena.Law (changed i) := by
  intro h
  have hz := h 0
  cases i <;> norm_num [changed, realize] at hz

def family : Registration arena (type_of% @count_weight_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_weight_lower_bound, changed false, changed_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, rfl, changed_law i⟩
      intro j hji
      funext p X
      cases p
      simp [changed, realize, hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 7, ?_⟩
    have hs : Squarefree (7:ℕ) := (show Nat.Prime 7 by norm_num).squarefree
    have hc : Nat.Coprime 7 30 := by decide
    cases i <;> norm_num [actual, realize, good, Finset.filter_singleton, hs, hc]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_weight_lower_bound) (Realization signature) Type Unit where
  unitName := `ThirtyWheelSquarefree.count_weight_lower_bound.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.ThirtyWheelSquarefree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun role _ X => if role then ∑ d ∈ good X, (d:ℚ) else ((good X).card:ℚ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ThirtyWheelSquarefree
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg", "arg", "arg"]
        booleanPredicate := false },
      { path := #["body", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg", "arg"]
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Weil.Mertens.ThirtyWheelSquarefree
