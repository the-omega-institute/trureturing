import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.SubmodularGreedyApproximation

/-! Source-bound audit for the cardinality-greedy submodular guarantee. -/

namespace Reg.D5.S3.Resource.SubmodularGreedyApproximation

open _root_.D5.S3.Resource.SubmodularGreedyApproximation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

abbrev signature : Signature.{0, u + 1, 0, 0, 0} where
  Params := Unit
  State _ := Type u → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev claim : Prop := ∀ {α : Type u} [DecidableEq α]
    (f : Finset α → ℝ) (hfzero : f ∅ = 0)
    (hfmono : _root_.D5.S3.Resource.SubmodularGreedyApproximation.Monotone f)
    (hfsub : Submodular f) (k : ℕ) (hk : 0 < k)
    (O : Finset α) (hO : O.card ≤ k)
    (S : ℕ → Finset α) (e : ℕ → α)
    (hS0 : S 0 = ∅)
    (hstep : ∀ i, i < k → S (i + 1) = insert (e i) (S i))
    (hgreedy : ∀ i, i < k → ∀ x, x ∉ S i →
      marginal f (S i) x ≤ marginal f (S i) (e i)),
    f (S k) ≥ (1 - Real.exp (-1)) * f O

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ p => p (ULift.{u} PUnit)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena.{0, u + 1, 0, 0, 0} where
  signature := signature.{u}
  Law r := r.readout () () (fun _ : Type u => claim.{u})

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), (fun _ : Type u => True), (fun _ : Type u => False), ?_⟩
  intro h
  change True = False at h
  exact Eq.mp h True.intro

def source_registration : Registration arena.{u} (type_of% @cardinality_greedy_one_sub_exp.{u}) where
  actual := actual
  bridge := by rfl
  variation := ⟨by
    change claim
    exact @cardinality_greedy_one_sub_exp.{u}, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected.{u}, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law.{u}⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cardinality_greedy_one_sub_exp.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Resource.SubmodularGreedyApproximation.unit
  realizationName := `Reg.D5.S3.Resource.SubmodularGreedyApproximation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ p => p (ULift.{u} PUnit)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Resource.SubmodularGreedyApproximation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Resource.SubmodularGreedyApproximation.cardinality_greedy_one_sub_exp
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Resource.SubmodularGreedyApproximation
