import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Circle.Orbit.TernaryPhaseZeroCount

/-! Source-bound audit of the complete ternary physical-label count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount
open scoped BigOperators

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n u =>
    (Finset.univ.filter (fun A : Finset (Fin n) => (∑ i ∈ A, u i) = 0)).card)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (u : Fin n → ℤ),
    (∀ i, u i = -1 ∨ u i = 0 ∨ u i = 1) →
    R.readout () n u =
      2 ^ (Finset.univ.filter (fun i => u i = 0)).card *
        Nat.choose
          ((Finset.univ.filter (fun i => u i = 1)).card +
            (Finset.univ.filter (fun i => u i = -1)).card)
          (Finset.univ.filter (fun i => u i = 1)).card

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (fun i => nomatch i) (fun i => nomatch i)
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  have hz := zero_subsets_card 1 (fun _ => 0) (by simp)
  have ho := zero_subsets_card 1 (fun _ => 1) (by simp)
  change (Finset.univ.filter (fun A : Finset (Fin 1) =>
    (∑ _i ∈ A, (0 : ℤ)) = 0)).card ≠
      (Finset.univ.filter (fun A : Finset (Fin 1) =>
        (∑ _i ∈ A, (1 : ℤ)) = 0)).card
  rw [hz, ho]
  norm_num

def familyRegistration : Registration arena (type_of% (@zero_subsets_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zero_subsets_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@zero_subsets_card) (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount.zero_subsets_card.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n u =>
    (Finset.univ.filter (fun A : Finset (Fin n) => (∑ i ∈ A, u i) = 0)).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.TernaryPhaseZeroCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.TernaryPhaseZeroCount
