import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! The full weighted-family telescope with its two layer cardinalities observed. -/

namespace Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
open _root_.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Two layer-cardinality observations on finite families over arbitrary carriers. -/
abbrev signature : Signature where
  Params := Type u
  State α := Finset (Finset α)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ F => F.card) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the two rank-layer cardinalities vary; every original hypothesis remains. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α]
    (ω : ℕ → ℝ) (C D : Finset (Finset α)),
    4 ≤ Fintype.card α → (∀ r, 0 ≤ ω r) →
    IsUpperSet (C : Set (Finset α)) → IsUpperSet (D : Set (Finset α)) →
    (∀ s ∈ C, ∀ t ∈ D, (s ∩ t).Nonempty) →
    ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω C →
    ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω D →
    R.readout false α (C.slice 1) + 2 ≤ R.readout true α (C.slice (Fintype.card α - 1))

private def largeFamily : Finset (Finset (ULift.{u} (Fin 4))) :=
  univ.filter (fun s => 3 ≤ s.card)

private theorem large_upper : IsUpperSet (largeFamily.{u} : Set (Finset (ULift.{u} (Fin 4)))) := by
  intro s t hst hs
  have hs' : 3 ≤ s.card := (mem_filter.mp hs).2
  exact mem_filter.mpr ⟨mem_univ _, hs'.trans (card_le_card hst)⟩

private theorem large_cross :
    ∀ s ∈ largeFamily.{u}, ∀ t ∈ largeFamily.{u}, (s ∩ t).Nonempty := by decide

private theorem large_mass :
    (1 : ℝ) + 1 < weightedMass (fun _ => 1) largeFamily.{u} := by
  have hc : largeFamily.{u}.card = 5 := by decide
  norm_num [weightedMass, hc]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (α := ULift.{u} (Fin 4)) (fun _ => 1) largeFamily largeFamily
    (by decide) (fun _ => by norm_num) large_upper large_upper large_cross
    (by simpa using large_mass.{u}) (by simpa using large_mass.{u})
  change 0 + 2 ≤ (0 : ℕ) at hh
  omega

/-- Change only one of the two source observations. -/
def intervention (i : Bool) : Realization signature.{u} :=
  realize signature (fun j _ F => if j = i then (if i = false then 4 else 0) else F.card)
    (fun e => nomatch e)

private theorem intervention_law (i : Bool) : ¬ arena.{u}.Law (intervention i) := by
  intro h
  have hh := h (α := ULift.{u} (Fin 4)) (fun _ => 1) largeFamily largeFamily
    (by decide) (fun _ => by norm_num) large_upper large_upper large_cross
    (by simpa using large_mass.{u}) (by simpa using large_mass.{u})
  have hl : (largeFamily.{u}.slice 1).card = 0 := by decide
  have hr : (largeFamily.{u}.slice 3).card = 4 :=
    by decide
  cases i <;> norm_num [intervention, realize, hl, hr] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), ∅, {∅}, ?_⟩
  simp [actual, realize]

def source_registration :
    Registration arena.{u} (type_of% @weighted_cross_intersecting_layer_gap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_cross_intersecting_layer_gap.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hj
      funext α F
      simp [actual, intervention, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_cross_intersecting_layer_gap.{u}) (Realization signature.{u}) (Bool) Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ F => F.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

/-- Four independently observed layer-cardinality occurrences of the paired law. -/
abbrev variableSignature : Signature where
  Params := Type u
  State α := Finset (Finset α)
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def variableActual : Realization variableSignature.{u} :=
  realize variableSignature (fun _ _ F => F.card) (fun e => nomatch e)

def variableRejected : Realization variableSignature.{u} :=
  realize variableSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original telescope, with only the four conclusion readouts varied. -/
abbrev variableArena : Arena where
  signature := variableSignature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α]
    (ω : ℕ → ℝ) (C D : Finset (Finset α)) (k : ℕ),
    3 ≤ Fintype.card α → k ≤ Fintype.card α - 3 → (∀ r, 0 ≤ ω r) →
    IsUpperSet (C : Set (Finset α)) → IsUpperSet (D : Set (Finset α)) →
    (∀ s ∈ C, ∀ t ∈ D, (s ∩ t).Nonempty) →
    (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * ω (Fintype.card α - j)) <
      weightedMass ω C →
    (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * ω (Fintype.card α - j)) <
      weightedMass ω D →
    R.readout 0 α (C.slice 1) + (k + 1) ≤
      R.readout 1 α (C.slice (Fintype.card α - 1)) ∧
    R.readout 2 α (D.slice 1) + (k + 1) ≤
      R.readout 3 α (D.slice (Fintype.card α - 1))

private theorem variable_rejected_law : ¬ variableArena.{u}.Law variableRejected := by
  intro h
  have hh := h (α := ULift.{u} (Fin 4)) (fun _ => 1) largeFamily largeFamily 1
    (by decide) (by decide) (fun _ => by norm_num) large_upper large_upper large_cross
    (by simpa [sum_range_succ] using large_mass.{u})
    (by simpa [sum_range_succ] using large_mass.{u})
  change 0 + (1 + 1) ≤ (0 : ℕ) ∧ 0 + (1 + 1) ≤ (0 : ℕ) at hh
  omega

/-- A whole-family intervention fixing the other three observed functions. -/
def variableIntervention (i : Fin 4) : Realization variableSignature.{u} :=
  realize variableSignature
    (fun j _ F => if j = i then (if i = 0 ∨ i = 2 then 4 else 0) else F.card)
    (fun e => nomatch e)

private theorem variable_intervention_law (i : Fin 4) :
    ¬ variableArena.{u}.Law (variableIntervention i) := by
  intro h
  have hh := h (α := ULift.{u} (Fin 4)) (fun _ => 1) largeFamily largeFamily 1
    (by decide) (by decide) (fun _ => by norm_num) large_upper large_upper large_cross
    (by simpa [sum_range_succ] using large_mass.{u})
    (by simpa [sum_range_succ] using large_mass.{u})
  have hl : (largeFamily.{u}.slice 1).card = 0 := by decide
  have hr : (largeFamily.{u}.slice 3).card = 4 := by decide
  fin_cases i <;> norm_num [variableIntervention, realize, hl, hr] at hh

private theorem variable_dependence :
    ObservationalDependence variableSignature.{u} variableActual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), ∅, {∅}, ?_⟩
  simp [variableActual, realize]

def variable_source_registration :
    Registration variableArena.{u}
      (type_of% @weighted_cross_intersecting_layer_gap_of_binomial_threshold.{u}) where
  actual := variableActual
  bridge := Iff.rfl
  variation := ⟨@weighted_cross_intersecting_layer_gap_of_binomial_threshold.{u},
    variableRejected, variable_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨variableIntervention i, ?_, rfl, variable_intervention_law i⟩
      intro j hj
      funext α F
      simp [variableActual, variableIntervention, realize, hj]
    · intro e
      exact nomatch e
  dependence := variable_dependence

def variable_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_cross_intersecting_layer_gap_of_binomial_threshold.{u})
    (Realization variableSignature.{u}) (Fin 4) Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.variable_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap.variable_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨variableArena⟩
  objectArena := .source ⟨variableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source variableArena ⟨variable_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize variableSignature.{u}
    (fun _ _ F => F.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms variable_source_registration
#print axioms variable_registration

end
end Reg.D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
