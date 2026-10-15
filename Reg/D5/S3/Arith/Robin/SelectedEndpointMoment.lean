import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.SelectedEndpointMoment
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open _root_.D5.S3.Arith.Robin.SelectedEndpointMoment
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment (width endpoint)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.SelectedEndpointMoment

namespace MonotoneMinimum

abbrev signature : Signature where
  Params := Measure ℝ × (ℝ → ℝ) × ℝ × ℝ × ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => ∫ t in S, p.2.1 t ∂p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {μ : Measure ℝ} {f : ℝ → ℝ} {l b r : ℝ} {S : Set ℝ},
    l ≤ b → b ≤ r → MeasurableSet S → S ⊆ Icc l r → MonotoneOn f (Icc l r) →
    μ S ≠ ⊤ → μ (Icc l b) ≠ ⊤ → IntegrableOn f S μ → IntegrableOn f (Icc l b) μ →
    μ.real S = μ.real (Icc l b) → (∫ t in Icc l b, f t ∂μ) ≤ R.readout () (μ, f, l, b, r) S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h (μ := volume) (f := fun _ : ℝ => 0)
    (l := 0) (b := 0) (r := 0) (S := ∅) le_rfl le_rfl MeasurableSet.empty
    (empty_subset _) (by intro _ _ _ _ _; exact le_rfl)
    (by simp) (by simp [Real.volume_Icc])
    (by simp) (by simp) (by simp [measureReal_def, Real.volume_Icc])
  change (∫ t in Icc (0 : ℝ) 0, (0 : ℝ)) ≤ -1 at ht
  norm_num at ht

def family : Registration arena (type_of% (@monotone_window_integral_minimum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monotone_window_integral_minimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(volume, (fun _ : ℝ => 1), 0, 1, 1), ∅, Icc 0 1, ?_⟩
    change (∫ _t in (∅ : Set ℝ), (1 : ℝ)) ≠ ∫ _t in Icc (0 : ℝ) 1, (1 : ℝ)
    simp [measureReal_def, Real.volume_Icc]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monotone_window_integral_minimum)
    (type_of% (realize signature (fun _ p S => ∫ t in S, p.2.1 t ∂p.1)
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.SelectedEndpointMoment.monotone_window_integral_minimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.SelectedEndpointMoment.MonotoneMinimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => ∫ t in S, p.2.1 t ∂p.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.SelectedEndpointMoment
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MonotoneMinimum

namespace ActualMoment

abbrev signature : Signature where
  Params := ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a S => selectedMoment a S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ} {S : Set ℝ}, 0 < a → MeasurableSet S → S ⊆ Ioc 0 a →
    ∃ τ ∈ Ioo 0 a, endpoint τ = a ∧
      (∫ t in Icc τ (τ + volume.real (selectedTail a S)),
        ((endpoint t - a) / width a) ^ 2) ≤ R.readout () a S ∧
      volume.real (selectedTail a S) ^ 3 / (3 * (a - τ) ^ 2) ≤ R.readout () a S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨τ, _, _, _, ht⟩ := h (a := 1) (S := ∅) (by norm_num)
    MeasurableSet.empty (empty_subset _)
  change volume.real (selectedTail 1 ∅) ^ 3 / (3 * (1 - τ) ^ 2) ≤ -1 at ht
  norm_num [selectedTail] at ht

private lemma whole_tail : selectedTail 2 (Ioc 0 2) = Ioc 1 2 := by
  ext t
  have hroot : endpoint 1 = 2 := by norm_num [endpoint, width]
  constructor
  · intro ht
    have ht' := ht.1
    refine ⟨?_, ht'.2⟩
    by_contra h
    have hw := Real.rpow_le_rpow ht'.1.le (not_lt.mp h)
      (by norm_num : 0 ≤ (4 / 5 : ℝ))
    have hb : endpoint t ≤ 2 := by
      dsimp [endpoint, width] at *
      norm_num at hw
      linarith
    exact (not_lt_of_ge hb) ht.2
  · intro ht
    refine ⟨⟨by linarith [ht.1], ht.2⟩, ?_⟩
    have hw := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) ht.1.le
      (by norm_num : 0 ≤ (4 / 5 : ℝ))
    dsimp [endpoint, width]
    norm_num at hw
    linarith [ht.1]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, ∅, Ioc 0 2, ?_⟩
  change selectedMoment 2 ∅ ≠ selectedMoment 2 (Ioc 0 2)
  have hzero : selectedMoment 2 ∅ = 0 := by simp [selectedMoment, selectedTail]
  obtain ⟨τ, hτ, _, _, hbound⟩ := selected_endpoint_moment_bounds (a := 2)
    (S := Ioc 0 2) (by norm_num) measurableSet_Ioc (Subset.rfl)
  rw [whole_tail] at hbound
  have hm : volume.real (Ioc (1 : ℝ) 2) = 1 := by
    norm_num [measureReal_def, Real.volume_Ioc]
  rw [hm] at hbound
  have hpos : 0 < (1 : ℝ) ^ 3 / (3 * (2 - τ) ^ 2) := by
    have hd : 0 < 2 - τ := sub_pos.mpr hτ.2
    positivity
  rw [hzero]
  exact ne_of_lt (hpos.trans_le hbound)

def family : Registration arena (type_of% (@selected_endpoint_moment_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@selected_endpoint_moment_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@selected_endpoint_moment_bounds)
    (type_of% (realize signature (fun _ a S => selectedMoment a S) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.SelectedEndpointMoment.selected_endpoint_moment_bounds.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.SelectedEndpointMoment.ActualMoment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a S => selectedMoment a S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.SelectedEndpointMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ActualMoment

#print axioms MonotoneMinimum.registration
#print axioms ActualMoment.registration

end Reg.D5.S3.Arith.Robin.SelectedEndpointMoment
