import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
import Reg.Support.SingleDependentReadout

/-! The layer value is observed over its complete natural-number domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ p ℓ => lcmPowerF p.1 p.2.2 ℓ)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => lcmPowerF p.1 p.2.1 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 < κ →
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ x' : ℝ, 1 < x' →
      R.readout () ⟨κ, ⟨x, x'⟩⟩ ℓ = lcmPowerF κ x 1 → x ^ ((1 : ℝ) / ℓ) < x'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, hX⟩ := h (κ := 2) (by norm_num)
  let x := max X 2
  have hx : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _)
  have hy : 1 < x ^ ((1 : ℝ) / 2) := Real.one_lt_rpow hx (by norm_num)
  have hb := hX x (le_max_left _ _) 2 (by norm_num) (x ^ ((1 : ℝ) / 2)) hy rfl
  exact (lt_irrefl _) hb

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, ⟨2, 2⟩⟩, 0, 1, ?_⟩
  have hp : 0 < lcmPowerF 2 2 1 := by
    norm_num [lcmPowerF, Real.rpow_ofNat]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hz : lcmPowerF 2 2 0 = 0 := by norm_num [lcmPowerF, Real.rpow_ofNat]
  simpa [actual, realize, hz] using hp.ne

def family : Registration arena (type_of% @layer_boundary_uniform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@layer_boundary_uniform, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@layer_boundary_uniform) (Realization signature) Type Unit where
  unitName := `LcmPowerLayerBoundary.layer_boundary_uniform.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary.family
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
    (fun _ p ℓ => lcmPowerF p.1 p.2.2 ℓ)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
    definition := none
    coordinates := #[0, 3, 7]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "body", "body", "body",
        "body", "domain", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Explicit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ p ℓ => lcmPowerF p.1 (p.2 ^ ((1 : ℝ) / ℓ)) ℓ)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => lcmPowerF p.1 p.2 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, 2⟩, 0, 1, ?_⟩
  have hp : 0 < lcmPowerF 2 2 1 := by
    norm_num [lcmPowerF, Real.rpow_ofNat]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hz : lcmPowerF 2 1 0 = 0 := by simp [lcmPowerF]
  simpa [actual, realize, hz] using hp.ne


abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 < κ → ∀ {x : ℝ},
    Real.exp (max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)))) ≤ x →
    ∀ {ℓ : ℕ}, 2 ≤ ℓ → lcmPowerF κ x 1 < R.readout () ⟨κ, x⟩ ℓ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (by norm_num)
    (x := Real.exp (max 6 (((2 : ℝ) ^ (2 + 1.01)) ^ (1 / (2 - 1)))))
    le_rfl (ℓ := 2) (by norm_num)
  exact (lt_irrefl _) hb

def family : Registration arena (type_of% @layer_boundary_explicit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@layer_boundary_explicit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@layer_boundary_explicit) (Realization signature) Type Unit where
  unitName := `LcmPowerLayerBoundary.layer_boundary_explicit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary.Explicit.family
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
    (fun _ p ℓ => lcmPowerF p.1 (p.2 ^ ((1 : ℝ) / ℓ)) ℓ)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Explicit
namespace Monotone

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℕ)
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p y => lcmPowerF p.1 y p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 < κ → ∀ {ℓ : ℕ}, 1 ≤ ℓ →
    StrictAntiOn (R.readout () ⟨κ, ℓ⟩) (Set.Ioi 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (κ := 2) (by norm_num) (ℓ := 1) (by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num)
    (show (3 : ℝ) ∈ Set.Ioi 1 by norm_num) (by norm_num : (2 : ℝ) < 3)
  exact (lt_irrefl (0 : ℝ)) hb

def family : Registration arena (type_of% @F_strictAntiOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@F_strictAntiOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨⟨2, 1⟩, 3, 2, ?_⟩
    exact (F_strictAntiOn (κ := 2) (by norm_num) (ℓ := 1) (by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num)
      (show (3 : ℝ) ∈ Set.Ioi 1 by norm_num) (by norm_num : (2 : ℝ) < 3)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_strictAntiOn) (Realization signature) Type Unit where
  unitName := `LcmPowerLayerBoundary.F_strictAntiOn.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary.Monotone.family
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
    (fun _ p y => lcmPowerF p.1 y p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Monotone
namespace LayerVariable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ℓ => lcmPowerF p.1 p.2.2 ℓ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => lcmPowerF p.1 p.2.1 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 < κ → ∀ {x x' : ℝ},
    Real.exp (max 6 (((2 : ℝ) ^ (κ + 1.01)) ^ (1 / (κ - 1)))) ≤ x →
    ∀ {ℓ : ℕ}, 2 ≤ ℓ → 1 < x' →
    R.readout () ⟨κ, ⟨x, x'⟩⟩ ℓ = lcmPowerF κ x 1 → x ^ ((1 : ℝ) / ℓ) < x'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x := Real.exp (max 6 (((2 : ℝ) ^ ((2 : ℝ) + 1.01)) ^ (1 / ((2 : ℝ) - 1))))
  have hx : 1 < x := Real.one_lt_exp_iff.mpr
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) (le_max_left _ _))
  have hy : 1 < x ^ ((1 : ℝ) / 2) := Real.one_lt_rpow hx (by norm_num)
  have hb := h (κ := 2) (by norm_num) (x := x) (x' := x ^ ((1 : ℝ) / 2))
    le_rfl (ℓ := 2) (by norm_num) hy rfl
  exact (lt_irrefl _) hb

def family : Registration arena (type_of% @layer_boundary_xl) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@layer_boundary_xl, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨⟨2, ⟨2, 2⟩⟩, 0, 1, ?_⟩
    have hp : 0 < lcmPowerF 2 2 1 := by
      norm_num [lcmPowerF, Real.rpow_ofNat]
      exact div_pos (Real.log_pos (by norm_num)) (by positivity)
    have hz : lcmPowerF 2 2 0 = 0 := by norm_num [lcmPowerF, Real.rpow_ofNat]
    simpa [actual, realize, hz] using hp.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@layer_boundary_xl) (Realization signature) Type Unit where
  unitName := `LcmPowerLayerBoundary.layer_boundary_xl.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary.LayerVariable.family
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
    (fun _ p ℓ => lcmPowerF p.1 p.2.2 ℓ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LayerVariable
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLayerBoundary
