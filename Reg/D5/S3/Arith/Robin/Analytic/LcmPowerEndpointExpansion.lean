import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

private theorem psi_three_gt_one : 1 < Chebyshev.psi (3 : ℝ) := by
  change 1 < Chebyshev.psi ((3 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto 3]
  have hL : Nat.lcmUpto 3 = 6 := by decide
  rw [hL]
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)).mpr
  exact Real.exp_one_lt_three.trans (by norm_num)

namespace NonnegativeCorrection

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 0 < κ → ∀ x : ℝ, R.readout () () 0 (C κ x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (κ := 1) (by norm_num) 0
  exact hh

def family : Registration arena (type_of% @C_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@C_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@C_nonneg) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.C_nonneg.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.NonnegativeCorrection.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NonnegativeCorrection

namespace PositiveRatio

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ x : ℝ}, 1 < κ → 1 < Chebyshev.psi x →
    R.readout () () 0 (G κ (Nat.lcmUpto ⌊x⌋₊))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (κ := 2) (x := 3) (by norm_num) psi_three_gt_one

def family : Registration arena (type_of% @G_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@G_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    change (fun y : ℝ => 0 < y) = (fun y : ℝ => 1 < y) at he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num)
    exact (lt_irrefl _ hh)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@G_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.G_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.PositiveRatio.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveRatio

namespace ExactExpansion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ x : ℝ}, 1 < κ → 1 < Chebyshev.psi x →
    R.readout () () (Real.log (G κ (Nat.lcmUpto ⌊x⌋₊)))
      (-κ * B x - κ * A x - κ * J x + T κ x + C κ x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (κ := 2) (x := 3) (by norm_num) psi_three_gt_one

def family : Registration arena (type_of% @log_G_decomposition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_G_decomposition, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_G_decomposition) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.log_G_decomposition.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.ExactExpansion.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExactExpansion


namespace Clock
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => Filter ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 𝓝 (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun x : ℝ => (Real.sqrt x * Real.log x) * J x)
    atTop (V.readout () () 1)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique J_scaled_limit h
  norm_num at he

def family : Registration arena (type_of% @J_scaled_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨J_scaled_limit, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact fun he => zero_ne_one (nhds_injective he)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@J_scaled_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.J_scaled_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.Clock.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Clock

namespace Layers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => Filter ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 𝓝 (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun x : ℝ => (Real.sqrt x * Real.log x) * A x)
    atTop (V.readout () () 2)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have he : (2 : ℝ) = 0 := tendsto_nhds_unique A_scaled_limit h
  norm_num at he

def family : Registration arena (type_of% @A_scaled_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨A_scaled_limit, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact fun he => zero_ne_one (nhds_injective he)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A_scaled_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.A_scaled_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.Layers.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Layers

namespace EulerTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
    R.readout () () (2 - epsilon) (Real.sqrt x * Real.log x *
      (Real.log (riemannZeta ((3 / 2 : ℝ) : ℂ)).re +
        ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          Real.log (1 - (p : ℝ) ^ (-(3 / 2 : ℝ)))))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := (h 1 zero_lt_one).exists
  exact hx

def family : Registration arena (type_of% @endpoint_euler_tail_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_euler_tail_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    change (fun y : ℝ => 0 < y) = (fun y : ℝ => 1 < y) at he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num)
    exact (lt_irrefl _ hh)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_euler_tail_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.endpoint_euler_tail_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion.EulerTail.family
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
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EulerTail

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
