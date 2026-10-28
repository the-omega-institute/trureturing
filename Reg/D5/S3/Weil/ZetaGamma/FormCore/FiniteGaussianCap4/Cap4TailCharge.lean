import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open _root_.FiniteGaussianCap4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge

namespace Reciprocal
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ n => weight (16 + n) / tailH (16 + n : ℕ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := Summable (R.readout () ()) ∧
    (∑' n : ℕ, weight (16 + n) / tailH (16 + n : ℕ)) ≤ sbar
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := h.1
  simpa only [summable_const_iff, one_ne_zero] using hs
def family : Registration arena (type_of% @complete_tail_reciprocal_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_tail_reciprocal_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change weight (16 + 0) / tailH (16 + 0 : ℕ) ≠
      weight (16 + 1) / tailH (16 + 1 : ℕ)
    norm_num [weight, ratio, tailH]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_tail_reciprocal_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge.Reciprocal.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge.Reciprocal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => weight (16 + n) / tailH (16 + n : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reciprocal
namespace Charge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ u => ∑' n : ℕ, weight (16 + n) * u n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (u : ℕ → ℝ),
    Summable (fun n : ℕ => tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2) →
    Summable (fun n : ℕ => weight (16 + n) * u n) ∧
      rho * (R.readout () () u) ^ 2 ≤
        ∑' n : ℕ, tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hE : Summable (fun n : ℕ =>
      tailH (16 + n : ℕ) * weight (16 + n) * (0 : ℝ) ^ 2) := by simp
  have hb := (h (fun _ => 0) hE).2
  change rho * (1 : ℝ) ^ 2 ≤ ∑' n : ℕ,
    tailH (16 + n : ℕ) * weight (16 + n) * (0 : ℝ) ^ 2 at hb
  norm_num [rho] at hb
def family : Registration arena (type_of% @complete_tail_charge_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_tail_charge_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (fun _ => 0), (fun n => if n = 0 then 1 else 0), ?_⟩
    change (∑' n : ℕ, weight (16 + n) * (0 : ℝ)) ≠
      ∑' n : ℕ, weight (16 + n) * (if n = 0 then (1 : ℝ) else 0)
    simp only [mul_zero, tsum_zero, mul_ite, mul_one, tsum_ite_eq, Nat.add_zero]
    norm_num [weight, ratio]
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_tail_charge_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge.Charge.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge.Charge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => ∑' n : ℕ, weight (16 + n) * u n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Charge
end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge
