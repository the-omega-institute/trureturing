import D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

noncomputable section

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual

open Real Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport (theta)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
open _root_.D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ P =>
    prefixH P ^ ((2 : ℝ) / 3) * prefixEll P *
      (integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P)))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun P : ℕ => R.readout () () P) atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3)))

private theorem limit_ne_zero : (3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 :=
  (show 0 < (3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3) by positivity).ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3))) := h
  exact limit_ne_zero (tendsto_nhds_unique hzero tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  by_contra! same
  have zero : ∀ P : ℕ, actual.readout () () P = 0 := by
    intro P
    rw [← same P]
    simp [actual, realize, prefixEll, prefixH, theta]
  have lim : Tendsto (fun P : ℕ => actual.readout () () P) atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3))) :=
    integer_infimum_cubic_activation_residual
  have limZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ((3 / 2 : ℝ) * (3 : ℝ) ^ ((1 : ℝ) / 3))) :=
    lim.congr' (Filter.Eventually.of_forall zero)
  exact limit_ne_zero (tendsto_nhds_unique limZero tendsto_const_nhds)

def registration : Registration arena (type_of% (@integer_infimum_cubic_activation_residual)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integer_infimum_cubic_activation_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integer_infimum_cubic_activation_residual)
    (type_of% (realize signature
      (fun _ _ P => prefixH P ^ ((2 : ℝ) / 3) * prefixEll P *
        (integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P)))
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual.integer_infimum_cubic_activation_residual.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ P => prefixH P ^ ((2 : ℝ) / 3) * prefixEll P *
      (integerInfimum (Nat.primesLE P) - activationSum (Nat.primesLE P) (prefixPrice P)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.CubicActivationResidual
