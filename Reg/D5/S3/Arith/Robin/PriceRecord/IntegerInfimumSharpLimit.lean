import D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

noncomputable section

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit

open Real Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary
open _root_.D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ P => sqrt (prefixH P) * prefixEll P *
    (integerInfimum (Nat.primesLE P) -
      (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun P : ℕ => R.readout () () P) atTop (𝓝 (2 * sqrt 2))

private theorem limit_pos : 0 < (2 * sqrt 2 : ℝ) :=
  mul_pos (by norm_num) (sqrt_pos.mpr (by norm_num))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (2 * sqrt 2)) := h
  exact limit_pos.ne' (tendsto_nhds_unique hzero tendsto_const_nhds)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  by_contra! same
  have zero : ∀ P : ℕ, actual.readout () () P = 0 := by
    intro P
    rw [← same P]
    simp [actual, realize, prefixH, theta]
  have lim : Tendsto (fun P : ℕ => actual.readout () () P) atTop (𝓝 (2 * sqrt 2)) :=
    actual_integer_infimum_sharp_limit
  have limZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (2 * sqrt 2)) :=
    lim.congr' (Filter.Eventually.of_forall zero)
  exact limit_pos.ne' (tendsto_nhds_unique limZero tendsto_const_nhds)

def registration : Registration arena (type_of% (@actual_integer_infimum_sharp_limit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_integer_infimum_sharp_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_integer_infimum_sharp_limit)
    (type_of% (realize signature
      (fun _ _ P => sqrt (prefixH P) * prefixEll P *
        (integerInfimum (Nat.primesLE P) -
          (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))))
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit.actual_integer_infimum_sharp_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit.registration
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
    (fun _ _ P => sqrt (prefixH P) * prefixEll P *
      (integerInfimum (Nat.primesLE P) -
        (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
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

end Reg.D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
