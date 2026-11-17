import D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/- Direct source-bound audit attempt for the exact normalized real-image limit.
The error-to-zero theorem and the supplier audits remain separate obligations.
No producer validation is asserted by the existence of this record. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
open Real Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open _root_.D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ _ P =>
    let H := theta (Nat.primesLE P)
    let ell := log H
    let M := sqrt H * ell * sqrt ell *
      (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))
    ell * (M - 8) + 8 * log ell)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 17) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun P : ℕ => R.readout () () P) atTop (𝓝 (16 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad : (17 : ℝ) = 16 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, ?_⟩
  by_contra! same
  have zero : ∀ P : ℕ, actual.readout () () P = 0 := by
    intro P
    rw [← same P]
    simp [actual, realize, theta]
  have lim : Tendsto (fun P : ℕ => actual.readout () () P) atTop (𝓝 (16 : ℝ)) :=
    actual_real_infimum_second_order
  have limZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (16 : ℝ)) :=
    lim.congr' (Filter.Eventually.of_forall zero)
  have bad : (0 : ℝ) = 16 := tendsto_nhds_unique tendsto_const_nhds limZero
  norm_num at bad

def registration : Registration arena (type_of% (@actual_real_infimum_second_order)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_real_infimum_second_order, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_real_infimum_second_order)
    (type_of% (realize signature
      (fun _ _ P =>
        let H := theta (Nat.primesLE P)
        let ell := log H
        let M := sqrt H * ell * sqrt ell *
          (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))
        ell * (M - 8) + 8 * log ell)
      (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder.actual_real_infimum_second_order.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder.registration
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
    (fun _ _ P =>
      let H := theta (Nat.primesLE P)
      let ell := log H
      let M := sqrt H * ell * sqrt ell *
        (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))
      ell * (M - 8) + 8 * log ell)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
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

end Reg.D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
