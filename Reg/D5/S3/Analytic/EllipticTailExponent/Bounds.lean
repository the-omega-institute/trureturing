import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.EllipticTailExponent.Bounds
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

namespace Reg.D5.S3.Analytic.EllipticTailExponent.Bounds
open _root_.D5.S3.Analytic.EllipticTailExponent.Bounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def bActual : Realization signature := realize signature (fun _ k a => b k a) (fun e => nomatch e)
def uActual : Realization signature := realize signature (fun _ n a => U n a) (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem bDependence : ObservationalDependence signature bActual := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  norm_num [bActual, realize, b]

private theorem uDependence : ObservationalDependence signature uActual := by
  intro i
  by_contra! h
  have he : U 0 = fun _ => U 0 0 := by
    funext a
    exact (h 0 a 0)
  have hd := deriv_U_neg 0 (a := 1 / 2) (by norm_num) (by norm_num)
  rw [he, deriv_const] at hd
  exact lt_irrefl 0 hd


namespace CoefficientZero

def arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, R.readout () k 0 = 1 / ((k : ℝ) * (k + 1))

private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have hh := h 1
  norm_num [zeroReadout, realize] at hh

def family : Registration arena (type_of% @b_zero) where
  actual := bActual
  bridge := Iff.rfl
  variation := ⟨@b_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law bActual zeroReadout rejected_law
  dependence := bDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@b_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.CoefficientZero.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.CoefficientZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k a => b k a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Bounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientZero



namespace Positive

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) {a : ℝ}, 0 ≤ a → a ≤ 3 / 4 → 0 < R.readout () n a

private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  exact lt_irrefl 0 (@h 0 0 (by norm_num) (by norm_num))

def family : Registration arena (type_of% @U_pos) where
  actual := uActual
  bridge := Iff.rfl
  variation := ⟨@U_pos, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law uActual zeroReadout rejected_law
  dependence := uDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@U_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => U n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Bounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positive


def contRejected : Realization signature :=
  realize signature (fun _ _ a => (Real.log (2 * a))⁻¹) (fun e => nomatch e)

namespace Continuity

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ContinuousOn (fun a => R.readout () n a) (Icc 0 (3 / 4))

private theorem rejected_law : ¬ arena.Law contRejected := by
  intro h
  have hc : ContinuousAt (fun a : ℝ => (Real.log (2 * a))⁻¹) (1 / 2) :=
    (h 0 (1 / 2) ⟨by norm_num, by norm_num⟩).continuousAt
      (Icc_mem_nhds (by norm_num) (by norm_num))
  have he : ContinuousAt (fun x : ℝ => (Real.log x)⁻¹) 1 := by
    have ht : ContinuousAt (fun x : ℝ => (Real.log (2 * (x / 2)))⁻¹) 1 :=
      hc.comp (f := fun x : ℝ => x / 2) (x := (1 : ℝ)) (continuousAt_id.div_const (2 : ℝ))
    simpa only [show ∀ x : ℝ, 2 * (x / 2) = x by intro x; ring] using ht
  exact Real.not_continuousAt_inv_log_one he

def family : Registration arena (type_of% @continuousOn_U) where
  actual := uActual
  bridge := Iff.rfl
  variation := ⟨@continuousOn_U, contRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law uActual contRejected rejected_law
  dependence := uDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuousOn_U) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.Continuity.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => U n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Bounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuity

namespace TailZero

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () n 0 = 1 / ((n : ℝ) + 1)

private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have hh := h 0
  norm_num [zeroReadout, realize] at hh

def family : Registration arena (type_of% @U_zero) where
  actual := uActual
  bridge := Iff.rfl
  variation := ⟨@U_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law uActual zeroReadout rejected_law
  dependence := uDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@U_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.TailZero.unit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Bounds.TailZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => U n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Bounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailZero


end
end Reg.D5.S3.Analytic.EllipticTailExponent.Bounds
