import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.EllipticTailExponent.Result
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.EllipticTailExponent.Tail
open _root_.D5.S3.Analytic.EllipticTailExponent.Defs
open _root_.D5.S3.Analytic.EllipticTailExponent.Tail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
open scoped BigOperators
noncomputable section

abbrev productSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def productActual : Realization productSignature :=
  realize productSignature (fun _ N a => (N + 1 : ℝ) * d (N + 1) a) (fun e => nomatch e)

def productRejected : Realization productSignature :=
  realize productSignature (fun _ _ _ => 0) (fun e => nomatch e)

def productArena : Arena where
  signature := productSignature
  Law R := ∀ (N : ℕ) (a : ℝ), R.readout () N a =
    a * (1 - a / (N + 1)) * ∏ j ∈ range N, (1 - a ^ 2 / ((j : ℝ) + 1) ^ 2)

private theorem productRejected_law : ¬ productArena.Law productRejected := by
  intro h
  have he := h 0 (1 / 2)
  norm_num [productRejected, realize] at he

private theorem productDependence : ObservationalDependence productSignature productActual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  norm_num [productActual, realize, d, prod_range_succ]

def productEvidence : Registration productArena (type_of% @d_product) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨d_product, productRejected, productRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    productArena.Law productActual productRejected productRejected_law
  dependence := productDependence

def productAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@d_product) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Tail.productUnit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Tail.productEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨productArena⟩
  objectArena := .source ⟨productArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena ⟨productEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize productSignature
    (fun _ N a => (N + 1 : ℝ) * d (N + 1) a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Tail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev tailSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ n a => ∑' k, t (k + n + 1) a) (fun e => nomatch e)

def tailRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => 0) (fun e => nomatch e)

def tailArena : Arena where
  signature := tailSignature
  Law R := ∀ (n : ℕ) {a : ℝ}, 0 < a → a ≤ 1 / 2 →
    Real.sin (Real.pi * a) / (Real.pi * (1 - a)) - S n a = R.readout () n a

private theorem tailHalf_ne_zero :
    Real.sin (Real.pi * (1 / 2)) / (Real.pi * (1 - 1 / 2)) - S 0 (1 / 2) ≠ 0 := by
  have hd := _root_.D5.S3.Analytic.EllipticTailExponent.Result.denominator_pos
    0 (a := 1 / 2) (by norm_num) (by norm_num)
  have hp : 0 < Real.pi * (1 - (1 / 2 : ℝ)) := by positivity
  have h := div_pos hd hp
  rw [sub_div, mul_div_cancel_left₀ _ hp.ne'] at h
  exact h.ne'

private theorem tailRejected_law : ¬ tailArena.Law tailRejected := by
  intro h
  exact tailHalf_ne_zero (@h 0 (1 / 2) (by norm_num) (by norm_num))

private theorem tailDependence : ObservationalDependence tailSignature tailActual := by
  intro i
  refine ⟨0, 0, 1 / 2, ?_⟩
  change (∑' k, t (k + 0 + 1) 0) ≠ ∑' k, t (k + 0 + 1) (1 / 2)
  have hz : (∑' k, t (k + 0 + 1) 0) = 0 := by simp [t]
  rw [hz, ← tail_eq_tsum 0 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)]
  exact Ne.symm tailHalf_ne_zero

def tailEvidence : Registration tailArena (type_of% @tail_eq_tsum) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨tail_eq_tsum, tailRejected, tailRejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law tailActual tailRejected tailRejected_law
  dependence := tailDependence

def tailAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tail_eq_tsum) (Realization tailSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.EllipticTailExponent.Tail.tailUnit
  realizationName := `Reg.D5.S3.Analytic.EllipticTailExponent.Tail.tailEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tailSignature
    (fun _ n a => ∑' k, t (k + n + 1) a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.EllipticTailExponent.Tail
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

end
end Reg.D5.S3.Analytic.EllipticTailExponent.Tail
