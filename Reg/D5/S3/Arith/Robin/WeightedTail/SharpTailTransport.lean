import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.WeightedTail.SharpTailTransport
import Reg.Support.SingleDependentReadout

/-! Source-bound observations for normalized tail transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Real Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.WeightedTail.SharpTailTransport
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport

namespace Reg.D5.S3.Arith.Robin.WeightedTail.SharpTailTransport

abbrev transportSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def transportActual : Realization transportSignature :=
  realize transportSignature (fun _ _ k => tail k) (fun e => nomatch e)

def transportRejected : Realization transportSignature :=
  realize transportSignature (fun _ _ _ _ => 1) (fun e => nomatch e)

def transportArena : Arena where
  signature := transportSignature
  Law V := ∀ {k : ℝ → ℝ} {x C : ℝ} (_ : 2 ≤ x)
    (_ : IntegrableOn k (Ioi x)) (_ : ∀ t ≥ x, |tail k t| ≤ C / sqrt t),
    |sqrt x * log x * weightedTail k x - sqrt x * V.readout () () k x| ≤
      3 * C / log x

private theorem transport_rejected : ¬ transportArena.Law transportRejected := by
  intro h
  have hh := h (k := fun _ => 0) (x := 2) (C := 0) le_rfl
    (by simp) (by intro t ht; simp [tail])
  change |sqrt 2 * log 2 * weightedTail (fun _ => 0) 2 -
    sqrt 2 * 1| ≤ 3 * 0 / log 2 at hh
  simp only [weightedTail, zero_mul, integral_zero, mul_zero, zero_sub, mul_one,
    abs_neg, zero_div, abs_of_nonneg (sqrt_nonneg _)] at hh
  exact (not_le_of_gt (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) hh

private theorem transport_dependence : ObservationalDependence transportSignature transportActual := by
  intro _
  refine ⟨(), (fun _ => 0), (fun t => exp (-t)), ?_⟩
  intro he
  have hx := congrFun he (2 : ℝ)
  change tail (fun _ => 0) 2 = tail (fun t => exp (-t)) 2 at hx
  have hi := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (2 : ℝ)
  have htail : tail (fun t => exp (-t)) 2 = exp (-2) := by
    simpa only [tail, neg_one_mul, neg_div_neg_eq, div_one, one_mul] using hi
  rw [htail] at hx
  simp only [tail, integral_zero] at hx
  exact (exp_pos (-2)).ne hx

def transportEvidence : Registration transportArena (type_of% @normalized_tail_transport) where
  actual := transportActual
  bridge := Iff.rfl
  variation := ⟨@normalized_tail_transport, transportRejected, transport_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    transportArena.Law transportActual transportRejected transport_rejected
  dependence := transport_dependence

def transportRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalized_tail_transport) (Realization transportSignature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.WeightedTail.SharpTailTransport.normalized_tail_transport.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.WeightedTail.SharpTailTransport.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some transportActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.WeightedTail.SharpTailTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms transportRegistration

end Reg.D5.S3.Arith.Robin.WeightedTail.SharpTailTransport
end
