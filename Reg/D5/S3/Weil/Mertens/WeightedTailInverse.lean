import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedTailInverse
import Reg.Support.SingleDependentReadout

/-! Typed whole-tail observations for positive L1 inversion and its lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.WeightedTailInverse

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => tail k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

def inverseArena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ → ℝ} {x : ℝ} (_ : 2 ≤ x) (_ : IntegrableOn k (Ioi x)),
    IntegrableOn (fun t => v t * weightedTail k t) (Ioi x) ∧
      R.readout () () k x = a x * weightedTail k x +
        ∫ t in Ioi x, v t * weightedTail k t

def lowerArena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ → ℝ} {x A : ℝ} (_ : Real.exp 1 ≤ x) (_ : 0 ≤ A)
      (_ : IntegrableOn k (Ioi x))
      (_ : ∀ t ≥ x, weightedTail k t ≥ -A / (Real.sqrt t * Real.log t)),
    R.readout () () k x ≥ -3 * A / Real.sqrt x

private theorem inverse_rejected : ¬ inverseArena.Law rejected := by
  intro h
  have hh := (h (k := fun _ => 0) (x := 2) (by norm_num) (by simp)).2
  norm_num [rejected, realize, weightedTail] at hh

private theorem lower_rejected : ¬ lowerArena.Law rejected := by
  intro h
  have hh := h (k := fun _ => 0) (x := Real.exp 1) (A := 0) le_rfl le_rfl
    (by simp) (by intro t ht; simp [weightedTail])
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (fun _ => 0), (fun t => Real.exp (-t)), ?_⟩
  intro he
  have hx := congrFun he (2 : ℝ)
  change tail (fun _ => 0) 2 = tail (fun t => Real.exp (-t)) 2 at hx
  have hi := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (2 : ℝ)
  have htail : tail (fun t => Real.exp (-t)) 2 = Real.exp (-2) := by
    simpa only [tail, neg_one_mul, neg_div_neg_eq, div_one, one_mul] using hi
  simp only [tail, integral_zero] at hx
  rw [show (∫ t in Ioi (2 : ℝ), Real.exp (-t)) = Real.exp (-2) from htail] at hx
  exact (Real.exp_pos (-2)).ne hx

def inverseEvidence : Registration inverseArena (type_of% @inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse, rejected, inverse_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    inverseArena.Law actual rejected inverse_rejected
  dependence := actual_dependence

def lowerEvidence : Registration lowerArena (type_of% @tail_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tail_lower_bound, rejected, lower_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    lowerArena.Law actual rejected lower_rejected
  dependence := actual_dependence

def inverseRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@inverse) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedTailInverse.inverse.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailInverse.inverseEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena⟩
  objectArena := .source ⟨inverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverseEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailInverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms inverseRegistration

def lowerRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tail_lower_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedTailInverse.tail_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailInverse.lowerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailInverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lowerRegistration

end Reg.D5.S3.Weil.Mertens.WeightedTailInverse
end
