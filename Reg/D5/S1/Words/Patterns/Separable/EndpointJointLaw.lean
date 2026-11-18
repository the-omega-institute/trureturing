import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointJointLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointJointLaw

open _root_.D5.S1.Words.Patterns.Separable.EndpointJointLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => endpointPMF (r, true)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ,
    let t : ℝ := Real.sqrt 2 - 1
    let a : ℝ := 1 - 1 / Real.sqrt 2
    endpointPMF (0, true) = ENNReal.ofReal a ∧
    endpointPMF (0, false) = ENNReal.ofReal (a * (1+t)) ∧
    (1 ≤ r →
      R.readout () () r = ENNReal.ofReal (a*t*(1+t)*t^(2*r-2)) ∧
      endpointPMF (r, false) = ENNReal.ofReal (t*(a*t*(1+t)*t^(2*r-2))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := ((h 1).2.2 (by decide)).1
  exact ENNReal.ofReal_ne_top bad.symm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change endpointPMF (0, true) ≠ endpointPMF (1, true)
  have h0 := (whole_endpoint_joint_law 0).1
  have h1 := ((whole_endpoint_joint_law 1).2.2 (by decide)).1
  norm_num only at h1
  intro same
  rw [h0, h1] at same
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hsupper : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have haeq : (1 : ℝ) - 1 / Real.sqrt 2 = (2 - Real.sqrt 2) / 2 := by
    field_simp
    nlinarith
  have ha : 0 < (1 : ℝ) - 1 / Real.sqrt 2 := by rw [haeq]; linarith
  have ht : 0 < Real.sqrt (2 : ℝ) - 1 := by linarith
  have hp : 0 < ((1 : ℝ) - 1 / Real.sqrt 2) * (Real.sqrt 2 - 1) *
      (1 + (Real.sqrt 2 - 1)) := by positivity
  have eqreal := (ENNReal.ofReal_eq_ofReal_iff ha.le hp.le).mp same
  have factor : (Real.sqrt (2 : ℝ) - 1) * (1 + (Real.sqrt 2 - 1)) =
      2 - Real.sqrt 2 := by nlinarith
  have eqreal' : ((1 : ℝ) - 1 / Real.sqrt 2) =
      ((1 : ℝ) - 1 / Real.sqrt 2) * (2 - Real.sqrt 2) := by
    calc
      _ = ((1 : ℝ) - 1 / Real.sqrt 2) * (Real.sqrt 2 - 1) *
          (1 + (Real.sqrt 2 - 1)) := eqreal
      _ = _ := by rw [mul_assoc, factor]
  nlinarith

def family : Registration arena (type_of% @whole_endpoint_joint_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_endpoint_joint_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_endpoint_joint_law) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointJointLaw.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointJointLaw.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => endpointPMF (r, true))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointJointLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.EndpointJointLaw
