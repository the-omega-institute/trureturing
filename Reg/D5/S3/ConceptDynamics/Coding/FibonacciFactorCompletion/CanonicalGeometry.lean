import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
import Reg.Support.SingleDependentReadout
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Analysis.Real.Cardinality

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
noncomputable section

private theorem coefficient_field_nonmember : ∃ c : ℝ, c ∉ coefficientField := by
  classical
  let C := Subfield.closure ({t} : Set ℝ)
  have hC : (C : Set ℝ).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    exact (Subfield.cardinalMk_closure_le_max ({t} : Set ℝ)).trans
      (max_le (Set.countable_singleton t).le_aleph0 le_rfl)
  have hF : (coefficientField : Set ℝ).Countable := hC.mono (by
    intro x hx
    change ∀ F : Subfield ℝ, t ∈ F → x ∈ F at hx
    exact hx C (Subfield.subset_closure (by simp)))
  by_contra h
  have allmem (x : ℝ) : x ∈ coefficientField := by
    by_contra hx
    exact h ⟨x, hx⟩
  exact Cardinal.not_countable_real (hF.mono (by
    intro x _
    exact allmem x))

namespace ExactOriginal45

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (List Label) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ w x => compose w x) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature
    (fun _ _ _ => Classical.choose coefficient_field_nonmember) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ w : List Label, r.readout () w (0 : ℝ) ∈ coefficientField

private theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (Classical.choose_spec coefficient_field_nonmember) (h [])

def evidence : Registration sourceArena (type_of% @literal_coefficient_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_coefficient_mem, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨[], 0, 1, ?_⟩
    norm_num [actual, realize, compose]

def literal_coefficient_mem_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@literal_coefficient_mem)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ w x => compose w x) (fun e => nomatch e))) Unit Unit where
  unitName := .str (.str
    `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    "ExactOriginal45") "unit"
  realizationName := .str (.str
    `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    "ExactOriginal45") "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ w x => compose w x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms literal_coefficient_mem_registration
end ExactOriginal45

namespace ExactOriginal46

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Bool → List Label)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature
    (fun _ _ _ => Classical.choose coefficient_field_nonmember) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (U : Bool → List Label) (L : ℕ),
    r.readout () U L ∈ coefficientField ∧ canonicalReturnHi U L ∈ coefficientField

private theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (Classical.choose_spec coefficient_field_nonmember) ((h (fun _ => []) 0).1)

def evidence : Registration sourceArena (type_of% @canonical_return_coefficient_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_return_coefficient_mem, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => [Label.L2]), 0, 1, ?_⟩
    change canonicalReturnLo (fun _ => [Label.L2]) 0 ≠
      canonicalReturnLo (fun _ => [Label.L2]) 1
    have hgp : 0 < g := tail_arithmetic.2.2.2.1
    have hg1 : g < 1 := tail_arithmetic.2.2.2.2.1
    have hneg : ¬ (0 : ℝ) < -g := by linarith
    have numerator : 0 < 1 - g := by linarith
    have denominator : 0 < 1 - g ^ 2 := by nlinarith
    have atZero : canonicalReturnLo (fun _ => [Label.L2]) 0 = 0 := by
      norm_num [canonicalReturnLo, canonicalAffineLo, compose, branch, shift]
    have atOne : 0 < canonicalReturnLo (fun _ => [Label.L2]) 1 := by
      simpa [canonicalReturnLo, canonicalAffineLo, compose, branch, shift, hneg,
        sub_eq_add_neg]
        using div_pos numerator denominator
    rw [atZero]
    exact ne_of_lt atOne

def canonical_return_coefficient_mem_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@canonical_return_coefficient_mem)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e))) Unit Unit where
  unitName := .str (.str
    `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    "ExactOriginal46") "unit"
  realizationName := .str (.str
    `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    "ExactOriginal46") "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms canonical_return_coefficient_mem_registration
end ExactOriginal46

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal43
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ L => (-g)^L) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (L : ℕ) (hL : 0 < L),
    -1 < (-g)^L ∧ (-g)^L < 1 ∧ r.readout () () L ≠ 0

theorem source_bridge : (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.return_slope_control) ↔
    sourceArena.Law actual := Iff.rfl

theorem positive_law : sourceArena.Law actual := @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.return_slope_control

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h 1 (by decide)).2.2
  exact impossible rfl

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change (-g)^(1 : ℕ) ≠ (-g)^(2 : ℕ)
  have hgp : 0 < g := tail_arithmetic.2.2.2.1
  have hsq : 0 < (-g)^2 := sq_pos_of_ne_zero (neg_ne_zero.mpr (ne_of_gt hgp))
  rw [pow_one]
  exact ne_of_lt (lt_trans (neg_neg_of_pos hgp) hsq)

def evidence : Registration sourceArena (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.return_slope_control) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

def return_slope_control_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.return_slope_control)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ L => (-g)^L) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal43.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal43.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ L => (-g)^L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms return_slope_control_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal43
