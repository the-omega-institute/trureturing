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

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal44
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => Bool → ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ a A => canonicalAffineLo A a) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (A : Bool → ℝ) (a : ℝ) (ha : -1 < a) (ha1 : a < 1),
    let lo := r.readout () a A
    let hi := canonicalAffineHi A a
    lo ≤ hi ∧
    (A false ≠ A true → lo < hi) ∧
    (hi-lo = (max (A false) (A true)-min (A false) (A true)) /
      (if 0 < a then 1-a else 1+a)) ∧
    (if 0 < a then
      lo = min (A false) (A true)+a*lo ∧ hi = max (A false) (A true)+a*hi
     else
      lo = min (A false) (A true)+a*hi ∧ hi = max (A false) (A true)+a*lo) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ A i+a*z ∧ A i+a*z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ A i+a*z ∧ A i+a*z ≤ u) →
      l ≤ lo ∧ hi ≤ u)

theorem source_bridge : (type_of% @canonical_affine_hull) ↔ sourceArena.Law actual :=
  Iff.rfl

theorem positive_law : sourceArena.Law actual := @canonical_affine_hull

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h (fun _ => 0) 0 (by norm_num) (by norm_num)).1
  norm_num [rejected, realize, canonicalAffineHi] at impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, canonicalAffineLo]

def evidence : Registration sourceArena (type_of% @canonical_affine_hull) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

def canonical_affine_hull_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@canonical_affine_hull)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ a A => canonicalAffineLo A a) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal44.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal44.evidence
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
    (fun _ a A => canonicalAffineLo A a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms canonical_affine_hull_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal44

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Bool → List Label) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ L U => canonicalReturnLo U L) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (U : Bool → List Label) (L : ℕ) (hL : 0 < L)
      (hlen : ∀ i, (U i).length=L) (hlegal : ∀ i, LegalWord s s (U i)),
    let lo := r.readout () L U
    let hi := canonicalReturnHi U L
    lo ≤ hi ∧
    (U false ≠ U true → lo < hi) ∧
    (∀ z ∈ Set.Icc lo hi, InSupport s z) ∧
    (∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi) ∧
    (∀ l u : ℝ, l ≤ u →
      (∀ i z, l ≤ z → z ≤ u → l ≤ compose (U i) z ∧ compose (U i) z ≤ u) →
      l ≤ lo ∧ hi ≤ u) ∧
    (lo = hi ↔ U false = U true) ∧
    (lo ∈ coefficientField ∧ hi ∈ coefficientField)

theorem source_bridge : (type_of% @canonical_legal_return_hull) ↔ sourceArena.Law actual :=
  Iff.rfl

theorem positive_law : sourceArena.Law actual := @canonical_legal_return_hull

/-- Both dependence states are genuine positive-length returns at the same guard. -/
theorem witness_returns_legal :
    LegalWord .G0 .G0 [Label.L0] ∧ LegalWord .G0 .G0 [Label.L2] := ⟨rfl, rfl⟩

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .G0 (fun _ => [Label.L0]) 1 (by decide)
    (by intro i; rfl) (fun _ => witness_returns_legal.1)).1
  norm_num [rejected, realize, canonicalReturnHi, canonicalAffineHi, compose, branch, shift]
    at impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

theorem actual_dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨1, (fun _ => [Label.L0]), (fun _ => [Label.L2]), ?_⟩
  change canonicalReturnLo (fun _ => [Label.L0]) 1 ≠
    canonicalReturnLo (fun _ => [Label.L2]) 1
  have hgp : 0 < g := tail_arithmetic.2.2.2.1
  have hg1 : g < 1 := tail_arithmetic.2.2.2.2.1
  have hneg : ¬ (0 : ℝ) < -g := by linarith
  have numerator : 0 < 1 - g := by linarith
  have denominator : 0 < 1 - g ^ 2 := by nlinarith
  have atZero : canonicalReturnLo (fun _ => [Label.L0]) 1 = 0 := by
    norm_num [canonicalReturnLo, canonicalAffineLo, compose, branch, shift]
  have atTwo : 0 < canonicalReturnLo (fun _ => [Label.L2]) 1 := by
    simpa [canonicalReturnLo, canonicalAffineLo, compose, branch, shift, hneg,
      sub_eq_add_neg] using div_pos numerator denominator
  rw [atZero]
  exact ne_of_lt atTwo

def evidence : Registration sourceArena (type_of% @canonical_legal_return_hull) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

def canonical_legal_return_hull_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@canonical_legal_return_hull)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ L U => canonicalReturnLo U L) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.evidence
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
    (fun _ L U => canonicalReturnLo U L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms canonical_legal_return_hull_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal48
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (a b lo hi : ℝ) (w : List Label) (cs : List Color)
    (hab : a ≤ b) (cert : EndpointCertificate a lo hi w cs),
    EndpointCertificate (r.readout () () b) lo hi w cs

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bounds := cut_bounds (0 : Color)
  norm_num only [Fin.val_zero, zero_add] at bounds
  have supported : InSupport .G0 (cut 0) :=
    ⟨bounds.1, bounds.2.1.le.trans bounds.2.2⟩
  have cost : max (cut 0 - cut 0) (max 0 (cut 0 - cut 1)) ≤ (0 : ℝ) := by
    rw [sub_self, max_eq_left (sub_nonpos.mpr bounds.2.1.le)]
    norm_num
  have cert : EndpointCertificate 0 (cut 0) (cut 0) [] [(0 : Color)] := by
    intro p hp
    have hp0 : p = 0 := by simpa only [List.length_singleton, Nat.lt_one_iff] using hp
    subst p
    simpa [compose] using And.intro (And.intro supported cost) (And.intro supported cost)
  have bad := h 0 0 (cut 0) (cut 0) [] [(0 : Color)] le_rfl cert
  have impossible := (bad 0 (by simp)).1.2
  change max (cut 0 - cut 0) (max 0 (cut 0 - cut 1)) ≤ (-1 : ℝ) at impossible
  have nonnegative : 0 ≤ max (cut 0 - cut 0) (max 0 (cut 0 - cut 1)) := by
    rw [sub_self]
    exact le_max_left _ _
  linarith

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.endpoint_certificate_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.endpoint_certificate_mono, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def endpoint_certificate_mono_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.endpoint_certificate_mono)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal48.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal48.evidence
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
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms endpoint_certificate_mono_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal48

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal49
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.observationSignature

abbrev actual : Realization observationSignature :=
  Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.actual

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

/-- Only the low endpoint in the high stem certificate is intervened on.
The original budget and every other endpoint occurrence remain fixed. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hcolors : ∀ i, (U i).length = (W i).length),
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (r.readout () L U) (canonicalReturnHi U L) P h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo U L) (canonicalReturnHi U L) (U i) (W i)) ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i))

theorem source_bridge : (type_of% @family_endpoint_certificates) ↔ sourceArena.Law actual :=
  Iff.rfl

theorem positive_law : sourceArena.Law actual := @family_endpoint_certificates

/-- The original telescope permits an empty legal stem and a nonempty color list.
The return words still have positive length and satisfy every original guard. -/
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have cert := (h .G0 .G0 [] [] [(0 : Color)] rfl rfl
    (fun _ => [Label.L0]) (fun _ => [Label.L0]) (fun _ => [(0 : Color)])
    1 (by decide) (by intro i; rfl) (by intro i; rfl)
    (fun _ => Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.witness_returns_legal.1)
    (fun _ => Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.witness_returns_legal.1)
    (by intro i; rfl)).2.2.1
  have impossible := (cert 0 (by simp)).1.1.1
  norm_num [rejected, realize, compose] at impossible

theorem sensitivity : Sensitivity sourceArena actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law

def evidence : Registration sourceArena (type_of% @family_endpoint_certificates) where
  actual := actual
  bridge := source_bridge
  variation := ⟨positive_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal47.actual_dependence

def family_endpoint_certificates_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@family_endpoint_certificates)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ L U => canonicalReturnLo U L) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal49.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal49.evidence
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
    (fun _ L U => canonicalReturnLo U L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
    definition := none
    coordinates := #[10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms family_endpoint_certificates_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal49
