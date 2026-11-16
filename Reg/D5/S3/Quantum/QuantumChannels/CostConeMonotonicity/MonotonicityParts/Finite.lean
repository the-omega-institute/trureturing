import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity
universe u v

namespace Conic
abbrev signature : Signature where
  Params := Type u
  State := fun X => X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ X => X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro he
  have h : (ULift.up true : ULift.{u} Bool) = ULift.up false :=
    Eq.mp (congrFun he (ULift.up false)) rfl
  cases h

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} {α : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace α]
    (μ : Measure α) {f : α → E} (hfm : StronglyMeasurable f) (hfi : Integrable f μ)
    {s : Set α} (hs : ∀ᵐ a ∂μ, a ∈ s),
    ∃ (k : ℕ) (w : Fin k → ℝ) (a : Fin k → α),
      (∀ i, 0 ≤ w i) ∧ (∀ i, a i ∈ s) ∧ R.readout () E (∑ i, w i • f (a i)) (∫ a, f a ∂μ)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨k, w, a, hw, ha, he⟩ := @h PUnit.{u+1} PUnit.{v+1}
    inferInstance inferInstance inferInstance inferInstance 0 (fun _ => 0)
    stronglyMeasurable_const (by simp) Set.univ (by simp)
  exact he

def source_registration : Registration arena.{u,v} (type_of% @finite_conic_moments.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_conic_moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@finite_conic_moments.{u,v}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.finite_conic_moments.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite.Conic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Conic

namespace Distance
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), 1, ?_⟩
  intro he
  have h : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} {α : Type v} [Fintype I]
    [MeasurableSpace α] (μ : Measure α) (p q : ℝ) (hq : 0 < q)
    (lam : I → ℝ) (z : α → I → ℝ) (r : α → ℝ) (hr : ∀ᵐ a ∂μ, 0 ≤ r a)
    (hfm : StronglyMeasurable (fun a => r a • distanceVector q (z a)))
    (hfi : Integrable (fun a => r a • distanceVector q (z a)) μ)
    (hmoment : (∫ a, r a • distanceVector q (z a) ∂μ) = distanceVector p lam),
    ∃ (k : ℕ) (w : Fin k → I → ℝ),
      ∀ i j, R.readout () () (|lam i - lam j| ^ p) (∑ l, |w l i - w l j| ^ q)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨k, w, he⟩ := @h PUnit.{u+1} PUnit.{v+1}
    inferInstance inferInstance 0 1 1 (by norm_num) (fun _ => 0) (fun _ _ => 0)
    (fun _ => 0) (by simp)
    (by simpa using (stronglyMeasurable_const : StronglyMeasurable (fun _ : PUnit.{v+1} => (0 : PUnit.{u+1} × PUnit.{u+1} → ℝ))))
    (by simp) (by ext ij; simp [distanceVector])
  exact he PUnit.unit PUnit.unit

def source_registration : Registration arena.{u,v} (type_of% @finite_distance_decomposition_of_integral.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_distance_decomposition_of_integral, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@finite_distance_decomposition_of_integral.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.finite_distance_decomposition_of_integral.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite.Distance.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Distance

namespace Exact
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), 1, ?_⟩
  intro he
  have h : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (lam : I → ℝ), ∃ (k : ℕ) (w : Fin k → I → ℝ),
      ∀ i j, R.readout () () (|lam i - lam j| ^ p) (∑ l, |w l i - w l j| ^ q)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨k, w, he⟩ := @h PUnit.{u+1} inferInstance 1 2 (by norm_num) (by norm_num) (fun _ => 0)
  exact he PUnit.unit PUnit.unit

def source_registration : Registration arena.{u} (type_of% @finite_distance_decomposition.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_distance_decomposition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@finite_distance_decomposition.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.finite_distance_decomposition.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite.Exact.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Exact
end Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite
