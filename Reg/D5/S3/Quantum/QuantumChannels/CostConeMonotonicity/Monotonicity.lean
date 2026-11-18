import Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Analytic
import Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.MonotonicityParts.Finite
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
import Reg.Support.DependentFamily
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators TensorProduct

namespace Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity

universe u

abbrev Params := Σ H : Type u, Σ G : NormedAddCommGroup H,
  @InnerProductSpace ℂ H inferInstance G.toSeminormedAddCommGroup

abbrev Operator (p : Params.{u}) : Type u := by
  letI := p.2.1
  letI := p.2.2
  exact p.1 →L[ℂ] p.1

abbrev Tensor (p : Params.{u}) : Type u := by
  letI := p.2.1
  letI := p.2.2
  exact Operator p ⊗[ℂ] Operator p

abbrev operatorSignature : Signature where
  Params := Params.{u}
  State := Operator
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Operator p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev tensorSignature : Signature where
  Params := Params.{u}
  State := Tensor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Tensor p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem empty_finiteObservable :
    IsFiniteObservable (0 : PUnit.{u+1} →L[ℂ] PUnit.{u+1}) := by
  refine ⟨by simp, ?_⟩
  rw [spectrum.of_subsingleton]
  exact Set.finite_empty

namespace Projection
abbrev signature := operatorSignature.{u}
def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let H := EuclideanSpace ℂ PUnit.{u+1}
  let p : Params.{u} := ⟨H, inferInstance, inferInstance⟩
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have h : (1 : Operator p) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h



abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : IsFiniteObservable A) (f : ℝ → ℝ) (v : ℝ),
    R.readout () ⟨H, inferInstance, inferInstance⟩ (specProj (cfc f A) v)
      (∑ x ∈ hA.2.toFinset.filter (fun x => f x = v), specProj A x)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance inferInstance 0
    empty_finiteObservable (fun x => x) 0

def source_registration : Registration arena.{u} (type_of% @specProj_cfc.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@specProj_cfc, rejected, rejected_law⟩
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
      (@specProj_cfc.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.specProj_cfc.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.Projection.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Projection

namespace Cost
abbrev signature := tensorSignature.{u}
def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let H := EuclideanSpace ℂ PUnit.{u+1}
  let p : Params.{u} := ⟨H, inferInstance, inferInstance⟩
  let one : Operator p := 1
  refine ⟨p, 0, one ⊗ₜ[ℂ] one, ?_⟩
  intro he
  have h : one ⊗ₜ[ℂ] one = (0 : Tensor p) := Eq.mp (congrFun he 0) rfl
  have hm := congrArg (LinearMap.mul' ℂ (Operator p)) h
  have ho : (1 : Operator p) = 0 := by simpa [one] using hm
  exact one_ne_zero ho



abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : IsFiniteObservable A) (q : ℝ) (f : ℝ → ℝ),
    R.readout () ⟨H, inferInstance, inferInstance⟩ (costElem q (cfc f A))
      (∑ x ∈ hA.2.toFinset, ∑ y ∈ hA.2.toFinset,
        |f x - f y| ^ q • (specProj A x ⊗ₜ[ℂ] specProj A y))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance inferInstance 0
    empty_finiteObservable 1 (fun x => x)

def source_registration : Registration arena.{u} (type_of% @costElem_cfc.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@costElem_cfc, rejected, rejected_law⟩
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
      (@costElem_cfc.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.costElem_cfc.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.Cost.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Cost

namespace Decomposition
abbrev signature := tensorSignature.{u}
def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let H := EuclideanSpace ℂ PUnit.{u+1}
  let p : Params.{u} := ⟨H, inferInstance, inferInstance⟩
  let one : Operator p := 1
  refine ⟨p, 0, one ⊗ₜ[ℂ] one, ?_⟩
  intro he
  have h : one ⊗ₜ[ℂ] one = (0 : Tensor p) := Eq.mp (congrFun he 0) rfl
  have hm := congrArg (LinearMap.mul' ℂ (Operator p)) h
  have ho : (1 : Operator p) = 0 := by simpa [one] using hm
  exact one_ne_zero ho



abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : IsFiniteObservable A) (p q : ℝ) {k : ℕ}
    (f : Fin k → ℝ → ℝ)
    (h : ∀ x ∈ hA.2.toFinset, ∀ y ∈ hA.2.toFinset,
      |x - y| ^ p = ∑ l, |f l x - f l y| ^ q),
    R.readout () ⟨H, inferInstance, inferInstance⟩ (costElem p A)
      (∑ l, costElem q (cfc (f l) A))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  apply @h PUnit.{u+1} inferInstance inferInstance inferInstance 0
    empty_finiteObservable 1 1 0 (fun i => Fin.elim0 i)
  intro x hx
  simpa [empty_finiteObservable, spectrum.of_subsingleton] using hx

def source_registration : Registration arena.{u} (type_of% @costElem_of_decomposition.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@costElem_of_decomposition, rejected, rejected_law⟩
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
      (@costElem_of_decomposition.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.costElem_of_decomposition.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.Decomposition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Decomposition

namespace FiniteObservable

abbrev ObservableParams := {p : Params.{u} // @CompleteSpace p.1 p.2.1.toUniformSpace}

abbrev Operator (p : ObservableParams.{u}) : Type u := by
  letI := p.1.2.1
  letI := p.1.2.2
  exact p.1.1 →L[ℂ] p.1.1

abbrev signature : Signature where
  Params := ObservableParams.{u}
  State := Operator
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.1.2.1
    letI := p.1.2.2
    letI := p.2
    exact IsFiniteObservable X) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : IsFiniteObservable A) (f : ℝ → ℝ),
    R.readout () ⟨⟨H, inferInstance, inferInstance⟩, inferInstance⟩ (cfc f A)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance inferInstance 0
    empty_finiteObservable (fun x => x)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let H := EuclideanSpace ℂ PUnit.{u+1}
  let p : ObservableParams.{u} := ⟨⟨H, inferInstance, inferInstance⟩, inferInstance⟩
  let B : Operator p := algebraMap ℂ (Operator p) Complex.I
  refine ⟨p, 0, B, ?_⟩
  intro he
  have hz : IsFiniteObservable (0 : Operator p) := by
    refine ⟨by simp, ?_⟩
    rw [spectrum.zero_eq]
    exact Set.finite_singleton 0
  have hB : IsFiniteObservable B := Eq.mp he hz
  have hi : IsSelfAdjoint Complex.I :=
    (isSelfAdjoint_algebraMap_iff (FaithfulSMul.algebraMap_injective ℂ (Operator p))).mp hB.1
  have hb := (Complex.im_eq_zero_iff_isSelfAdjoint Complex.I).mpr hi
  norm_num at hb

def source_registration : Registration arena.{u} (type_of% @finiteObservable_cfc.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteObservable_cfc, rejected, rejected_law⟩
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
      (@finiteObservable_cfc.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.finiteObservable_cfc.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.FiniteObservable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p X => by
    letI := p.1.2.1
    letI := p.1.2.2
    letI := p.2
    exact IsFiniteObservable X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end FiniteObservable

namespace Inclusion
abbrev signature : Signature where
  Params := Params.{u}
  State p := Set (Tensor p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (Tensor p) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X Y => X ⊆ Y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q),
    R.readout () ⟨H, inferInstance, inferInstance⟩ (costCone (H := H) p) (costCone q)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance inferInstance 1 1 (by norm_num) le_rfl

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : Params.{u} := ⟨PUnit.{u+1}, inferInstance, inferInstance⟩
  refine ⟨p, ∅, Set.univ, ?_⟩
  intro he
  have hu : (Set.univ : Set (Tensor p)) ⊆ ∅ := Eq.mp (congrFun he ∅) (Set.empty_subset _)
  exact hu (Set.mem_univ (0 : Tensor p))

def source_registration : Registration arena.{u} (type_of% @result.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
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
      (@result.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity.Inclusion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X ⊆ Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Inclusion

end Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity
