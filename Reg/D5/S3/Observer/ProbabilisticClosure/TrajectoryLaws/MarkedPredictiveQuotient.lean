import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix Classical
open LeanInformationAudit MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

local notation "originalCylinder" => _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.cylinder

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
universe u

abbrev Parameters := Σ T : Producer.{u}, Σ _t : ℤ, Σ _n : ℕ,
  @FutureClass T.hidden T.finite (@Presentation.matrix T.hidden T.finite T.parameter)

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State t := Fin t.2.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ t := Set (PathSpace t.1.hidden)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ t w => @endpointEvent t.1.hidden t.1.finite (@Presentation.matrix t.1.hidden t.1.finite t.1.parameter)
    t.2.1 t.2.2.1 w t.2.2.2) Empty.elim

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) Empty.elim

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (T : Producer.{u}) [MeasurableSpace T.hidden] [MeasurableSingletonClass T.hidden],
    letI : Fintype T.hidden := T.finite
    ∀ (_hu : RowUnifilar T.parameter.matrix)
      (J : Measure (PathSpace T.hidden)) [IsProbabilityMeasure J]
      (_hcyl : HasOriginalCylinders J T.parameter) (t : ℤ) (n : ℕ)
      (w : Fin n → Bool) (a : FutureClass T.parameter.matrix),
      J.real (R.readout () ⟨T, t, n, a⟩ w) =
        ∑ i, T.parameter.initial i *
          if endpoint (quotientSuccessor T.parameter.matrix) n (classOf T.parameter.matrix i) w = a
          then wordMass (quotientMass T.parameter.matrix) (quotientSuccessor T.parameter.matrix)
            n (classOf T.parameter.matrix i) w else 0

abbrev Toy := ULift.{u} Unit

def toy : Presentation Toy where
  initial _ := 1
  matrix x _ _ := if x = false then 1 else 0
  initial_nonneg _ := by norm_num
  initial_sum := by simp
  matrix_nonneg x _ _ := by split_ifs <;> norm_num
  stochastic _ := by simp
  stationary _ := by simp
  no11 := by simp [Matrix.mul_apply]

abbrev toyProducer : Producer.{u} := ⟨Toy, inferInstance, toy⟩

def toyPath : PathSpace Toy := (fun _ => ⟨()⟩, fun _ => false)

private theorem toy_cylinders : HasOriginalCylinders (Measure.dirac toyPath.{u}) toy := by
  intro t n h w
  have hh : ∀ k, h k = (⟨()⟩ : Toy) := fun k => Subsingleton.elim _ _
  have he : toyPath.{u} ∈ originalCylinder t n h w ↔ ∀ k, w k = false := by
    constructor
    · intro hz k
      exact (hz.2 k).symm
    · intro hw
      constructor
      · intro k; exact (hh k).symm
      · intro k; exact (hw k).symm
  rw [measureReal_def, Measure.dirac_apply toyPath]
  simp only [Set.indicator_apply, Pi.one_apply, he]
  by_cases hw : ∀ k, w k = false
  · simp [hw, toy, pathMass]
  · obtain ⟨k, hk⟩ := not_forall.mp hw
    have hp : pathMass toy.matrix n h w = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [toy, hk]
    simp only [if_neg hw, ENNReal.toReal_zero]
    change 0 = 1 * pathMass toy.matrix n h w
    rw [hp, mul_zero]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hu : RowUnifilar toy.matrix := by intro x i j k _ _; exact Subsingleton.elim _ _
  have hh := h toyProducer hu (Measure.dirac toyPath.{u}) toy_cylinders
    0 0 (fun i => nomatch i) (classOf toy.matrix ⟨()⟩)
  simpa [rejected, realize, toy, toyProducer, endpoint, wordMass] using hh

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let a := classOf toy.matrix (⟨()⟩ : Toy)
  refine ⟨⟨toyProducer, 0, 1, a⟩, (fun _ => false), (fun _ => true), ?_⟩
  intro he
  have hg : toyPath ∈ endpointEvent toy.matrix 0 1 (fun _ => false) a := by
    constructor
    · intro k; rfl
    · rfl
  change endpointEvent toy.matrix 0 1 (fun _ => false) a =
    endpointEvent toy.matrix 0 1 (fun _ => true) a at he
  rw [he] at hg
  exact Bool.noConfusion (hg.1 0)

def family : Registration arena.{u} (type_of% (@actual_endpoint_mass.{u})) where
  actual := realize signature.{u} (fun _ t w => @endpointEvent t.1.hidden t.1.finite (@Presentation.matrix t.1.hidden t.1.finite t.1.parameter)
    t.2.1 t.2.2.1 w t.2.2.2) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@actual_endpoint_mass.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_endpoint_mass.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ t w => @endpointEvent t.1.hidden t.1.finite (@Presentation.matrix t.1.hidden t.1.finite t.1.parameter)
      t.2.1 t.2.2.1 w t.2.2.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
    definition := none
    coordinates := #[0, 7, 8, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
