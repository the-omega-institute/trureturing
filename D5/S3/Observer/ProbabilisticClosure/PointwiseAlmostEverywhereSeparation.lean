/- GID: D5/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/PointwiseAlmostEverywhereSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise sufficiency implies a.e. descent; one null point refutes the converse. -/

/- Library-search audit trail (2026-08-27):
   * All ten current `Observer/ProbabilisticClosure` signatures were read.
     `StrongLumpabilityDescent` concerns pushed-forward PMF rows on the realized image;
     it neither states nor is rebuilt as the arbitrary-target a.e. separation below.
   * `ConullImageProbabilityIsomorphism` pulls a law back along a measurable injection
     with conull image; it does not compare a.e. and pointwise fiber sufficiency.
   * `SingleSampleLawNonimplication`, `GraphMechanismLawSeparation`, and
     `FiniteMarginalGlobalReadoutContrast` are nonimplication patterns for different data.
     The other five directory modules contain no a.e. fiber-factorization criterion.
   * Repository hit `AnswerabilityCriterion.answerability_criterion` packages the
     anchored factorization. Pinned `Function.factorsThrough_iff` weakens its anchor
     to exactly `[Nonempty Y]` and is applied directly, rather than reproved.
   * Pinned Mathlib hits `Measure.ae_ne`, `Real.volume_singleton`, and
     `Real.volume_univ` verify the null defect and the nonzero measure.
   * No prime parameter, primality assumption, or natural-number index occurs here.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace D5.S3.Observer.ProbabilisticClosure.PointwiseAlmostEverywhereSeparation

/-- The target has one value on each readout fiber, with no exceptional states. -/
def PointwiseSufficient {X Q Y : Type*} (q : X → Q) (T : X → Y) : Prop :=
  Function.FactorsThrough T q

/-- The target factors through the readout outside a set of measure zero. -/
def AlmostEverywhereSufficient {X Q Y : Type*} [MeasurableSpace X]
    (mu : Measure X) (q : X → Q) (T : X → Y) : Prop :=
  ∃ Tbar : Q → Y, T =ᵐ[mu] Tbar ∘ q

/-- Pointwise fiber sufficiency gives an exact factorization, hence an a.e.
factorization for every measure. Target nonemptiness supplies a value with
which to extend the exact factor off the realized image of `q`. -/
theorem pointwise_sufficient_implies_almost_everywhere_sufficient
    {X Q Y : Type*} [MeasurableSpace X] [Nonempty Y]
    (mu : Measure X) (q : X → Q) (T : X → Y)
    (hPointwise : PointwiseSufficient q T) :
    AlmostEverywhereSufficient mu q T := by
  have hFactor : ∃ Tbar : Q → Y, T = Tbar ∘ q :=
    (Function.factorsThrough_iff (f := q) T).mp hPointwise
  obtain ⟨Tbar, hTbar⟩ := hFactor
  refine ⟨Tbar, Filter.Eventually.of_forall ?_⟩
  intro x
  exact congrFun hTbar x

#print axioms pointwise_sufficient_implies_almost_everywhere_sufficient

/-- Without a target value, pointwise fiber constancy need not provide a factor
on the whole readout codomain. This is the necessary counterexample for the
public target-nonemptiness instance. -/
theorem nonempty_target_is_necessary :
    ∃ (q : Empty → PUnit) (T : Empty → Empty),
      PointwiseSufficient q T ∧
        ¬AlmostEverywhereSufficient (0 : Measure Empty) q T := by
  let q : Empty → PUnit := fun x => nomatch x
  let T : Empty → Empty := fun x => nomatch x
  refine ⟨q, T, ?_, ?_⟩
  · intro x
    exact nomatch x
  · rintro ⟨Tbar, _⟩
    exact Empty.elim (Tbar PUnit.unit)

#print axioms nonempty_target_is_necessary

/-- Under the zero measure, every supplied factor agrees a.e.; the a.e.
equality itself is therefore vacuous even when pointwise equality fails. -/
theorem zero_measure_almost_everywhere_sufficient
    {X Q Y : Type*} [MeasurableSpace X]
    (q : X → Q) (T : X → Y) (Tbar : Q → Y) :
    AlmostEverywhereSufficient (0 : Measure X) q T := by
  refine ⟨Tbar, ?_⟩
  rw [ae_zero]
  exact Filter.eventually_bot

#print axioms zero_measure_almost_everywhere_sufficient

/-- An injective readout determines every target pointwise. In particular,
the identity readout always satisfies pointwise sufficiency. -/
theorem injective_readout_pointwise_sufficient
    {X Q Y : Type*} (q : X → Q) (T : X → Y) (hq : Function.Injective q) :
    PointwiseSufficient q T := by
  intro x y hxy
  exact congrArg T (hq hxy)

#print axioms injective_readout_pointwise_sufficient

/-- A constant target is both pointwise and a.e. sufficient for every readout
and every measure, including constant and zero-valued readouts. -/
theorem constant_target_sufficient
    {X Q Y : Type*} [MeasurableSpace X]
    (mu : Measure X) (q : X → Q) (c : Y) :
    PointwiseSufficient q (fun _ => c) ∧
      AlmostEverywhereSufficient mu q (fun _ => c) := by
  constructor
  · intro _ _ _
    rfl
  · refine ⟨fun _ => c, Filter.Eventually.of_forall ?_⟩
    intro _
    rfl

#print axioms constant_target_sufficient

/-- Lebesgue measure is the measure in the strict counterexample. -/
def nullPointMeasure : Measure ℝ :=
  volume

/-- The strict counterexample has one readout fiber. -/
def nullPointReadout : ℝ → PUnit :=
  fun _ => PUnit.unit

/-- The target differs from `false` only at the origin. -/
def nullPointTarget : ℝ → Bool :=
  fun x => if x = 0 then true else false

/-- The a.e. factor is constantly false on the one-point readout space. -/
def nullPointFactor : PUnit → Bool :=
  fun _ => false

/-- The counterexample measure is nonzero, so its a.e. clause is not true merely
because the whole measure vanishes. -/
theorem null_point_measure_ne_zero : nullPointMeasure ≠ 0 := by
  intro hzero
  have huniv := congrArg (fun mu : Measure ℝ => mu Set.univ) hzero
  simp [nullPointMeasure] at huniv

#print axioms null_point_measure_ne_zero

/-- The sole point where the counterexample target changes has zero Lebesgue measure. -/
theorem null_point_singleton_measure_zero :
    nullPointMeasure ({0} : Set ℝ) = 0 := by
  simp [nullPointMeasure]

#print axioms null_point_singleton_measure_zero

/-- Zero and one lie in the same readout fiber but have different target values. -/
theorem null_point_same_fiber_different_target :
    ∃ x y : ℝ, nullPointReadout x = nullPointReadout y ∧
      nullPointTarget x ≠ nullPointTarget y := by
  refine ⟨0, 1, rfl, ?_⟩
  simp [nullPointTarget]

#print axioms null_point_same_fiber_different_target

/-- The constantly false factor agrees with the target outside the null origin. -/
theorem null_point_almost_everywhere_sufficient :
    AlmostEverywhereSufficient nullPointMeasure nullPointReadout nullPointTarget := by
  refine ⟨nullPointFactor, ?_⟩
  change nullPointTarget =ᵐ[(volume : Measure ℝ)] nullPointFactor ∘ nullPointReadout
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  simp [nullPointTarget, nullPointFactor, hx]

#print axioms null_point_almost_everywhere_sufficient

/-- FPOD Principle 118.1: a.e. sufficiency is strictly weaker than pointwise
sufficiency. The displayed null-point construction satisfies the former and
has an explicit same-fiber pair refuting the latter. -/
theorem fpod_principle_118_1 :
    AlmostEverywhereSufficient nullPointMeasure nullPointReadout nullPointTarget ∧
      ¬PointwiseSufficient nullPointReadout nullPointTarget := by
  refine ⟨null_point_almost_everywhere_sufficient, ?_⟩
  intro hPointwise
  obtain ⟨x, y, hFiber, hTarget⟩ := null_point_same_fiber_different_target
  exact hTarget (hPointwise hFiber)

#print axioms fpod_principle_118_1

/-- The empty, singleton, identity, constant, and zero-measure audit inputs are
all explicit instances of the public declarations above. -/
example :
    PointwiseSufficient (id : Empty → Empty) (id : Empty → Empty) := by
  exact injective_readout_pointwise_sufficient id id Function.injective_id

example :
    AlmostEverywhereSufficient (0 : Measure Empty)
      (id : Empty → Empty) (id : Empty → Empty) := by
  exact zero_measure_almost_everywhere_sufficient
    (id : Empty → Empty) (id : Empty → Empty) (id : Empty → Empty)

example :
    PointwiseSufficient (id : Unit → Unit) (fun _ : Unit => false) ∧
      AlmostEverywhereSufficient (Measure.dirac ())
        (id : Unit → Unit) (fun _ : Unit => false) := by
  exact constant_target_sufficient (X := Unit) (Q := Unit) (Y := Bool)
    (Measure.dirac ()) id false

end D5.S3.Observer.ProbabilisticClosure.PointwiseAlmostEverywhereSeparation
