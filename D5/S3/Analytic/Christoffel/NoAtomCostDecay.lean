/- GID: D5/S3/Analytic/Christoffel/NoAtomCostDecay
   generality: G
   mirror-B: D5/B/S3/Analytic/Christoffel/NoAtomCostDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Outside the supported circle, Christoffel evaluation costs decay exponentially. -/

import D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-09-02):
   * The repository owner `ChristoffelAtomFloor.christoffelEvaluationCost`
     is imported directly; this module does not create a second cost definition.
   * Pinned Mathlib supplies `Polynomial.eval_monomial`,
     `Polynomial.natDegree_monomial_le`, `Measure.support_mem_ae`,
     `MeasureTheory.lintegral_const`, `iInf_le`, and
     `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`.
   * Loogle, LeanSearch, and Reservoir exposed no whole-theorem or third-party
     Christoffel no-atom decay result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Christoffel.NoAtomCostDecay

open Filter MeasureTheory Set Topology
open scoped ENNReal

abbrev christoffelEvaluationCost :=
  D5.S3.Analytic.ZetaObservation.ChristoffelAtomFloor.christoffelEvaluationCost

/-- The complex unit circle that carries the Cayley zero measure under the
support hypothesis. -/
def complexUnitCircle : Set Complex := {z | ‖z‖ = 1}

/-- The source polynomial `p_N(z) = (z / w)^N`, represented as its single
degree-`N` monomial. -/
def observationPolynomial (w : Complex) (degree : Nat) : Polynomial Complex :=
  Polynomial.monomial degree (w⁻¹ ^ degree)

lemma observationPolynomial_eval (w z : Complex) (degree : Nat) :
    (observationPolynomial w degree).eval z = (z / w) ^ degree := by
  simp [observationPolynomial, Polynomial.eval_monomial, div_eq_mul_inv, mul_comm,
    mul_pow]

lemma observationPolynomial_degree_le (w : Complex) (degree : Nat) :
    (observationPolynomial w degree).natDegree ≤ degree := by
  exact Polynomial.natDegree_monomial_le _

lemma observationPolynomial_eval_center
    (w : Complex) (outsideCircle : 1 < ‖w‖) (degree : Nat) :
    (observationPolynomial w degree).eval w = 1 := by
  have wNonzero : w ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one outsideCircle))
  simp [observationPolynomial_eval, wNonzero]

lemma observationPolynomial_norm_on_circle
    (w z : Complex) (degree : Nat) (zOnCircle : z ∈ complexUnitCircle) :
    ‖(observationPolynomial w degree).eval z‖ = ‖w‖⁻¹ ^ degree := by
  rw [observationPolynomial_eval, norm_pow, norm_div]
  change ‖z‖ = 1 at zOnCircle
  rw [zOnCircle, one_div]

/-- For the finite Cayley zero measure, support on the unit circle and an
evaluation point outside that circle force the normalized monomial energy,
the Christoffel upper bound, and hence the cost itself to vanish
geometrically. The support premise is the source volume's RH-equivalent
condition for its project measure `mu_a`; it is deliberately public here. -/
theorem no_atom_cost_decay
    (muA : Measure Complex) [finiteMeasure : IsFiniteMeasure muA] (w : Complex)
    (supportOnCircle : muA.support ⊆ complexUnitCircle)
    (outsideCircle : 1 < ‖w‖) :
    (∀ degree : Nat, (observationPolynomial w degree).eval w = 1) ∧
    (∀ (degree : Nat) (z : Complex), z ∈ complexUnitCircle →
      ‖(observationPolynomial w degree).eval z‖ = ‖w‖⁻¹ ^ degree) ∧
    (∀ degree : Nat, 0 ≤ christoffelEvaluationCost muA w degree) ∧
    (∀ degree : Nat,
      christoffelEvaluationCost muA w degree ≤
        muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2))) ∧
    Tendsto (fun degree : Nat => christoffelEvaluationCost muA w degree)
      atTop (𝓝 0) := by
  have almostEverywhereOnCircle : ∀ᵐ z ∂muA, z ∈ complexUnitCircle := by
    filter_upwards [Measure.support_mem_ae] with z zInSupport
    exact supportOnCircle zInSupport
  have circleHasFullMass : muA Set.univ = muA complexUnitCircle := by
    apply measure_congr
    filter_upwards [almostEverywhereOnCircle] with z zOnCircle
    apply propext
    constructor
    · intro _zInUniverse
      exact zOnCircle
    · intro _zOnCircle
      exact Set.mem_univ z
  have polynomialEnergy (degree : Nat) :
      (∫⁻ z, ENNReal.ofReal
          (Complex.normSq ((observationPolynomial w degree).eval z)) ∂muA) =
        muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) := by
    calc
      (∫⁻ z, ENNReal.ofReal
          (Complex.normSq ((observationPolynomial w degree).eval z)) ∂muA) =
          ∫⁻ _z, ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) ∂muA := by
            apply lintegral_congr_ae
            filter_upwards [almostEverywhereOnCircle] with z zOnCircle
            rw [Complex.normSq_eq_norm_sq,
              observationPolynomial_norm_on_circle w z degree zOnCircle, pow_mul]
      _ = ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) * muA Set.univ :=
        lintegral_const _
      _ = muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) := by
        rw [circleHasFullMass, mul_comm]
  have costUpperBound (degree : Nat) :
      christoffelEvaluationCost muA w degree ≤
        muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) := by
    let candidate :
        {polynomial : Polynomial Complex //
          polynomial.natDegree ≤ degree ∧ polynomial.eval w = 1} :=
      ⟨observationPolynomial w degree,
        observationPolynomial_degree_le w degree,
        observationPolynomial_eval_center w outsideCircle degree⟩
    exact (iInf_le (fun polynomial :
      {polynomial : Polynomial Complex //
        polynomial.natDegree ≤ degree ∧ polynomial.eval w = 1} =>
          ∫⁻ z, ENNReal.ofReal (Complex.normSq (polynomial.1.eval z)) ∂muA)
      candidate).trans_eq (polynomialEnergy degree)
  have inverseNormLtOne : ‖w‖⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ outsideCircle
  have squaredInverseNormLtOne : ‖w‖⁻¹ ^ 2 < 1 :=
    pow_lt_one₀ (inv_nonneg.mpr (norm_nonneg w)) inverseNormLtOne (by norm_num)
  have ennrealSquaredInverseNormLtOne :
      ENNReal.ofReal (‖w‖⁻¹ ^ 2) < 1 :=
    ENNReal.ofReal_lt_one.mpr squaredInverseNormLtOne
  have upperBoundTendsToZero :
      Tendsto
        (fun degree : Nat =>
          muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)))
        atTop (𝓝 0) := by
    have geometricTendsToZero :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ennrealSquaredInverseNormLtOne
    have finiteCircleMass : muA complexUnitCircle ≠ ∞ :=
      ((measure_mono (Set.subset_univ complexUnitCircle)).trans_lt
        finiteMeasure.measure_univ_lt_top).ne
    have scaledTendsToZero :
        Tendsto
          (fun degree : Nat =>
            muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ 2) ^ degree)
          atTop (𝓝 0) := by
      simpa using
        ENNReal.Tendsto.const_mul geometricTendsToZero (Or.inr finiteCircleMass)
    convert scaledTendsToZero using 1
    funext degree
    congr 1
    rw [Nat.mul_comm, pow_mul,
      ENNReal.ofReal_pow (sq_nonneg ‖w‖⁻¹)]
  refine ⟨observationPolynomial_eval_center w outsideCircle,
    (fun degree z hz => observationPolynomial_norm_on_circle w z degree hz),
    fun _ => bot_le, costUpperBound, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    upperBoundTendsToZero (fun _ => bot_le) costUpperBound

/-- Reverse probe: the public theorem exposes the source's exponential upper
bound as an independently projectable conclusion. -/
example
    (muA : Measure Complex) [IsFiniteMeasure muA] (w : Complex)
    (supportOnCircle : muA.support ⊆ complexUnitCircle)
    (outsideCircle : 1 < ‖w‖) (degree : Nat) :
    christoffelEvaluationCost muA w degree ≤
      muA complexUnitCircle * ENNReal.ofReal (‖w‖⁻¹ ^ (degree * 2)) :=
  (no_atom_cost_decay muA w supportOnCircle outsideCircle).2.2.2.1 degree

/-- Trivialization probe: the key outside-circle premise excludes the zero
evaluation point, so `w = 0` cannot make the theorem vacuous. -/
example : ¬(1 < ‖(0 : Complex)‖) := by norm_num

/-- Separation probe: at degree one the witness distinguishes zero from the
exterior evaluation point, so it has not collapsed to a constant polynomial. -/
example (w : Complex) (outsideCircle : 1 < ‖w‖) :
    (observationPolynomial w 1).eval 0 = 0 ∧
    (observationPolynomial w 1).eval w = 1 := by
  exact ⟨by simp [observationPolynomial_eval],
    observationPolynomial_eval_center w outsideCircle 1⟩

#print axioms no_atom_cost_decay

end D5.S3.Analytic.Christoffel.NoAtomCostDecay
