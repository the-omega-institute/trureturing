/- GID: D5/S3/Zeros/Resolvent/ActualXiDictionary
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiDictionary
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Complete actual xi reflection-folded spectrum Taylor moments and real-polynomial Hankel dictionary. -/

import D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.ActualXiDictionary
open Complex Finset
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
open D5.S3.Zeros.Resolvent.ActualXiTaylorBounds
open D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open D5.S3.Zeros.Symmetry.ZeroOrbitCardinality
open scoped ComplexConjugate

/-- The full actual dictionary, with no spectral convergence or RH premise. -/
structure Dictionary : Prop where
  reflection_section : ∀ n : ℕ, ∃! k : PositiveZero,
    n = (k : ℕ) ∨ n = actualData.reflection k
  original_node : ∀ n : PositiveZero, node n = -1 / (actualData.zero n - 1 / 2) ^ 2
  nodes_injective : Function.Injective node
  nodes_bounds : ∀ n : PositiveZero, 0 < ‖node n‖ ∧ ‖node n‖ < 1
  weights_nonzero : ∀ n : PositiveZero, weight n ≠ 0
  weights_formula : ∀ n : PositiveZero,
    weight n = 2 * (actualData.multiplicity n : ℂ) * node n ^ 2 / (1 + node n / 4)
  denominators_nonzero : ∀ n : PositiveZero, 1 + node n / 4 ≠ 0
  weights_absolute : Summable (fun n : PositiveZero => ‖weight n‖)
  node_cuts_finite : ∀ ε : ℝ, 0 < ε → {n : PositiveZero | ε ≤ ‖node n‖}.Finite
  conjugation_involution : Function.Involutive conjugation
  conjugate_nodes : ∀ n : PositiveZero, node (conjugation n) = conj (node n)
  conjugate_weights : ∀ n : PositiveZero, weight (conjugation n) = conj (weight n)
  conjugate_multiplicity : ∀ n : PositiveZero,
    actualData.multiplicity (conjugation n) = actualData.multiplicity n
  real_node_iff : ∀ n : PositiveZero, (node n).im = 0 ↔ (actualData.zero n).re = 1 / 2
  real_node_positive : ∀ n : PositiveZero, (node n).im = 0 →
    0 < (node n).re ∧ 0 < (weight n).re ∧ (weight n).im = 0
  off_line_pair : ∀ n : PositiveZero, (actualData.zero n).re ≠ 1 / 2 →
    ({(n : ℕ), actualData.reflection n, actualData.conjugation n,
      actualData.conjugation (actualData.reflection n)} : Finset ℕ).card = 4 ∧
    node n ≠ conj (node n) ∧
    ∀ k : PositiveZero,
      (k : ℕ) ∈ ({(n : ℕ), actualData.reflection n, actualData.conjugation n,
        actualData.conjugation (actualData.reflection n)} : Finset ℕ) ↔
      k = n ∨ k = conjugation n
  xi_identity : ∀ w : ℂ, ‖w‖ < 1 / 4 →
    HasSum (fun n : PositiveZero => w * weight n / (1 - node n * w ^ 2)) (xiOdd w)
  folded_resolvent : ∀ w : ℂ, ‖w‖ < 1 / 4 →
    Summable (fun n : PositiveZero => weight n / (1 - node n * w ^ 2)) ∧
    xiOdd w = w * ∑' n : PositiveZero, weight n / (1 - node n * w ^ 2)
  xi_analytic : ∀ w : ℂ, ‖w‖ < 1 / 4 → AnalyticAt ℂ xiOdd w
  moment_series : ∀ w : ℂ, ‖w‖ < 1 / 4 →
    HasSum (fun j : ℕ => moment j * w ^ (2 * j + 1)) (xiOdd w)
  taylor_moments : ∀ j : ℕ,
    iteratedDeriv (2 * j + 1) xiOdd 0 / ((2 * j + 1).factorial : ℂ) = moment j
  real_moments : ∀ j : ℕ, (moment j).im = 0
  even_derivatives : ∀ j : ℕ, iteratedDeriv (2 * j) xiOdd 0 = 0
  radius_bound : 0 ≤ radius ∧ radius ≤ 1
  disk_bound : ∀ r : ℝ, 0 ≤ r → r < 1 / 4 → ∀ w : ℂ, ‖w‖ ≤ r →
    ‖xiOdd w‖ ≤ totalWeight * r / (1 - radius * r ^ 2)
  remainder_bound : ∀ r : ℝ, 0 ≤ r → r < 1 / 4 → ∀ w : ℂ, ‖w‖ ≤ r → ∀ J : ℕ,
    ‖xiOdd w - ∑ j ∈ range (J + 1), moment j * w ^ (2 * j + 1)‖ ≤
      totalWeight * r * (radius * r ^ 2) ^ (J + 1) / (1 - radius * r ^ 2)
  folded_normal : ∀ r : ℝ, 0 ≤ r → r < 1 / 4 →
    HasSumUniformlyOn (fun n : PositiveZero => fun w : ℂ =>
      w * weight n / (1 - node n * w ^ 2)) xiOdd (Metric.closedBall 0 r)
  hankel : ∀ (N m : ℕ) (u : Fin (N + 1) → ℝ),
    (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ))) =
    (∑' n : PositiveZero, weight n *
      (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2).re
  rh_nonnegative : RiemannHypothesis → ∀ (N m : ℕ) (u : Fin (N + 1) → ℝ),
    0 ≤ ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ))

/-- Actual xi, actual multiplicities, the complete folded spectrum and every Taylor/Hankel order. -/
theorem actual_xi_dictionary : Dictionary := by
  classical
  refine {
    reflection_section := ?_
    original_node := node_original
    nodes_injective := node_injective
    nodes_bounds := fun n => ⟨norm_pos_iff.mpr (node_ne_zero n), node_norm_lt_one n⟩
    weights_nonzero := weight_ne_zero
    weights_formula := weight_node
    denominators_nonzero := node_denominator_ne_zero
    weights_absolute := weight_norm_summable
    node_cuts_finite := node_large_finite
    conjugation_involution := tau_involutive
    conjugate_nodes := node_conjugation
    conjugate_weights := weight_conjugation
    conjugate_multiplicity := multiplicity_conjugation
    real_node_iff := node_real_iff
    real_node_positive := node_real_positive
    off_line_pair := ?_
    xi_identity := actual_xi_folded_hasSum
    folded_resolvent := ?_
    folded_resolvent : ∀ w : ℂ, ‖w‖ < 1 / 4 →
    Summable (fun n : PositiveZero => weight n / (1 - node n * w ^ 2)) ∧
    xiOdd w = w * ∑' n : PositiveZero, weight n / (1 - node n * w ^ 2)
  xi_analytic := actual_xi_analytic
    moment_series := actual_xi_moment_hasSum
    taylor_moments := actual_xi_taylor_moment
    real_moments := moment_real
    even_derivatives := actual_xi_even_derivative
    radius_bound := radius_bounds
    disk_bound := actual_xi_disk_bound
    remainder_bound := actual_xi_taylor_remainder
    folded_normal := fun r hr hr1 => (actual_xi_folded_normal r hr hr1).2
    hankel := actual_xi_hankel_identity
    rh_nonnegative := actual_xi_hankel_nonnegative_of_rh }
  · intro n
    have hn : (actualData.zero n).im ≠ 0 := by
      intro h
      have ht := actual_ordinate_sq_gt_one n
      rw [h] at ht
      norm_num at ht
    by_cases hp : 0 < (actualData.zero n).im
    · refine ⟨⟨n, hp⟩, Or.inl rfl, ?_⟩
      intro k hk
      rcases hk with hk | hk
      · exact Subtype.ext hk.symm
      · have hi := congrArg (fun j : ℕ => (actualData.zero j).im) hk
        rw [actualData.zero_reflection] at hi
        simp only [Complex.sub_im, Complex.one_im, zero_sub] at hi
        linarith [k.property]
    · have hneg : (actualData.zero n).im < 0 := lt_of_le_of_ne (le_of_not_gt hp) hn
      have hpos : 0 < (actualData.zero (actualData.reflection n)).im := by
        rw [actualData.zero_reflection]
        simpa using neg_pos.mpr hneg
      refine ⟨⟨actualData.reflection n, hpos⟩, Or.inr (actualData.reflection_reflection n).symm, ?_⟩
      intro k hk
      rcases hk with hk | hk
      · have hi := congrArg (fun j : ℕ => (actualData.zero j).im) hk
        linarith [k.property]
      · apply Subtype.ext
        have he := congrArg actualData.reflection hk
        simpa using he.symm
  · intro n hoff
    have hc : actualData.conjugation n ≠ (n : ℕ) := by
      intro h
      have hi := congrArg (fun j : ℕ => (actualData.zero j).im) h
      rw [actualData.zero_conjugation, Complex.conj_im] at hi
      linarith [n.property]
    refine ⟨zero_orbit_card_four_of_off_line actualData n hc hoff, ?_, ?_⟩
    · intro h
      have hi := congrArg Complex.im h
      simp only [Complex.conj_im] at hi
      exact hoff ((node_real_iff n).mp (by linarith))
    · intro k
      have hr : (k : ℕ) ≠ actualData.reflection n := by
        intro h
        have hi := k.property
        rw [h, actualData.zero_reflection] at hi
        simp only [Complex.sub_im, Complex.one_im, zero_sub] at hi
        linarith [n.property]
      have hc' : (k : ℕ) ≠ actualData.conjugation n := by
        intro h
        have hi := k.property
        rw [h, actualData.zero_conjugation, Complex.conj_im] at hi
        linarith [n.property]
      have hm : ((conjugation n : PositiveZero) : ℕ) =
          actualData.conjugation (actualData.reflection n) := by
        exact zero_symmetries_commute actualData n
      simp only [Finset.mem_insert, Finset.mem_singleton, hr, hc', false_or, or_false]
      rw [← hm]
      exact or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm

  · intro w hw
    by_cases hz : w = 0
    · subst w
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero, div_one]
      refine ⟨weight_norm_summable.of_norm, ?_⟩
      rw [xiOdd_square]
      simp
    · have hs : HasSum (fun n : PositiveZero => weight n / (1 - node n * w ^ 2))
          (xiOdd w / w) := by
        convert (actual_xi_folded_hasSum w hw).div_const w using 1
        funext n
        have hd := resolvent_denominator_ne_zero n w (by linarith)
        field_simp [hz, hd]
      refine ⟨hs.summable, ?_⟩
      rw [hs.tsum_eq]
      field_simp [hz]

#print axioms actual_xi_dictionary
end D5.S3.Zeros.Resolvent.ActualXiDictionary
