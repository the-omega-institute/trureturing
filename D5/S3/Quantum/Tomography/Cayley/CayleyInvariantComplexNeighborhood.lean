/- GID: D5/S3/Quantum/Tomography/Cayley/CayleyInvariantComplexNeighborhood
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/Cayley/CayleyInvariantComplexNeighborhood
   mirror-E: none(waiver:uniform-analytic-domain)
   anchors: []
   utility: none
   digest: One open reciprocal-invariant complex neighborhood of the real Cayley atlas has uniform pole margins and supports every fixed-matrix residual after arbitrary certified restrictions. -/

import D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/- The domain is the Cayley pullback of 1/2 < |w| < 2. Its rational
   inequality avoids logarithms, square roots and branch choices.
   Inversion is a chart transition only where z is nonzero. No theorem
   asserts a holomorphic reciprocal chart at zero.
   Pruning restricts candidate regions; it is not analytically continued as
   a min/max/Boolean map. A Newton self-map requires an additional margin.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.Cayley.CayleyInvariantComplexNeighborhood

open D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard

/-- A single open neighborhood of the real axis, with both Cayley poles
excluded. Its product is used for every sign chart and every proof-node type. -/
def cayleyNeighborhood : Set ℂ :=
  {z | 10 * |z.im| < 3 * (1 + Complex.normSq z)}

private theorem denominator_normSq (z : ℂ) :
    Complex.normSq (1 + Complex.I * z) = 1 + Complex.normSq z - 2 * z.im ∧
    Complex.normSq (1 - Complex.I * z) = 1 + Complex.normSq z + 2 * z.im := by
  constructor <;>
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] <;> ring

/-- The common domain is open, contains every real coordinate, and gives
uniform strictly positive squared-norm margins for BOTH denominators. -/
theorem cayley_neighborhood_open_real_and_poles :
    IsOpen cayleyNeighborhood ∧
      (∀ t : ℝ, (t : ℂ) ∈ cayleyNeighborhood) ∧
      (∀ z ∈ cayleyNeighborhood,
        (2 / 5 : ℝ) < Complex.normSq (1 - Complex.I * z) ∧
        (2 / 5 : ℝ) < Complex.normSq (1 + Complex.I * z)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply isOpen_lt <;> fun_prop
  · intro t
    change 10 * |(t : ℂ).im| < 3 * (1 + Complex.normSq (t : ℂ))
    simp only [Complex.ofReal_im, abs_zero, mul_zero]
    nlinarith [Complex.normSq_nonneg (t : ℂ)]
  · intro z hz
    change 10 * |z.im| < 3 * (1 + Complex.normSq z) at hz
    obtain ⟨hp, hm⟩ := denominator_normSq z
    constructor <;> nlinarith [Complex.normSq_nonneg z,
      le_abs_self z.im, neg_le_abs z.im]

/-- The SAME domain survives sign changes, conjugation and the reciprocal
signed-Cayley chart change. This is an exact domain identity, not a finite
sample or a shrinkage budget accumulated at every tree depth. -/
theorem cayley_neighborhood_chart_invariance (z : ℂ) :
    ((-z) ∈ cayleyNeighborhood ↔ z ∈ cayleyNeighborhood) ∧
      (star z ∈ cayleyNeighborhood ↔ z ∈ cayleyNeighborhood) ∧
      (z ≠ 0 → ((-z⁻¹) ∈ cayleyNeighborhood ↔ z ∈ cayleyNeighborhood)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cayleyNeighborhood, Complex.normSq_neg]
  · simp [cayleyNeighborhood, Complex.star_def, Complex.normSq_conj]
  · intro hz
    have hq : 0 < Complex.normSq z := by
      exact lt_of_le_of_ne (Complex.normSq_nonneg z)
        (Ne.symm (mt Complex.normSq_eq_zero.mp hz))
    have hq0 : Complex.normSq z ≠ 0 := ne_of_gt hq
    change 10 * |(-z⁻¹).im| < 3 * (1 + Complex.normSq (-z⁻¹)) ↔
      10 * |z.im| < 3 * (1 + Complex.normSq z)
    simp only [Complex.neg_im, Complex.inv_im, neg_div, neg_neg,
      Complex.normSq_neg, Complex.normSq_inv, abs_div, abs_of_pos hq]
    constructor
    · intro h
      calc
        10 * |z.im| = (10 * (|z.im| / Complex.normSq z)) * Complex.normSq z := by
          field_simp [hq0]
        _ < (3 * (1 + (Complex.normSq z)⁻¹)) * Complex.normSq z :=
          mul_lt_mul_of_pos_right h hq
        _ = 3 * (1 + Complex.normSq z) := by field_simp [hq0]; ring
    · intro h
      have hdiv := div_lt_div_of_pos_right h hq
      calc
        10 * (|z.im| / Complex.normSq z) = (10 * |z.im|) / Complex.normSq z := by ring
        _ < (3 * (1 + Complex.normSq z)) / Complex.normSq z := hdiv
        _ = 3 * (1 + (Complex.normSq z)⁻¹) := by field_simp [hq0]; ring

/-- Throughout the common neighborhood, every unit-prefactor Cayley phase
and its reciprocal companion have squared modulus strictly between 1/4 and 4.
The bound is independent of the sign/quarter-turn chart, matrix branch,
subdivision depth and any finite pruning history. -/
theorem cayley_neighborhood_phase_bounds (z s : ℂ)
    (hz : z ∈ cayleyNeighborhood) (hs : Complex.normSq s = 1) :
    (1 / 4 : ℝ) < Complex.normSq (cayleyPhase s z) ∧
      Complex.normSq (cayleyPhase s z) < 4 := by
  have hD := cayley_neighborhood_open_real_and_poles.2.2 z hz
  obtain ⟨hp, hm⟩ := denominator_normSq z
  have hmPos : 0 < Complex.normSq (1 - Complex.I * z) := by linarith [hD.1]
  have hLow : Complex.normSq (1 - Complex.I * z) <
      4 * Complex.normSq (1 + Complex.I * z) := by
    change 10 * |z.im| < 3 * (1 + Complex.normSq z) at hz
    nlinarith [le_abs_self z.im]
  have hHigh : Complex.normSq (1 + Complex.I * z) <
      4 * Complex.normSq (1 - Complex.I * z) := by
    change 10 * |z.im| < 3 * (1 + Complex.normSq z) at hz
    nlinarith [neg_le_abs z.im]
  have hValue : Complex.normSq (cayleyPhase s z) =
      Complex.normSq (1 + Complex.I * z) /
        Complex.normSq (1 - Complex.I * z) := by
    simp only [cayleyPhase, Complex.normSq_div, Complex.normSq_mul, hs, one_mul]
  rw [hValue]
  constructor
  · apply (lt_div_iff₀ hmPos).2
    linarith
  · exact (div_lt_iff₀ hmPos).2 hHigh

private theorem phase_norm_le_two (z s : ℂ)
    (hz : z ∈ cayleyNeighborhood) (hs : Complex.normSq s = 1) :
    ‖cayleyPhase s z‖ ≤ 2 := by
  have h := (cayley_neighborhood_phase_bounds z s hz hs).2
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (cayleyPhase s z)]

private theorem phase_derivative_norm_le_five (z s : ℂ)
    (hz : z ∈ cayleyNeighborhood) (hs : Complex.normSq s = 1) :
    ‖2 * Complex.I * s / (1 - Complex.I * z) ^ 2‖ ≤ 5 := by
  have hn : ‖s‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg s]
  have hD := (cayley_neighborhood_open_real_and_poles.2.2 z hz).1
  have hp : 0 < Complex.normSq (1 - Complex.I * z) := by linarith
  calc
    ‖2 * Complex.I * s / (1 - Complex.I * z) ^ 2‖ =
        2 / Complex.normSq (1 - Complex.I * z) := by
      simp [norm_div, norm_mul, norm_pow, hn, Complex.normSq_eq_norm_sq]
    _ ≤ 5 := (div_le_iff₀ hp).2 (by linarith)

/-- An explicit Jacobian envelope on the same domain. For d=6 and unit
Hadamard coefficients it is 120 per matrix entry. Selecting outcomes or
fixing the gauge only removes rows/columns; it cannot enlarge this bound. -/
theorem paired_cayley_jacobian_uniform_bound
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (s z : Fin d → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hH : ∀ i a, ‖H i a‖ ≤ M)
    (hs : ∀ i, Complex.normSq (s i) = 1)
    (hz : ∀ i, z i ∈ cayleyNeighborhood) :
    ∀ a k, ‖pairedCayleyJacobian H s z a k‖ ≤ 20 * (d : ℝ) * M ^ 2 := by
  have hzneg (i : Fin d) : -z i ∈ cayleyNeighborhood :=
    (cayley_neighborhood_chart_invariance (z i)).1.mpr (hz i)
  have hsstar (i : Fin d) : Complex.normSq (star (s i)) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_conj] using hs i
  have hplus (a : Fin d) :
      ‖∑ i, star (H i a) * cayleyPhase (s i) (z i)‖ ≤ (d : ℝ) * (M * 2) := by
    calc
      ‖∑ i, star (H i a) * cayleyPhase (s i) (z i)‖ ≤
          ∑ i, ‖star (H i a) * cayleyPhase (s i) (z i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, M * 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_star]
        exact mul_le_mul (hH i a) (phase_norm_le_two _ _ (hz i) (hs i))
          (norm_nonneg _) hM
      _ = (d : ℝ) * (M * 2) := by simp
  have hminus (a : Fin d) :
      ‖∑ i, H i a * cayleyPhase (star (s i)) (-z i)‖ ≤ (d : ℝ) * (M * 2) := by
    calc
      ‖∑ i, H i a * cayleyPhase (star (s i)) (-z i)‖ ≤
          ∑ i, ‖H i a * cayleyPhase (star (s i)) (-z i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, M * 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hH i a)
          (phase_norm_le_two _ _ (hzneg i) (hsstar i)) (norm_nonneg _) hM
      _ = (d : ℝ) * (M * 2) := by simp
  intro a k
  have hdp := phase_derivative_norm_le_five (z k) (s k) (hz k) (hs k)
  have hdm : ‖-2 * Complex.I * star (s k) / (1 + Complex.I * z k) ^ 2‖ ≤ 5 := by
    have h := phase_derivative_norm_le_five (-z k) (star (s k)) (hzneg k) (hsstar k)
    simpa only [mul_neg, sub_neg_eq_add, neg_mul, neg_div, norm_neg] using h
  have hcplus : ‖star (H k a) *
      (2 * Complex.I * s k / (1 - Complex.I * z k) ^ 2)‖ ≤ M * 5 := by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hH k a) hdp (norm_nonneg _) hM
  have hcminus : ‖H k a *
      (-2 * Complex.I * star (s k) / (1 + Complex.I * z k) ^ 2)‖ ≤ M * 5 := by
    rw [norm_mul]
    exact mul_le_mul (hH k a) hdm (norm_nonneg _) hM
  have hm5 : 0 ≤ M * 5 := mul_nonneg hM (by norm_num)
  unfold pairedCayleyJacobian
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (M * 5) * ((d : ℝ) * (M * 2)) +
        (M * 5) * ((d : ℝ) * (M * 2)) := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hcplus (hminus a) (norm_nonneg _) hm5
      · rw [norm_mul]
        exact mul_le_mul hcminus (hplus a) (norm_nonneg _) hm5
    _ = 20 * (d : ℝ) * M ^ 2 := by ring

/-- Reciprocal coordinate transport changes only the phase prefactor. The
nonzero-coordinate guard is indispensable even though the global projective
atlas itself has no singularity on the real unit circle. -/
theorem cayley_phase_reciprocal_transition (z s : ℂ)
    (hz : z ≠ 0) (hD : z ∈ cayleyNeighborhood) :
    cayleyPhase s (-z⁻¹) = cayleyPhase (-s) z := by
  have hden : 1 - Complex.I * z ≠ 0 := by
    intro h
    have hpos := cayley_neighborhood_open_real_and_poles.2.2 z hD
    rw [h] at hpos
    norm_num at hpos
  have hD' := (cayley_neighborhood_chart_invariance z).2.2 hz
  have hden' : 1 - Complex.I * (-z⁻¹) ≠ 0 := by
    intro h
    have hpos := cayley_neighborhood_open_real_and_poles.2.2 (-z⁻¹) (hD'.2 hD)
    rw [h] at hpos
    norm_num at hpos
  dsimp [cayleyPhase]
  apply (div_eq_div_iff hden' hden).2
  field_simp [hz]
  ring_nf
  simp [Complex.I_sq]

/-- A single pole-free complex domain serves ANY family of candidate
regions: each region may be produced by splits, restrictions, exclusions,
contractions or tube membership, provided it stays inside that domain.
No holomorphic extension of Boolean pruning decisions is asserted.

This applies to all 32 signs, arbitrary fixed Hadamard types and arbitrary
pruning depth. Actual Newton self-invariance is a separate inequality. -/
theorem paired_residual_holomorphic_on_every_restriction
    {d : ℕ} {Node : Type*} (H : Matrix (Fin d) (Fin d) ℂ)
    (s : Fin d → ℂ) (regions : Node → Set (Fin d → ℂ))
    (hregions : ∀ node z, z ∈ regions node → ∀ k, z k ∈ cayleyNeighborhood) :
    ∀ node, DifferentiableOn ℂ (pairedCayleyResidual H s) (regions node) := by
  intro node z hz
  have hpoles (k : Fin d) :=
    cayley_neighborhood_open_real_and_poles.2.2 (z k) (hregions node z hz k)
  have hm (k : Fin d) : 1 - Complex.I * z k ≠ 0 := by
    intro h
    have hp := (hpoles k).1
    rw [h] at hp
    norm_num at hp
  have hp (k : Fin d) : 1 + Complex.I * z k ≠ 0 := by
    intro h
    have hp := (hpoles k).2
    rw [h] at hp
    norm_num at hp
  exact (paired_cayley_residual_hasFDerivAt H s z hm hp).differentiableAt.differentiableWithinAt

#print axioms cayley_neighborhood_open_real_and_poles
#print axioms cayley_neighborhood_chart_invariance
#print axioms cayley_neighborhood_phase_bounds
#print axioms paired_cayley_jacobian_uniform_bound
#print axioms cayley_phase_reciprocal_transition
#print axioms paired_residual_holomorphic_on_every_restriction

end D5.S3.Quantum.Tomography.Cayley.CayleyInvariantComplexNeighborhood
