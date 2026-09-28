/- GID: D5/S3/Observer/Linear/GradedExponentialRemainder
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GradedExponentialRemainder
   mirror-E: none(waiver:general-banach-algebra-estimate)
   anchors: []
   digest: Derive an actual uniform anisotropically scaled exponential observation remainder from vanishing low derivative readouts. -/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic

/-!
Unlike a certificate taking a Taylor bound as input, this module obtains the
bound from the actual Banach-algebra exponential series. A fixed linear
readout L annihilates B^k below order j; this is the mathematical derivative
layer hypothesis. The result is uniform in the rescaled time s in [0,1].

For the full Gramian theorem one must still assemble the actual orthogonal
layer projections, integrate in s, prove positivity, and compare sorted
spectra. Those steps are not asserted by this remainder theorem alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.Linear.GradedExponentialRemainder

open NormedSpace Finset
open scoped BigOperators Topology

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine exponential Taylor polynomial with m terms. -/
def taylor (m : ℕ) (x : A) : A :=
  ∑ k ∈ Finset.range m, ((Nat.factorial k : ℝ)⁻¹) • x^k

/-- A uniform small-ball remainder for all truncation orders, obtained from
Mathlib's actual convergent power series for the exponential. -/
theorem exponential_uniform_remainder :
    ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0,
      ∀ (x : A), ‖x‖ < 1 → ∀ m : ℕ,
        ‖NormedSpace.exp x - taylor m x‖ ≤ C * (a * ‖x‖)^m := by
  have hr : 0 < (NormedSpace.expSeries ℝ A).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact ENNReal.zero_lt_top
  have hp := NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos hr
  have hball : ((1 : ℝ≥0) : ℝ≥0∞) < (NormedSpace.expSeries ℝ A).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    simp
  obtain ⟨a, ha, C, hC, hbound⟩ := hp.uniform_geometric_approx' hball
  refine ⟨a, ha, C, hC, ?_⟩
  intro x hx m
  have h := hbound x (by simpa only [Metric.mem_ball, dist_zero_right] using hx) m
  simpa only [zero_add, FormalMultilinearSeries.partialSum,
    NormedSpace.expSeries_apply_eq, NNReal.coe_one, div_one, taylor] using h

/-- Low derivative annihilation collapses the actual Taylor polynomial to
its first visible term; no leading coefficient is supplied separately. -/
theorem observed_taylor_first (B : A) (L : A →L[ℝ] E) (j : ℕ)
    (hvanish : ∀ k < j, L (B^k) = 0) (u : ℝ) :
    L (taylor (j+1) (u • B)) =
      (u^j / (Nat.factorial j : ℝ)) • L (B^j) := by
  classical
  unfold taylor
  rw [map_sum]
  simp only [map_smul, smul_pow, smul_smul]
  have hsum :
      (∑ k ∈ Finset.range (j+1), ((Nat.factorial k : ℝ)⁻¹ * u^k) • L (B^k)) =
        ((Nat.factorial j : ℝ)⁻¹ * u^j) • L (B^j) := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      have hkj' : k < j := by
        have := Finset.mem_range.mp hk
        omega
      rw [hvanish k hkj', smul_zero]
    · intro hj
      exact (hj (Finset.mem_range.mpr (Nat.lt_succ_self j))).elim
  rw [hsum]
  congr 1
  ring

/-- Uniform, quantitative O(T) error after dividing by the true derivative
order. Its constant is constructed from the exponential remainder; it is
not an assumed asymptotic or supplied Gramian comparison. -/
theorem uniform_scaled_derivative_layer (B : A) (L : A →L[ℝ] E) (j : ℕ)
    (hvanish : ∀ k < j, L (B^k) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 < T → T * ‖B‖ < 1 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖(T^j)⁻¹ • L (NormedSpace.exp ((T*s) • B)) -
          (s^j / (Nat.factorial j : ℝ)) • L (B^j)‖ ≤ K * T := by
  obtain ⟨a, ha, C, hC, hbound⟩ := exponential_uniform_remainder (A := A)
  have ha0 : 0 ≤ a := ha.1.le
  have hC0 : 0 ≤ C := hC.le
  let K : ℝ := ‖L‖ * C * (a * ‖B‖)^(j+1)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro T hT hTB s hs
  have hTs : 0 ≤ T*s := mul_nonneg hT.le hs.1
  have hx : ‖(T*s) • B‖ ≤ T * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hTs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hT.le hs.2) (norm_nonneg _)
  have hrem := hbound ((T*s) • B) (hx.trans_lt hTB) (j+1)
  have hb : ‖L (NormedSpace.exp ((T*s) • B)) -
      ((T*s)^j / (Nat.factorial j : ℝ)) • L (B^j)‖ ≤
        ‖L‖ * C * (a * (T * ‖B‖))^(j+1) := by
    rw [← observed_taylor_first B L j hvanish (T*s), ← map_sub]
    calc
      _ ≤ ‖L‖ * ‖NormedSpace.exp ((T*s) • B) - taylor (j+1) ((T*s) • B)‖ :=
        L.le_opNorm _
      _ ≤ ‖L‖ * (C * (a * ‖(T*s) • B‖)^(j+1)) :=
        mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
      _ ≤ ‖L‖ * (C * (a * (T * ‖B‖))^(j+1)) := by gcongr
      _ = _ := by ring
  have hp : T^j ≠ 0 := pow_ne_zero j (ne_of_gt hT)
  have hsimpl : (T^j)⁻¹ •
      (((T*s)^j / (Nat.factorial j : ℝ)) • L (B^j)) =
        (s^j / (Nat.factorial j : ℝ)) • L (B^j) := by
    rw [smul_smul, mul_pow]
    congr 1
    field_simp [hp]
  rw [← hsimpl, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hT j))]
  calc
    _ ≤ (T^j)⁻¹ * (‖L‖ * C * (a * (T * ‖B‖))^(j+1)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg hT.le j))
    _ = K * T := by
      dsimp [K]
      simp only [mul_pow, pow_succ]
      field_simp [hp, ne_of_gt hT]
      <;> ring

/-- The time-window restriction is nonvacuous for every bounded generator. -/
theorem explicit_window_radius (B : A) :
    0 < (‖B‖ + 1)⁻¹ ∧
      ∀ T : ℝ, 0 < T → T < (‖B‖ + 1)⁻¹ → T * ‖B‖ < 1 := by
  have hpos : 0 < ‖B‖ + 1 := by positivity
  refine ⟨inv_pos.mpr hpos, ?_⟩
  intro T hT hsmall
  have hm : T * (‖B‖ + 1) < 1 := by
    apply (lt_div_iff₀ hpos).mp
    simpa only [one_div] using hsmall
  nlinarith

#print axioms exponential_uniform_remainder
#print axioms observed_taylor_first
#print axioms uniform_scaled_derivative_layer
#print axioms explicit_window_radius
end D5.S3.Observer.Linear.GradedExponentialRemainder
