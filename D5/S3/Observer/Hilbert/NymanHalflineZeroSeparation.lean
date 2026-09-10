/- GID: D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation
   generality: I
   mirror-B: D5/B/S3/Observer/Hilbert/NymanHalflineZeroSeparation
   mirror-E: none(waiver:unbounded-analytic-construction)
   anchors: []
   utility: none
   digest: Conditional half-line separation at a nontrivial zeta zero. -/

import D5.S3.Observer.Hilbert.NymanHalflineMellinKernel
import D5.S3.Observer.Hilbert.NymanBeurlingConeResidual
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import D5.S3.Weil.ZetaCore.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanHalflineZeroSeparation

open Set MeasureTheory
open D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
open D5.S3.Observer.Hilbert.NymanBeurlingConeResidual
open D5.S3.Observer.Hilbert.NymanHalflineMellinKernel
open D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

/-- The unit-interval target has the nonzero Mellin value. -/
theorem halflineFunctional_target (rho : ℂ) (hb : 1 / 2 < rho.re) (h1 : rho ≠ 1) :
    halflineFunctional rho hb h1 target = 1 / rho := by
  rw [(halflineFunctional_integral rho hb h1 target _ target_coe_ae.symm).2.2]
  have hl : (∫ x in Ioo (0 : ℝ) 1,
      (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x * (x : ℂ) ^ (rho - 1)) =
      ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (rho - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    simp [hx]
  have ht : (∫ x in Ioi (1 : ℝ),
      (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x / (x : ℂ)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hn : x ∉ Ioo (0 : ℝ) 1 := fun h => lt_asymm h.2 hx
    simp [hn]
  rw [hl, ht, mul_zero, sub_zero, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl (by simp; linarith))]
  have h0 : rho ≠ 0 := by intro h; simp [h] at hb; norm_num at hb
  simp [sub_add_cancel, Complex.zero_cpow h0]

private theorem source_tail_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ x in Ioi (1 : ℝ), ((Int.fract (1 / (a * x)) : ℝ) : ℂ) / (x : ℂ)) =
      (a : ℂ)⁻¹ := by
  have heq : (∫ x in Ioi (1 : ℝ), ((Int.fract (1 / (a * x)) : ℝ) : ℂ) / (x : ℂ)) =
      ∫ x in Ioi (1 : ℝ), (a : ℂ)⁻¹ * ((x ^ (-2 : ℝ) : ℝ) : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [realSourceVector_tail a ha hx,
      Real.rpow_neg (zero_lt_one.trans hx).le, Real.rpow_two]
    push_cast
    ring
  rw [heq, integral_const_mul, integral_complex_ofReal,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- Frozen E9 and the reciprocal tail cancel at every real source parameter. -/
theorem halflineFunctional_realSource (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (a : ℝ) (ha : 1 ≤ a) :
    halflineFunctional rho hb hz.not_trivial.2 (realSourceVector a ha) = 0 := by
  rw [(halflineFunctional_integral rho hb hz.not_trivial.2 _ _
    (realSourceVector_coe_ae a ha).symm).2.2, source_tail_integral a ha]
  have heq : (fun x : ℝ => ((Int.fract (1 / (a * x)) : ℝ) : ℂ) *
      (x : ℂ) ^ (rho - 1)) =
      fun x : ℝ => ((Int.fract ((1 / a) / x) : ℝ) : ℂ) * (x : ℂ) ^ (rho - 1) := by
    funext x
    rw [div_div]
  rw [heq, fractionalMellin_eq_zeta (1 / a) (by positivity)
    (by exact (div_le_one (by linarith : 0 < a)).mpr ha) rho hz.2.1 hz.2.2, hz.1]
  simp [div_eq_mul_inv, mul_comm]

/-- Every finite shell is annihilated, including the empty shell. -/
theorem halflineFunctional_shell (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (N : ℕ) (f : Carrier) (hf : f ∈ shell N) :
    halflineFunctional rho hb hz.not_trivial.2 f = 0 := by
  have hle : shell N ≤ (halflineFunctional rho hb hz.not_trivial.2).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change halflineFunctional rho hb hz.not_trivial.2 _ = 0
    dsimp only
    rw [← realSourceVector_nat (i.val + 1) (by omega)]
    exact halflineFunctional_realSource rho hz hb _ _
  exact hle hf

/-- Continuity extends annihilation to the original natural cumulative closed space. -/
theorem halflineFunctional_M (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (f : Carrier) (hf : f ∈ M) :
    halflineFunctional rho hb hz.not_trivial.2 f = 0 := by
  have hle : (M : Set Carrier) ⊆ (halflineFunctional rho hb hz.not_trivial.2).ker := by
    rw [cumulative_eq_closure_union]
    apply closure_minimal _ (ContinuousLinearMap.isClosed_ker _)
    rintro x ⟨s, ⟨N, rfl⟩, hx⟩
    exact halflineFunctional_shell rho hz hb N x hx
  exact hle hf

/-- The closure of the complex span of all real parameters, a separately defined space. -/
def fullRealClosure : Submodule ℂ Carrier :=
  (Submodule.span ℂ (Set.range (fun a : {a : ℝ // 1 ≤ a} =>
    realSourceVector a.val a.property))).topologicalClosure

/-- The same functional annihilates the closure of the full real source span. -/
theorem halflineFunctional_fullRealClosure (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (f : Carrier) (hf : f ∈ fullRealClosure) :
    halflineFunctional rho hb hz.not_trivial.2 f = 0 := by
  have hle : fullRealClosure ≤ (halflineFunctional rho hb hz.not_trivial.2).ker := by
    apply closure_minimal _ (ContinuousLinearMap.isClosed_ker _)
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact halflineFunctional_realSource rho hz hb a.val a.property
  exact hle hf

private theorem separation_bound (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (S : Submodule ℂ Carrier)
    (hS : ∀ f ∈ S, halflineFunctional rho hb hz.not_trivial.2 f = 0) :
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      Metric.infDist target (S : Set Carrier) ^ 2 := by
  let J := halflineFunctional rho hb hz.not_trivial.2
  have hn := halflineFunctional_norm_sq rho hb hz.not_trivial.2
  have hb0 : 0 < 2 * rho.re - 1 := by linarith only [hb]
  have he : 0 < 1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (one_div_pos.mpr hb0) (one_div_nonneg.mpr (sq_nonneg _))
  have hj : 0 < ‖J‖ := by
    change ‖J‖ ^ 2 = _ at hn
    exact lt_of_le_of_ne (norm_nonneg J) (Ne.symm (sq_pos_iff.mp (hn.symm ▸ he)))
  have hd : ‖J target‖ / ‖J‖ ≤ Metric.infDist target (S : Set Carrier) := by
    apply (Metric.le_infDist ⟨0, S.zero_mem⟩).mpr
    intro f hf
    apply (div_le_iff₀ hj).mpr
    have hh := J.le_opNorm (target - f)
    have hsf : J f = 0 := hS f hf
    rw [map_sub, hsf, sub_zero] at hh
    calc
      ‖J target‖ ≤ ‖J‖ * ‖target - f‖ := hh
      _ = dist target f * ‖J‖ := by rw [dist_eq_norm, mul_comm]
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    Metric.infDist_nonneg).mpr hd
  change (‖halflineFunctional rho hb hz.not_trivial.2 target‖ /
    ‖halflineFunctional rho hb hz.not_trivial.2‖) ^ 2 ≤ _ at hs
  rw [halflineFunctional_target, norm_div, norm_one, div_pow, div_pow, one_pow,
    div_div, halflineFunctional_norm_sq] at hs
  exact hs

/-- The literal lower bound for every original finite shell, with no conditioning premise. -/
theorem nyman_halfline_distance_bound (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) (N : ℕ) :
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤ distance N ^ 2 :=
  separation_bound rho hz hb (shell N) (halflineFunctional_shell rho hz hb N)

/-- The same bound holds for the original natural cumulative closed space. -/
theorem nyman_halfline_closed_distance_bound (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) :
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      Metric.infDist target (M : Set Carrier) ^ 2 :=
  separation_bound rho hz hb M (halflineFunctional_M rho hz hb)

/-- The same bound holds for the separately defined full-real-source closed span. -/
theorem nyman_halfline_real_closed_distance_bound (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) :
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      Metric.infDist target (fullRealClosure : Set Carrier) ^ 2 :=
  separation_bound rho hz hb fullRealClosure (halflineFunctional_fullRealClosure rho hz hb)

/-- The denominator bound equals the original radius expression, which is strictly positive. -/
theorem nyman_halfline_radius_chain (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) :
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) =
      (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 ∧
    (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 =
      ‖(1 : ℂ) - 1 / rho‖ ^ 2 * (1 - ‖(1 : ℂ) - 1 / rho‖ ^ 2) ∧
    0 < ‖(1 : ℂ) - 1 / rho‖ ^ 2 * (1 - ‖(1 : ℂ) - 1 / rho‖ ^ 2) := by
  have h0 : rho ≠ 0 := by intro h; simpa [h] using hz.2.1
  have hn : 0 < ‖rho‖ := norm_pos_iff.mpr h0
  have ht : 0 < ‖rho - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.not_trivial.2)
  have hd : 0 < 2 * rho.re - 1 := by linarith
  have he : ‖rho - 1‖ ^ 2 = ‖rho‖ ^ 2 - (2 * rho.re - 1) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq]
    simp
    ring
  have hr : ‖(1 : ℂ) - 1 / rho‖ ^ 2 = ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 2 := by
    rw [one_sub_div h0, norm_div, div_pow]
  have ha : 1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) =
      (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 := by
    have hsum : 1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2 =
        ‖rho‖ ^ 2 / ((2 * rho.re - 1) * ‖rho - 1‖ ^ 2) := by
      field_simp
      nlinarith [he]
    rw [hsum]
    field_simp
  have hb' : (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 =
      ‖(1 : ℂ) - 1 / rho‖ ^ 2 * (1 - ‖(1 : ℂ) - 1 / rho‖ ^ 2) := by
    rw [hr]
    field_simp
    nlinarith [he]
  refine ⟨ha, hb', ?_⟩
  rw [← hb']
  positivity

/-- E11 at the canonical nontrivial-zero predicate, conditional on a zero right of one half. -/
theorem nyman_halfline_e11 (rho : ℂ) (hz : Zeta23.IsNontrivialZero rho)
    (hb : 1 / 2 < rho.re) :
    (∀ N : ℕ, 1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      distance N ^ 2) ∧
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      Metric.infDist target (M : Set Carrier) ^ 2 ∧
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) ≤
      Metric.infDist target (fullRealClosure : Set Carrier) ^ 2 ∧
    1 / (‖rho‖ ^ 2 * (1 / (2 * rho.re - 1) + 1 / ‖rho - 1‖ ^ 2)) =
      (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 ∧
    (2 * rho.re - 1) * ‖rho - 1‖ ^ 2 / ‖rho‖ ^ 4 =
      ‖(1 : ℂ) - 1 / rho‖ ^ 2 * (1 - ‖(1 : ℂ) - 1 / rho‖ ^ 2) ∧
    0 < ‖(1 : ℂ) - 1 / rho‖ ^ 2 * (1 - ‖(1 : ℂ) - 1 / rho‖ ^ 2) :=
  ⟨nyman_halfline_distance_bound rho hz hb,
    nyman_halfline_closed_distance_bound rho hz hb,
    nyman_halfline_real_closed_distance_bound rho hz hb, nyman_halfline_radius_chain rho hz hb⟩

#print axioms halflineFunctional_target
#print axioms halflineFunctional_realSource
#print axioms halflineFunctional_shell
#print axioms halflineFunctional_M
#print axioms fullRealClosure
#print axioms halflineFunctional_fullRealClosure
#print axioms nyman_halfline_distance_bound
#print axioms nyman_halfline_closed_distance_bound
#print axioms nyman_halfline_real_closed_distance_bound
#print axioms nyman_halfline_radius_chain
#print axioms nyman_halfline_e11

end D5.S3.Observer.Hilbert.NymanHalflineZeroSeparation
