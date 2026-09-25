/- GID: D5/S3/Fourier/Asymptotics/CosineIntegralLattice
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineIntegralLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The squared real cosine-integral tail has a uniform bound on every positive lattice. -/

import Mathlib.Fourier.Asymptotics.ImproperIntegrals
import Mathlib.Fourier.Asymptotics.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

open MeasureTheory Set Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.Asymptotics.CosineIntegralLattice

/-- The real cosine-integral tail on the positive half-line, after integration by parts:
`Ci(x) = -lim_{R → ∞} ∫ t in x..R, cos(t)/t`.
The integral in this definition is absolutely convergent for `x > 0`. -/
noncomputable def cosineIntegral (x : ℝ) : ℝ :=
  Real.sin x / x - ∫ t in Ioi x, Real.sin t / t ^ 2

/-- A single square-sum bound for every positive lattice spacing. -/
theorem result : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    Summable (fun n : ℕ => cosineIntegral (z * (n + 1)) ^ 2) ∧
      z * (∑' n : ℕ, cosineIntegral (z * (n + 1)) ^ 2) ≤ C := by
  have hsinpow : ∀ x : ℝ, 0 < x → |Real.sin x| ≤ x ^ (3 / 4 : ℝ) := by
    intro x hx
    by_cases h1 : x ≤ 1
    · calc
        |Real.sin x| ≤ x := by simpa [abs_of_pos hx] using Real.abs_sin_le_abs (x := x)
        _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h1 (by norm_num)
    · calc
        |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
        _ = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
        _ ≤ x ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h1) (by norm_num)
  have hdivpow : ∀ x : ℝ, 0 < x →
      x ^ (3 / 4 : ℝ) / x ^ 2 = x ^ (-5 / 4 : ℝ) := by
    intro x hx
    rw [show (-5 / 4 : ℝ) = 3 / 4 - 2 by norm_num, Real.rpow_sub hx, Real.rpow_two]
  have htailmajor : ∀ x : ℝ, 0 < x →
      ‖Real.sin x / x ^ 2‖ ≤ x ^ (-2 : ℝ) := by
    intro x hx
    rw [norm_div, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_of_pos hx,
      show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_two]
    simpa [one_div] using div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (sq_nonneg x)
  have htailint : ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi x) := by
    intro x hx
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).mono' ?_ ?_
    · exact (Real.measurable_sin.div (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htailmajor t (hx.trans ht)
  have hsmall : ∀ x : ℝ, 0 < x → |cosineIntegral x| ≤ 5 * x ^ (-1 / 4 : ℝ) := by
    intro x hx
    have hfirst : |Real.sin x / x| ≤ x ^ (-1 / 4 : ℝ) := by
      rw [abs_div, abs_of_pos hx]
      calc
        |Real.sin x| / x ≤ x ^ (3 / 4 : ℝ) / x := div_le_div_of_nonneg_right (hsinpow x hx) hx.le
        _ = x ^ (-1 / 4 : ℝ) := by
          rw [show (-1 / 4 : ℝ) = 3 / 4 - 1 by norm_num, Real.rpow_sub hx, Real.rpow_one]
    have htail : |∫ t in Ioi x, Real.sin t / t ^ 2| ≤ 4 * x ^ (-1 / 4 : ℝ) := by
      have h := (norm_integral_le_integral_norm (fun t : ℝ => Real.sin t / t ^ 2)
        (μ := volume.restrict (Ioi x))).trans (integral_mono_ae (htailint x hx).norm
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) hx) ?_)
      · rw [integral_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) hx] at h
        norm_num at h
        simpa [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using h
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 := hx.trans ht
        rw [norm_div, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_of_pos ht0]
        exact (div_le_div_of_nonneg_right (hsinpow t ht0) (sq_nonneg t)).trans_eq (hdivpow t ht0)
    exact (abs_sub _ _).trans (by dsimp [cosineIntegral] at *; linarith)
  have hlarge : ∀ x : ℝ, 0 < x → |cosineIntegral x| ≤ 2 / x := by
    intro x hx
    have hfirst : |Real.sin x / x| ≤ 1 / x := by
      rw [abs_div, abs_of_pos hx]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hx.le
    have htail : |∫ t in Ioi x, Real.sin t / t ^ 2| ≤ 1 / x := by
      have h := (norm_integral_le_integral_norm (fun t : ℝ => Real.sin t / t ^ 2)
        (μ := volume.restrict (Ioi x))).trans (integral_mono_ae (htailint x hx).norm
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx) ?_)
      · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx] at h
        norm_num [Real.rpow_neg_one, Real.norm_eq_abs] at h
        simpa [one_div] using h
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact htailmajor t (hx.trans ht)
    change |Real.sin x / x - ∫ t in Ioi x, Real.sin t / t ^ 2| ≤ _
    exact (abs_sub _ _).trans (by
      simp only [div_eq_mul_inv] at hfirst htail ⊢
      linarith)
  let E : ℝ → ℝ := fun x => if x ≤ 1 then 25 * x ^ (-1 / 2 : ℝ) else 25 * x ^ (-2 : ℝ)
  have hEpos : ∀ x : ℝ, 0 < x → 0 ≤ E x := by
    intro x hx
    dsimp [E]
    split_ifs <;> positivity
  have hmajor : ∀ x : ℝ, 0 < x → cosineIntegral x ^ 2 ≤ E x := by
    intro x hx
    dsimp [E]
    split_ifs with h1
    · have h := pow_le_pow_left₀ (abs_nonneg (cosineIntegral x)) (hsmall x hx) 2
      rw [sq_abs, mul_pow] at h
      have hp : (x ^ (-1 / 4 : ℝ)) ^ 2 = x ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        norm_num
      rw [hp] at h
      norm_num at h ⊢
      exact h
    · have h := pow_le_pow_left₀ (abs_nonneg (cosineIntegral x)) (hlarge x hx) 2
      rw [sq_abs, div_pow] at h
      have hp : x ^ (-2 : ℝ) = 1 / x ^ 2 := by rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]
      rw [hp]
      norm_num [div_eq_mul_inv] at h ⊢
      nlinarith [inv_nonneg.mpr (sq_nonneg x)]

  have hanti : AntitoneOn E (Ioi 0) := by
    intro x hx y hy hxy
    dsimp [E]
    split_ifs with hy1 hx1 hx1
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num : (-1 / 2 : ℝ) ≤ 0)) (by norm_num)
    · exact (hx1 (hxy.trans hy1)).elim
    · have hleft : (1 : ℝ) ≤ x ^ (-1 / 2 : ℝ) := by
        calc
          1 = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
      have hright : y ^ (-2 : ℝ) ≤ 1 := by
        calc
          _ ≤ y ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy1) (by norm_num)
          _ = 1 := Real.rpow_zero y
      linarith
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num : (-2 : ℝ) ≤ 0)) (by norm_num)
  have hEint : IntegrableOn E (Ioi 0) := by
    have h0 : IntegrableOn E (Ioc 0 1) := by
      have hp : IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by norm_num)
      refine IntegrableOn.congr_fun (hp.const_mul 25) ?_ measurableSet_Ioc
      intro x hx
      simp [E, hx.2]
    have h1 : IntegrableOn E (Ioi 1) := by
      refine IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul 25) ?_ measurableSet_Ioi
      intro x hx
      simp [E, not_le.mpr (show 1 < x from hx)]
    convert h0.union h1 using 1
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · intro h
      by_cases hx : x ≤ 1
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
    · rintro (h | h) <;> linarith
  have hmass : ∀ x : ℝ, 0 < x → x * E x ≤ 25 := by
    intro x hx
    dsimp [E]
    split_ifs with hx1
    · have he : x * x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx]
        norm_num
      have hr : x ^ (1 / 2 : ℝ) ≤ 1 := by
        calc
          _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
          _ = 1 := Real.rpow_zero x
      calc
        x * (25 * x ^ (-1 / 2 : ℝ)) = 25 * x ^ (1 / 2 : ℝ) := by nlinarith [he]
        _ ≤ 25 := by linarith
    · have he : x * x ^ (-2 : ℝ) = x ^ (-1 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx]
        norm_num
      have hr : x ^ (-1 : ℝ) ≤ 1 := by
        calc
          _ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (by norm_num)
          _ = 1 := Real.rpow_zero x
      calc
        x * (25 * x ^ (-2 : ℝ)) = 25 * x ^ (-1 : ℝ) := by nlinarith [he]
        _ ≤ 25 := by linarith
  have hIpos : 0 ≤ ∫ x in Ioi (0 : ℝ), E x :=
    setIntegral_nonneg measurableSet_Ioi hEpos
  refine ⟨26 + ∫ x in Ioi (0 : ℝ), E x, by linarith, ?_⟩
  intro z hz
  let F : ℝ → ℝ := fun t => E (z * t)
  have hFanti : AntitoneOn F (Ici 1) := by
    intro x hx y hy hxy
    exact hanti (by change 0 < z * x; have : 1 ≤ x := hx; nlinarith) (by change 0 < z * y; have : 1 ≤ y := hy; nlinarith) (mul_le_mul_of_nonneg_left hxy hz.le)
  have hFint : IntegrableOn F (Ioi 1) := by
    apply (integrableOn_Ioi_comp_mul_left_iff E 1 hz).mpr
    simpa using hEint.mono_set (Ioi_subset_Ioi hz.le)
  have hFpos : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ F t := by
    intro t ht
    exact hEpos _ (mul_pos hz (lt_trans zero_lt_one ht))
  have hFsummable : Summable (fun n : ℕ => F n) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 1) (by simpa using hFanti) (by simpa using hFint) (by simpa using hFpos)
  have hFsum : Summable (fun n : ℕ => F (n + 1 : ℕ)) :=
    (summable_nat_add_iff 1).mpr hFsummable
  have hCsum : Summable (fun n : ℕ => cosineIntegral (z * (n + 1)) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ hFsum
    intro n
    simpa [F, Nat.cast_add, Nat.cast_one] using hmajor (z * (n + 1)) (by positivity)
  refine ⟨hCsum, ?_⟩
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (f := F) (by simpa using hFanti) (by simpa using hFint) (by simpa using hFpos)
  have hcompare : (∑' n : ℕ, cosineIntegral (z * (n + 1)) ^ 2) ≤
      ∑' n : ℕ, F (n + 1 : ℕ) := by
    apply hCsum.tsum_le_tsum ?_ hFsum
    intro n
    simpa [F, Nat.cast_add, Nat.cast_one] using hmajor (z * (n + 1)) (by positivity)
  have hsum : (∑' n : ℕ, F (n + 1 : ℕ)) ≤ E z + ∫ x in Ioi (1 : ℝ), F x := by
    rw [hFsum.tsum_eq_zero_add]
    simpa [F, Nat.cast_add, Nat.cast_one, add_assoc] using add_le_add_left htail (E z)
  have hchange : z * (∫ t in Ioi (1 : ℝ), F t) = ∫ x in Ioi z, E x := by
    simpa [F, smul_eq_mul] using integral_comp_mul_left_Ioi' E 1 hz
  have hsubset : (∫ x in Ioi z, E x) ≤ ∫ x in Ioi (0 : ℝ), E x := by
    apply setIntegral_mono_set hEint
    · exact ae_restrict_of_forall_mem measurableSet_Ioi hEpos
    · exact (Ioi_subset_Ioi hz.le).eventuallyLE
  calc
    z * (∑' n : ℕ, cosineIntegral (z * (n + 1)) ^ 2) ≤
        z * (E z + ∫ x in Ioi (1 : ℝ), F x) :=
      mul_le_mul_of_nonneg_left (hcompare.trans hsum) hz.le
    _ = z * E z + ∫ x in Ioi z, E x := by rw [mul_add, hchange]
    _ ≤ 26 + ∫ x in Ioi (0 : ℝ), E x := by linarith [hmass z hz]

end D5.S3.Fourier.Asymptotics.CosineIntegralLattice
