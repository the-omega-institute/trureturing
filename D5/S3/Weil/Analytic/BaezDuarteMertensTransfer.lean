/- GID: D5/S3/Weil/Analytic/BaezDuarteMertensTransfer
   generality: G
   mirror-B: D5/B/S3/Weil/Analytic/BaezDuarteMertensTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed unweighted Mertens power bounds imply original coefficient decay. -/
import D5.S3.Weil.Analytic.BaezDuarteMertensKernel
import D5.S3.Weil.ZetaBridge.RieszBaezDuarte
import Mathlib.NumberTheory.AbelSummation

open scoped Topology BigOperators Real
open Filter MeasureTheory Set Asymptotics
open D5.S3.Weil.RieszBaezDuarte
open D5.S3.Weil.Analytic.BaezDuarteMertensKernel

namespace D5.S3.Weil.Analytic.BaezDuarteMertensTransfer

local notation "M" => (fun x : ℝ => Finset.sum (Finset.Icc 1 (Nat.floor x))
  (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)))
local notation "kernel" => (fun k : ℕ => fun x : ℝ => x⁻¹^2*(1-x⁻¹^2)^k)

private theorem mertens_abs_le (x : ℝ) (hx : 0 ≤ x) : |M x| ≤ x := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

private theorem kernel_bounds (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ kernel k x ∧ kernel k x ≤ x⁻¹^2 := by
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : x⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hx
  have hq : x⁻¹^2 ≤ 1 := pow_le_one₀ hi hi1
  have hp := pow_le_one₀ (sub_nonneg.mpr hq) (by nlinarith [sq_nonneg x⁻¹] : 1-x⁻¹^2 ≤ 1) (n := k)
  exact ⟨mul_nonneg (sq_nonneg _) (pow_nonneg (sub_nonneg.mpr hq) _),
    mul_le_of_le_one_right (sq_nonneg _) hp⟩

private theorem kernel_deriv_bound (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    |deriv (kernel k) x| ≤ (2+2*(k : ℝ))*x⁻¹^3 := by
  rw [(baez_duarte_kernel_hasDerivAt k hk x hx).deriv]
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : x⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hx
  have hq : x⁻¹^2 ≤ 1 := pow_le_one₀ hi hi1
  have hbase : 0 ≤ 1-x⁻¹^2 := sub_nonneg.mpr hq
  have hp (n : ℕ) : (1-x⁻¹^2)^n ≤ 1 := pow_le_one₀ hbase (by nlinarith [sq_nonneg x⁻¹])
  have h5 : x⁻¹^5 ≤ x⁻¹^3 := by
    calc
      _ = x⁻¹^3*x⁻¹^2 := by ring
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hi _) hq
  calc
    _ ≤ |-2*x⁻¹^3*(1-x⁻¹^2)^k| + |2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1)| := abs_add_le _ _
    _ = 2*x⁻¹^3*(1-x⁻¹^2)^k + 2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (pow_nonneg hi _), abs_of_nonneg (pow_nonneg hbase _),
        abs_of_nonneg (by positivity)]
    _ ≤ 2*x⁻¹^3 + 2*(k : ℝ)*x⁻¹^5 := by
      exact add_le_add
        (mul_le_of_le_one_right (by positivity) (hp k))
        (mul_le_of_le_one_right (by positivity) (hp (k-1)))
    _ ≤ (2+2*(k : ℝ))*x⁻¹^3 := by nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2*k)]

private theorem zero_sum (n : ℕ) :
    ∑ i ∈ Finset.Icc 0 n, (ArithmeticFunction.moebius i : ℝ) =
      ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℝ) := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  norm_num

private theorem kernel_deriv_locallyIntegrable (k : ℕ) (hk : 1 ≤ k) :
    LocallyIntegrableOn (deriv (kernel k)) (Ici 1) := by
  have hc : ContinuousOn (fun x : ℝ => -2*x⁻¹^3*(1-x⁻¹^2)^k +
      2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1)) (Ici 1) := by
    fun_prop (disch := intro x hx; linarith [show 1 ≤ x from hx])
  apply (hc.congr ?_).locallyIntegrableOn measurableSet_Ici
  intro x hx
  exact (baez_duarte_kernel_hasDerivAt k hk x hx).deriv

private theorem kernel_boundary (k : ℕ) :
    Tendsto (fun n : ℕ => kernel k n * ∑ i ∈ Finset.Icc 0 n,
      (ArithmeticFunction.moebius i : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun n : ℕ => (n : ℝ)⁻¹)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hM : |∑ i ∈ Finset.Icc 0 n, (ArithmeticFunction.moebius i : ℝ)| ≤ n := by
      simpa [zero_sum] using mertens_abs_le (n : ℝ) (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_bounds k n hx).1]
    calc
      _ ≤ (n : ℝ)⁻¹^2 * n := mul_le_mul (kernel_bounds k n hx).2 hM (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem derivative_mertens_bigO (k : ℕ) (hk : 1 ≤ k) :
    (fun x : ℝ => deriv (kernel k) x * ∑ i ∈ Finset.Icc 0 ⌊x⌋₊,
      (ArithmeticFunction.moebius i : ℝ)) =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨2+2*(k : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_mul, zero_sum]
  have hM := mertens_abs_le x hx0.le
  have hd := kernel_deriv_bound k hk x hx
  calc
    _ ≤ ((2+2*(k : ℝ))*x⁻¹^3)*x := mul_le_mul hd hM (abs_nonneg _) (by positivity)
    _ = (2+2*(k : ℝ))*x⁻¹^2 := by field_simp
    _ = _ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
        Real.rpow_neg hx0.le, Real.rpow_two, inv_pow]

private theorem derivative_mertens_integrable (k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (fun x : ℝ => M x * deriv (kernel k) x) (Ioi 1) := by
  have hg : IntegrableAtFilter (fun x : ℝ => x ^ (-2 : ℝ)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)⟩
  have h := (locallyIntegrableOn_mul_sum_Icc
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)) zero_le_one
    (kernel_deriv_locallyIntegrable k hk)).integrableOn_of_isBigO_atTop
      (derivative_mertens_bigO k hk) hg
  rw [integrableOn_Ici_iff_integrableOn_Ioi] at h
  simpa only [zero_sum, mul_comm] using h

/-- Signed Abel summation retains the positive integer one and the negative sign. -/
theorem baez_duarte_abel_identity (k : ℕ) (hk : 1 ≤ k) :
    baezDuarte k = -(∫ x : ℝ in Ioi 1, M x * deriv (kernel k) x) := by
  have hg : IntegrableAtFilter (fun x : ℝ => x ^ (-2 : ℝ)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ))
    (f := kernel k) (by simp)
    (fun x hx => (baez_duarte_kernel_hasDerivAt k hk x hx).differentiableAt)
    (kernel_deriv_locallyIntegrable k hk) (kernel_boundary k)
    (derivative_mertens_bigO k hk) hg
  have hsum : HasSum (fun n : ℕ => kernel k n * (ArithmeticFunction.moebius n : ℝ))
      (baezDuarte k) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [div_eq_mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc] using
      baez_duarte_hasSum_moebius k
  have ht : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 0 n,
      kernel k i * (ArithmeticFunction.moebius i : ℝ)) atTop (𝓝 (baezDuarte k)) := by
    simpa only [Function.comp_def, Nat.range_succ_eq_Icc_zero] using
      hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [zero_sub, zero_sum, mul_comm] using tendsto_nhds_unique ht hAbel

private theorem weighted_derivative_bound (a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) (hx : 1 ≤ x) :
    x^a * |deriv (kernel k) x| ≤
      2 * (x^(a-3)*(1-x⁻¹^2)^k) + 2*(k : ℝ)*(x^(a-5)*(1-x⁻¹^2)^(k-1)) := by
  have hx0 : 0 < x := by linarith
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hq : x⁻¹^2 ≤ 1 := pow_le_one₀ hi ((inv_le_one₀ hx0).mpr hx)
  have hp : 0 ≤ 1-x⁻¹^2 := sub_nonneg.mpr hq
  have hder : |deriv (kernel k) x| ≤
      2*x⁻¹^3*(1-x⁻¹^2)^k + 2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1) := by
    rw [(baez_duarte_kernel_hasDerivAt k hk x hx).deriv]
    calc
      _ ≤ |-2*x⁻¹^3*(1-x⁻¹^2)^k| + |2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1)| := abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (pow_nonneg hi _), abs_of_nonneg (pow_nonneg hp _),
          abs_of_nonneg (by positivity)]
  have hpower (n : ℕ) : x^a * x⁻¹^n = x^(a-(n : ℝ)) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    congr 1
  calc
    _ ≤ x^a * (2*x⁻¹^3*(1-x⁻¹^2)^k + 2*(k : ℝ)*x⁻¹^5*(1-x⁻¹^2)^(k-1)) :=
      mul_le_mul_of_nonneg_left hder (Real.rpow_nonneg hx0.le _)
    _ = 2*(x^a*x⁻¹^3)*(1-x⁻¹^2)^k + 2*(k : ℝ)*(x^a*x⁻¹^5)*(1-x⁻¹^2)^(k-1) := by ring
    _ = _ := by rw [hpower 3, hpower 5]; norm_num; ring

/-- The original signed unweighted Mertens bound gives the full transfer range. -/
theorem baez_duarte_decay_of_mertens_bound (a : ℝ) (_ha : 0 ≤ a) (ha2 : a < 2)
    (hM : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → |M x| ≤ A * Real.rpow x a) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      |baezDuarte k| ≤ C * Real.rpow (k : ℝ) (a/2-1) := by
  obtain ⟨A, hA, hM⟩ := hM
  let b : ℝ := 1-a/2
  have hb : 0 < b := by dsimp [b]; linarith
  obtain ⟨C, hC, hCbound⟩ := baez_duarte_beta_combined_bound b hb
  refine ⟨A*C, mul_pos hA hC, fun k hk => ?_⟩
  let g₁ : ℝ → ℝ := fun x => Real.rpow x (-2*b-1)*(1-x⁻¹^2)^k
  let g₂ : ℝ → ℝ := fun x => Real.rpow x (-2*(b+1)-1)*(1-x⁻¹^2)^(k-1)
  have hg₁ : IntegrableOn g₁ (Ioi 1) := baez_duarte_kernel_integrable b hb k
  have hg₂ : IntegrableOn g₂ (Ioi 1) := baez_duarte_kernel_integrable (b+1) (by linarith) (k-1)
  have hpoint (x : ℝ) (hx : x ∈ Ioi 1) :
      |M x * deriv (kernel k) x| ≤ A * (2*g₁ x + 2*(k : ℝ)*g₂ x) := by
    rw [abs_mul]
    calc
      _ ≤ A*Real.rpow x a*|deriv (kernel k) x| :=
        mul_le_mul_of_nonneg_right (hM x hx.le) (abs_nonneg _)
      _ ≤ A*(2*g₁ x + 2*(k : ℝ)*g₂ x) := by
        have h := mul_le_mul_of_nonneg_left (weighted_derivative_bound a k hk x hx.le) hA.le
        have he₁ : a-3 = -2*b-1 := by dsimp [b]; ring
        have he₂ : a-5 = -2*(b+1)-1 := by dsimp [b]; ring
        simpa only [mul_assoc, he₁, he₂, g₁, g₂, Real.rpow_eq_pow] using h
  have he₂ : (((k-1 : ℕ) : ℂ)+1) = (k : ℂ) := by
    exact_mod_cast Nat.sub_add_cancel hk
  have hInt : (∫ x : ℝ in Ioi 1, A*(2*g₁ x + 2*(k : ℝ)*g₂ x)) =
      A*((Complex.betaIntegral (b : ℂ) ((k : ℂ)+1)).re +
        (k : ℝ)*(Complex.betaIntegral ((b : ℂ)+1) (k : ℂ)).re) := by
    rw [integral_const_mul, integral_add (hg₁.const_mul 2) (hg₂.const_mul (2*(k : ℝ))),
      integral_const_mul, integral_const_mul]
    dsimp only [g₁, g₂]
    rw [baez_duarte_kernel_integral b hb k,
      baez_duarte_kernel_integral (b+1) (by linarith) (k-1), he₂, Complex.ofReal_add,
      Complex.ofReal_one]
    ring
  rw [baez_duarte_abel_identity k hk, abs_neg]
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, |M x * deriv (kernel k) x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ in Ioi 1, A*(2*g₁ x + 2*(k : ℝ)*g₂ x) :=
      integral_mono_ae (derivative_mertens_integrable k hk).abs
        (((hg₁.const_mul 2).add (hg₂.const_mul (2*(k : ℝ)))).const_mul A)
        (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
    _ ≤ A*C * Real.rpow (k : ℝ) (a/2-1) := by
      rw [hInt]
      have h := mul_le_mul_of_nonneg_left (hCbound k hk) hA.le
      have hb' : -b = a/2-1 := by dsimp [b]; ring
      simpa only [hb', mul_assoc] using h

/-- An eventual Mertens estimate absorbs the genuine finite prefix, including one. -/
theorem baez_duarte_decay_of_eventual_mertens_bound (a : ℝ) (ha : 0 ≤ a) (ha2 : a < 2)
    (hM : ∃ A : ℝ, 0 < A ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |M x| ≤ A * Real.rpow x a) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      |baezDuarte k| ≤ C * Real.rpow (k : ℝ) (a/2-1) := by
  obtain ⟨A, hA, X, hM⟩ := hM
  apply baez_duarte_decay_of_mertens_bound a ha ha2
  refine ⟨max A (max 1 X), lt_of_lt_of_le hA (le_max_left _ _), fun x hx => ?_⟩
  by_cases hX : X ≤ x
  · exact (hM x hX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _))
  · have hxp : 1 ≤ Real.rpow x a := by simpa only [Real.rpow_eq_pow] using Real.one_le_rpow hx ha
    calc
      _ ≤ x := mertens_abs_le x (by linarith)
      _ ≤ max A (max 1 X) := (le_of_lt (lt_of_not_ge hX)).trans
        ((le_max_right 1 X).trans (le_max_right A _))
      _ ≤ max A (max 1 X) * Real.rpow x a := le_mul_of_one_le_right
        (le_trans hA.le (le_max_left _ _)) hxp

end D5.S3.Weil.Analytic.BaezDuarteMertensTransfer
