/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentLiteralV
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentLiteralV
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consuming literal-V continuum and cutoff obstruction. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentFiniteAtom

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

private lemma literal_continuum_identity (h L D : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (hD : L + h ≤ D) (F : ℝ → ℝ) (hc : Continuous F)
    (he : ∀ t, F (-t) = F t) (hs : ∀ t, h ≤ |t| → F t = 0) :
    (2 * ∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))) =
    4 * ∫ t in (0 : ℝ)..h,
      (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t := by
  let J : ℝ → ℝ := fun t => Real.exp (t / 2) * F t
  have hJ : Continuous J := (by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).mul hc
  have hD0 : 0 ≤ D := by linarith
  have hcut : (∫ t in (0 : ℝ)..D, J t) = ∫ t in (0 : ℝ)..h, J t := by
    have hz : (∫ t in h..D, J t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      have ht := uIoc_subset_uIcc ht
      rw [uIcc_of_le (by linarith : h ≤ D)] at ht
      dsimp [J]
      rw [hs t (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1), mul_zero]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable 0 h) (hJ.intervalIntegrable h D)
    linarith only [hadj, hz]
  have hplus : (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t + L)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le hD0] at ht
    rw [hs (t + L) (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1]), mul_zero]
  have hleft : (∫ t in (-L)..(-h), J t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le (by linarith : -L ≤ -h)] at ht
    dsimp [J]
    rw [hs t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]), mul_zero]
  have hright : (∫ t in h..(D - L), J t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht := uIoc_subset_uIcc ht
    rw [uIcc_of_le (by linarith : h ≤ D - L)] at ht
    dsimp [J]
    rw [hs t (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1), mul_zero]
  have hwindow : (∫ t in (-L)..(D - L), J t) = ∫ t in (-h)..h, J t := by
    have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable (-L) (-h)) (hJ.intervalIntegrable (-h) (D - L))
    have hb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hJ.intervalIntegrable (-h) h) (hJ.intervalIntegrable h (D - L))
    linarith only [ha, hb, hleft, hright]
  have hminus : (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t - L)) =
      Real.exp (L / 2) * ∫ t in (-h)..h, J t := by
    have heq (t : ℝ) : Real.exp (t / 2) * F (t - L) = Real.exp (L / 2) * J (t - L) := by
      dsimp [J]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right,
      zero_sub, hwindow]
  have hreflect : (∫ t in (-h)..0, J t) =
      ∫ t in (0 : ℝ)..h, Real.exp (-t / 2) * F t := by
    have ht := intervalIntegral.integral_comp_neg
      (f := J) (a := (0 : ℝ)) (b := h)
    simp only [neg_zero] at ht
    have heq : (fun t => J (-t)) = fun t => Real.exp (-t / 2) * F t := by
      ext t
      simp only [J, he]
    rw [heq] at ht
    exact ht.symm
  have heven : (∫ t in (-h)..h, J t) =
      ∫ t in (0 : ℝ)..h, (Real.exp (t / 2) + Real.exp (-t / 2)) * F t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hJ.intervalIntegrable (-h) 0) (hJ.intervalIntegrable 0 h), hreflect]
    have hnint : IntervalIntegrable (fun t : ℝ => Real.exp (-t / 2) * F t) volume 0 h :=
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2) * F t)).intervalIntegrable 0 h
    rw [← intervalIntegral.integral_add hnint (hJ.intervalIntegrable 0 h)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [J]
    ring
  have hsplit : (∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))) =
      2 * (∫ t in (0 : ℝ)..D, J t) -
      (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t + L)) -
      (∫ t in (0 : ℝ)..D, Real.exp (t / 2) * F (t - L)) := by
    have heq (t : ℝ) : Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L)) =
        2 * J t - Real.exp (t / 2) * F (t + L) - Real.exp (t / 2) * F (t - L) := by
      dsimp [J]; ring
    simp_rw [heq]
    have hp : Continuous (fun t : ℝ => Real.exp (t / 2) * F (t + L)) := by fun_prop
    have hm : Continuous (fun t : ℝ => Real.exp (t / 2) * F (t - L)) := by fun_prop
    have h2J : Continuous (fun t => 2 * J t) := hJ.const_mul 2
    have hfirst : IntervalIntegrable
        (fun t => 2 * J t - Real.exp (t / 2) * F (t + L)) volume 0 D :=
      (h2J.sub hp).intervalIntegrable 0 D
    rw [intervalIntegral.integral_sub (μ := volume) hfirst (hm.intervalIntegrable 0 D),
      intervalIntegral.integral_sub (μ := volume) (h2J.intervalIntegrable 0 D)
        (hp.intervalIntegrable 0 D), intervalIntegral.integral_const_mul]
  have hbracket : (∫ t in (0 : ℝ)..h,
      (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t) =
      (∫ t in (0 : ℝ)..h, J t) - Real.exp (L / 2) / 2 *
        (∫ t in (0 : ℝ)..h, (Real.exp (t / 2) + Real.exp (-t / 2)) * F t) := by
    have heq (t : ℝ) : (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t =
        J t - Real.exp (L / 2) / 2 * ((Real.exp (t / 2) + Real.exp (-t / 2)) * F t) := by
      dsimp [J]; ring
    simp_rw [heq]
    have hbcont : Continuous (fun t : ℝ => Real.exp (L / 2) / 2 *
        ((Real.exp (t / 2) + Real.exp (-t / 2)) * F t)) := by fun_prop
    rw [intervalIntegral.integral_sub (μ := volume)
      (hJ.intervalIntegrable 0 h) (hbcont.intervalIntegrable 0 h),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hcut, hplus, hminus, heven, hbracket]
  ring


private lemma literal_continuum_bound (h L D B : ℝ) (hh : 0 ≤ h) (hL : h ≤ L)
    (hD : L + h ≤ D) (hB : 0 ≤ B) (F : ℝ → ℝ) (hc : Continuous F)
    (he : ∀ t, F (-t) = F t) (hs : ∀ t, h ≤ |t| → F t = 0)
    (hb : ∀ t, |F t| ≤ B) :
    |2 * ∫ t in (0 : ℝ)..D,
      Real.exp (t / 2) * (2 * F t - F (t + L) - F (t - L))| ≤
      4 * h * Real.exp ((L + h) / 2) * B := by
  rw [literal_continuum_identity h L D hh hL hD F hc he hs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := h) (C := Real.exp ((L + h) / 2) * B)
    (f := fun t => (Real.exp (t / 2) - Real.exp (L / 2) *
        (Real.exp (t / 2) + Real.exp (-t / 2)) / 2) * F t) (fun t ht => by
      rw [uIoc_of_le hh] at ht
      have hA : Real.exp (t / 2) ≤ Real.exp ((L + h) / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      have h₁ : Real.exp (L / 2) * Real.exp (t / 2) ≤ Real.exp ((L + h) / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [ht.2])
      have h₂ : Real.exp (L / 2) * Real.exp (-t / 2) ≤ Real.exp ((L + h) / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [ht.1])
      have hB' : 0 ≤ Real.exp (L / 2) * (Real.exp (t / 2) + Real.exp (-t / 2)) / 2 := by positivity
      have hd : |Real.exp (t / 2) - Real.exp (L / 2) *
          (Real.exp (t / 2) + Real.exp (-t / 2)) / 2| ≤ Real.exp ((L + h) / 2) := by
        apply abs_le.mpr
        constructor <;> nlinarith [Real.exp_pos (t / 2)]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hd (hb t) (abs_nonneg _) (Real.exp_pos _).le)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at hn
  nlinarith only [hn]

private lemma literal_numeric_margin :
    (1 / 2 : ℝ) < Real.sqrt 2 * Real.log 2 -
      4 * (1 / 16) * Real.exp ((Real.log 2 + 1 / 16) / 2) := by
  have hs : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have he : Real.exp (1 / 32 : ℝ) ≤ 32 / 31 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [show (Real.log 2 + 1 / 16) / 2 = Real.log 2 / 2 + 1 / 32 by ring,
    Real.exp_add, hsqrt]
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hfactor : (1 / 2 : ℝ) < Real.sqrt 2 * (Real.log 2 - Real.exp (1 / 32) / 4) := by
    have hpos : (0 : ℝ) < Real.log 2 - Real.exp (1 / 32) / 4 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hs) hpos]
  nlinarith only [hfactor]

private lemma literal_ratio_constant (q : ℕ) (hq : 1 ≤ q) (N Eg Wg Vv E : ℝ)
    (hN : 0 < N) (hEg : 0 < Eg) (hEg' : Eg ≤ literalStep q)
    (hW : Real.exp (-literalStep q / 4) ^ 2 * literalStep q ^ 3 / 48 ≤ Wg)
    (hV : Vv ≤ -(N * Wg) / 2) (hE : E = 2 * N * Eg) :
    0 < E ∧ Vv / E ≤ -1 / (65536 * (q : ℝ) ^ 2) := by
  have hl := literal_step_bounds q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hr : (3 / 4 : ℝ) ≤ Real.exp (-literalStep q / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    have ha := Real.add_one_le_exp (-literalStep q / 2)
    rw [show -literalStep q / 4 + -literalStep q / 4 = -literalStep q / 2 by ring]
    linarith [hl.2.1]
  have hw : literalStep q ^ 2 * Eg / 64 ≤ Wg := by
    have hp := mul_nonneg (sub_nonneg.mpr hr) (pow_nonneg hl.1.le 3)
    have hp' := mul_nonneg (sub_nonneg.mpr hEg') (sq_nonneg (literalStep q))
    nlinarith only [hW, hp, hp']
  have hE0 : 0 < E := by rw [hE]; positivity
  have hvE : Vv ≤ -(literalStep q ^ 2 / 256) * E := by
    calc
      Vv ≤ -(N / 2) * Wg := by linarith only [hV]
      _ ≤ -(N / 2) * (literalStep q ^ 2 * Eg / 64) :=
        mul_le_mul_of_nonpos_left hw (by linarith)
      _ = _ := by rw [hE]; ring
  have hel : literalStep q ^ 2 / 256 = 1 / (65536 * (q : ℝ) ^ 2) := by
    dsimp [literalStep]
    field_simp
    <;> ring
  refine ⟨hE0, (div_le_iff₀ hE0).mpr ?_⟩
  rw [hel] at hvE
  simpa only [neg_div, one_mul] using hvE


private lemma literal_V_upper (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) :
    V D (literalNodes q) (literalCoeffs q) ≤
      -(literalN q * W D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))) / 2 := by
  let F : ℝ → ℝ := S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ))
  let B := W D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ))
  have hL : 1 / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hD0 : 0 ≤ D := by linarith
  have hDh : 1 / 16 ≤ D := by linarith
  have hx := literal_support_D q hq D hD
  have hxe : ∀ i, literalEtaNodes q i ∈ Icc (0 : ℝ) D := fun i =>
    ⟨(literal_eta_support q hq i).1, (literal_eta_support q hq i).2.trans hDh⟩
  have hFcont : Continuous F := by
    have heq : F = fun t => -literalPair (literalEtaNodes q) (literalEtaCoeffs q)
        (fun s => max s 0 + Real.exp (-|s| / 2)) t :=
      funext (literal_S_pair D hD0 _ _ hxe (literal_eta_mass q))
    rw [heq]
    dsimp [literalPair]
    fun_prop
  have hFeven (t : ℝ) : F (-t) = F t := S_even D hD0 _ _ (literal_eta_mass q) t
  have hFtail (t : ℝ) (ht : 1 / 16 ≤ |t|) : F t = 0 :=
    literal_S_tail D (1 / 16) hD0 _ _ hxe (literal_eta_support q hq)
      (literal_eta_mass q) (literal_eta_exp q) t ht
  have hFbound (t : ℝ) : |F t| ≤ B := S_abs_le_W D hD0 _ _ hxe (literal_eta_mass q) t
  have hB : 0 ≤ B := W_nonneg D hD0 _ _ hxe (literal_eta_mass q)
  have htwo (t : ℝ) : S D (literalNodes q) (literalCoeffs q) t =
      2 * F t - F (t + Real.log 2) - F (t - Real.log 2) := literal_two_S q hq D hD t
  have htail (t : ℝ) (ht : Real.log 2 + 1 / 16 ≤ t) :
      S D (literalNodes q) (literalCoeffs q) t = 0 := by
    rw [htwo, hFtail t (by rw [abs_of_nonneg (by linarith)]; linarith),
      hFtail (t + Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith),
      hFtail (t - Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith)]
    ring
  have hSL : S D (literalNodes q) (literalCoeffs q) (Real.log 2) = -B := by
    rw [htwo, hFtail (Real.log 2) (by rwa [abs_of_nonneg (by linarith)]),
      hFtail (Real.log 2 + Real.log 2) (by rw [abs_of_nonneg (by linarith)]; linarith), sub_self]
    change 2 * 0 - 0 - B = -B
    ring
  have hZ : Z D (literalNodes q) (literalCoeffs q) = 0 := by
    rw [Z, htail D hD, mul_zero]
  have hExpD0 : Real.exp (Real.log 2 + 1 / 16) < 3 := by
    have he := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num at he
    linarith
  have hlog3 : Real.log 2 + 1 / 16 < Real.log 3 := by
    apply Real.exp_lt_exp.mp
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have h2 : 2 ∈ primes D := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl, (log_cut_iff 2 (by norm_num) D).mp ?_⟩
    norm_num only [Nat.cast_ofNat]
    linarith
  have hsqrt : 2 / Real.sqrt (2 : ℝ) = Real.sqrt 2 := by
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have harith : 2 * (∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      S D (literalNodes q) (literalCoeffs q) (Real.log n)) =
      -Real.sqrt 2 * Real.log 2 * B := by
    rw [Finset.sum_eq_single 2]
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num only [Nat.cast_ofNat]
      rw [hSL]
      calc
        _ = -(2 / Real.sqrt (2 : ℝ)) * Real.log 2 * B := by ring
        _ = _ := by rw [hsqrt]
    · intro n hn hn2
      have hn3 : 3 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      have hlogn : Real.log 3 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      rw [htail _ (by linarith), mul_zero]
    · exact fun hn => (hn h2).elim
  have hC : |2 * ∫ t in Icc (0 : ℝ) D,
      Real.exp (t / 2) * S D (literalNodes q) (literalCoeffs q) t| ≤
      4 * (1 / 16) * Real.exp ((Real.log 2 + 1 / 16) / 2) * B := by
    have h := literal_continuum_bound (1 / 16) (Real.log 2) D B (by norm_num)
      hL hD hB F hFcont hFeven hFtail hFbound
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD0]
    simpa only [htwo] using h
  have hV : V D (literalNodes q) (literalCoeffs q) =
      -Real.sqrt 2 * Real.log 2 * B -
        2 * ∫ t in Icc (0 : ℝ) D,
          Real.exp (t / 2) * S D (literalNodes q) (literalCoeffs q) t := by
    rw [V, harith, hZ, mul_zero, sub_zero]
  have hv : V D (literalNodes q) (literalCoeffs q) ≤ -B / 2 := by
    have hmargin := mul_nonneg (sub_nonneg.mpr literal_numeric_margin.le) hB
    rw [hV]
    have hc := (abs_le.mp hC).1
    nlinarith only [hmargin, hc]
  simpa only [B, literal_eta_W q hq D hDh] using hv

/-- The explicit six-q atom family retains the inclusive literal Mangoldt V,
vanishes through exactly the requested polynomial order and at the positive
exponential moment, and has a strictly negative energy-normalized value. -/
theorem literal_V_energy_moment_obstruction (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) :
    ∃ (x : Fin q × Fin 3 × Bool → ℝ) (a : Fin q × Fin 3 × Bool → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) (1 / 16) ∪ Icc (Real.log 2) (Real.log 2 + 1 / 16)) ∧
      (∀ i, x i ∈ Icc (0 : ℝ) D) ∧
      (∀ m : ℕ, m ≤ q → ∑ i, a i * (x i : ℂ) ^ m = 0) ∧
      (∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0) ∧
      (∑ i, a i * (x i : ℂ) ^ (q + 1)) ≠ 0 ∧
      (∑ i, a i * (x i : ℂ) * (Real.exp (x i / 2) : ℂ)) ≠ 0 ∧
      0 < energy x a ∧ V D x a / energy x a ≤ -1 / (65536 * (q : ℝ) ^ 2) := by
  have hl := literal_step_bounds q hq
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 < 1 - Real.exp (-literalStep q / 4) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hl.1]))
  have hR : (-1 : ℝ) ^ (q + 1) * ((q + 1).factorial : ℝ) * Real.log 2 *
      literalStep q ^ q * (1 - Real.exp (-literalStep q / 4)) / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) hL.ne')
      (pow_ne_zero _ hl.1.ne')) hr.ne') (by norm_num)
  have hM : (∑ i, literalCoeffs q i * (literalNodes q i : ℂ) ^ (q + 1)) ≠ 0 := by
    rw [literal_moment_residual q hq]
    exact_mod_cast hR
  have hLexp : 1 < Real.exp (Real.log 2 / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  have hlexp : 1 < Real.exp (literalStep q / 2) := Real.one_lt_exp_iff.mpr (by linarith [hl.1])
  have hqexp : 1 < Real.exp (literalStep q / 4) := Real.one_lt_exp_iff.mpr (by linarith [hl.1])
  have hRexp : (literalStep q / 2) * (1 - Real.exp (Real.log 2 / 2)) *
      (1 - Real.exp (literalStep q / 2)) ^ (q - 1) *
      (Real.exp (literalStep q / 4) - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (by linarith : 0 < literalStep q / 2))
      (ne_of_lt (by linarith : 1 - Real.exp (Real.log 2 / 2) < 0)))
      (pow_ne_zero _ (ne_of_lt (by linarith : 1 - Real.exp (literalStep q / 2) < 0))))
      (ne_of_gt (by linarith : 0 < Real.exp (literalStep q / 4) - 1))
  have hMexp : (∑ i, literalCoeffs q i * (literalNodes q i : ℂ) *
      (Real.exp (literalNodes q i / 2) : ℂ)) ≠ 0 := by
    rw [literal_exp_residual q hq]
    exact_mod_cast hRexp
  let Eg := literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2
  have hEg : 0 < Eg := by
    exact div_pos (mul_pos hl.1 (by positivity)) (by norm_num)
  have hEg' : Eg ≤ literalStep q := by
    have he : Real.exp (-literalStep q / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hl.1])
    have hp := Real.exp_pos (-literalStep q / 4)
    have hsq : Real.exp (-literalStep q / 4) ^ 2 ≤ 1 := by nlinarith
    have ht := mul_nonneg hl.1.le (sub_nonneg.mpr hsq)
    dsimp [Eg]
    nlinarith only [ht]
  have hD0 : 0 ≤ D := by linarith
  have hlD : literalStep q ≤ D := by linarith [hl.2.1]
  have hout := literal_ratio_constant q hq (literalN q) Eg
    (W D (literalNuNodes (literalStep q)) (fun i => (literalNuCoeffs (literalStep q) i : ℂ)))
    (V D (literalNodes q) (literalCoeffs q)) (energy (literalNodes q) (literalCoeffs q))
    (literal_N_pos q hq) hEg hEg' (literalNu_W_lower D _ hD0 hl.1.le hlD)
    (literal_V_upper q hq D hD) (by simpa only [Eg, mul_assoc] using literal_energy_double q hq)
  exact ⟨literalNodes q, literalCoeffs q, literal_support q hq, literal_support_D q hq D hD,
    literal_moments q hq, literal_exp_null q, hM, hMexp, hout.1, hout.2⟩


end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
