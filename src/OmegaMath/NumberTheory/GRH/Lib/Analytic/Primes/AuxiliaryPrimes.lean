import OmegaMath.NumberTheory.GRH.Lib.Analytic.DirichletTheta.MellinTheta
import OmegaMath.NumberTheory.GRH.Lib.Analytic.Landau.PolarLandau
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). From a small
zero-free disc at 1, this file only finds one prime congruent to 1 modulo a power of a fixed
multiple of 4, with its logarithm in a long window. It gives no asymptotic count. Source: Montgomery
and Vaughan, Multiplicative Number Theory I, 2007, Cor. 11.19.

This file: A prime 1 modulo M^k with logarithm in a long window; zero-free disc. -/

attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono
open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory LSeries Finset Real
  Topology vonMangoldt Chebyshev Polynomial ZMod MulChar

/-- For 0 < r < 1/9 there is C ≥ 0 with |L(s, χ)| ≤ C q^(2r) on the disc |s − 1| ≤ r, for every
modulus q and every non-principal character χ mod q. -/
lemma exists_norm_LFunction_le {r} (h0 : 0 < r) (_ : r < 9⁻¹) : ∃ C ≥ 0, ∀ {q} [NeZero q]
    {χ : DirichletCharacter ℂ q} {s}, χ ≠ 1 → dist s 1 ≤ r → ‖χ.LFunction s‖ ≤ C * q ^ (2 * r) := by
  have p s := by simpa [← dist_eq_norm] using abs_re_le_norm (s - 1)
  choose c c0 hc using
    (@exists_pos_le_norm_gaussianMellin · _ (isCompact_closedBall 1 r) (by simp; grind))
  exact ⟨_, norm_nonneg (_ / c ·), @fun q ⟨_⟩ χ s hχ hs ↦ by
    have ⟨j, hp⟩ : ∃ j : Fin 2, χ (-1) = (-1) ^ j.1 := by simpa using! χ.even_or_odd
    grw [← norm_le_pi_norm, ← le_norm_self, div_mul_eq_mul_div, le_div_iff₀' (c0 j), hc j s hs,
      ← norm_mul, ← mellin_gaussianTheta_char hχ hp (by grind), mellin, norm_integral_le_of_norm_le
      (((GammaIntegral_convergent h0).const_mul (3 * rexp 1)).mul_const _)
      (ae_restrict_of_forall_mem (by simp) fun t (k : 0 < t) ↦ ?_), integral_mul_const]
    grw [norm_smul, le_min (summable_and_norm_gaussianTheta_le (by simp) k).2
      (norm_gaussianTheta_char_le hχ hp k), min_def]
    split <;> simp (disch := positivity) [← log_le_log_iff, abs_le] at * <;>
      nlinarith [p s, log_natCast_nonneg q]⟩

/-- Let M > 0 be a multiple of 4 and A natural. For small η > 0, all k ≥ 2 with M^k ≤ η^{−A},
all characters χ mod M^k and |s − 1| ≤ η, one has η|L̃′(s, χ)| < |L̃(s, χ)|, where L̃ is
`entireL`. -/
lemma eventually_mul_norm_deriv_entireL_lt A {M : ℕ} [NeZero M] (e : 4 ∣ M) : ∀ᶠ η : ℝ in 𝓝[>] 0,
  ∀ k > 1, ∀ χ s,
  M ^ k ≤ (η ^ A)⁻¹ → dist s 1 ≤ η → ¬‖entireL χ s‖ ≤ η * ‖deriv (@entireL (M ^ k) _ χ) s‖ := by
  obtain ⟨⟨r, h0, _⟩, m, f⟩ := exists_pos_mul_lt one_pos (20 * A + 18 : ℝ), e
  have ⟨K, _, hC⟩ := exists_norm_LFunction_le (add_pos h0 h0) (by nlinarith)
  filter_upwards [mem_inf_of_left (eventually_closedBall_subset (by
    simp; intro; and_intros <;> apply ContinuousAt.eventually_lt <;> first
      | fun_prop (disch := grind) | simp (disch := bound) [entireL_ne_zero] : ∀ᶠ x in 𝓝 (0, 1), ∀ f
    ∈ range (@entireL (M ^ 2) _), x.1 * ‖deriv f x.2‖ < ‖f x.2‖ ∧ x.1 ^ (-A * (2 * (r + r)) * 5 + 1)
    * ‖f x.2‖ ^ 3 * (3 / r) ^ 4 * K ^ 5 < 1)), Ioc_mem_nhdsGT h0] with η H ⟨hη, j⟩ k o χ s hk hs h7
  have H {s} hs χ (h : χ ^ 2 = 1) := @H (η, s) (max_le (c := η) (by simp; grind) hs) (entireL χ)
    (((χ.factorsThrough_iff_ker_unitsMap (pow_dvd_pow M o)).2 fun u hu ↦
    ((intCast_eq_intCast_iff_dvd_sub u.1.cast 1 _).1 (by simp; use congr($hu.1))).elim fun t a ↦ by
    obtain ⟨⟨c⟩⟩ := (C (M * m * t) + X ^ 2 + X).existsUnique_nilpotent_sub_and_aeval_eq_zero
      (x := 0 * u.1) ⟨k, by simp [mul_pow, natCast_pow_eq_zero_of_le]⟩ (by simp), congr($a + u.1)
    ext; simpa [show u = (1 + 2 * c) ^ 2 by simp [f, map_ofNat] at *; grind, ← pow_apply', h] using
      one_apply_coe u).2.imp fun g a ↦ by ext s; fun_cases entireL g <;> by_cases s =
    1 <;> simp [LFunction_changeLevel, Nat.primeFactors_pow, *, entireL, o.ne_zero,
    LFunctionTrivChar_eq_mul_riemannZeta] <;>
    simpa [*, Nat.primeFactors_pow] using g.LFunction_changeLevel dvd_rfl)
  have ⟨h, n, h1⟩ : χ ^ 2 ≠ 1 ∧ χ ≠ 1 ∧ dist (1 + η : ℂ) 1 ≤ η := by simp; grind [one_pow]
  have hd (z : ℂ) (b : dist z 1 ≤ η) := norm_deriv_le_of_forall_mem_sphere_norm_le h0
    (differentiable_LFunction n).diffContOnCl fun w a ↦ hC n (by grw [dist_triangle, a.le, b, j])
  apply ((H h1 1 (by simp)).2.trans_le (norm_LFunction_product_ge_one χ hη 0)).not_ge
  simp [entireL, hη.ne', abs_of_pos, rpow_add, rpow_mul hη.le, *, -neg_mul] at h7 ⊢
  nth_grw 1 [norm_le_insert' (χ.LFunction _), h7, hd, (convex_closedBall
    ..).norm_image_sub_le_of_norm_deriv_le (by fun_prop) hd hs h1, ← dist_eq_norm,
    dist_triangle_right, hs, h1, hC h, ← hk] <;> grind

/-- Let M > 0 be a multiple of 4 and A natural. For large W, all k ≥ 2 with M^k ≤ W^A and all U in
[W, W^A], there is a prime p ≡ 1 mod M^k with U ≤ log p ≤ U + W.

Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). -/
lemma exists_prime_modEq_one_log_mem (M A : ℕ) [NeZero M] (hM : 4 ∣ M) : ∀ᶠ W : ℝ in atTop, ∀ k > 1,
  M ^
  k ≤ W ^ A → ∀ U ∈ Icc W (W ^ A), ∃ p, p.Prime ∧ p ≡ 1 [MOD M ^ k] ∧ .log p ∈ Icc U (U + W) := by
  obtain ⟨t, n, C, hC⟩ := tendsto_sqrt_atTop, (hasDerivAt_term · · · |>.differentiableAt),
    (LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 3 / 4) (by simpa [sum_filter,
    psi_sub_theta_eq_sum_not_prime, sqrt_eq_rpow] using! isBigO_psi_sub_theta_sqrt.natCast_atTop)
    (by bound) (by simp) (by bound)).norm
  filter_upwards [mem_atTop (C ⊔ 0), t (tendsto_inv_atTop_nhdsGT_zero
    (eventually_mul_norm_deriv_entireL_lt (2 * A) hM)), t (tendsto_exp_mul_div_rpow_atTop (2 *
    A * 2) 4⁻¹ (by simp) (Ioi_mem_atTop (.exp 2))), t (mem_atTop 9)] with W _ h hW g k o hq U hV
  set q := M ^ k; simp_all [← natCast_eq_natCast_iff, rpow_mul, pow_mul]
  have ⟨D, d, p, _⟩ : ∃ D > 0, 0 < W ∧ U * D = 1 := ⟨U⁻¹, by grind [inv_pos]⟩
  let a n : ℂ := @residueClass q 1 n
  let F z := (1 - z * ∑ χ, logDeriv (@entireL q _ χ) (1 + z)) / q.totient
  have e z (h : 0 < z.re) : LSeriesHasSum a (1 + z) (F z / z) := by
    convert (LSeriesHasSum.sum (S := ⊤) fun χ _ ↦ @LSeriesHasSum_mul_vonMangoldt q χ _ _ ?_).smul
      q.totient⁻¹ <;> simp [a, residueClass_eq, h, ite_div]
    field [ne_zero_of_re_pos h]
  have hb {z} (u : ‖z‖ ≤ (√W)⁻¹) : _ ∧ ‖F z‖ ≤ 2 := have h := (h k o · (1 + z) hq (by simpa))
    ⟨(norm_pos_iff.1 <| h · |>.trans_le' (by bound)), by
    grw [norm_div, mul_sum, norm_sub_le, norm_sum_le]; simp [logDeriv, mul_div]
    grw [u, h, div_self_le_one]
    simp [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ, field, mul_two, NeZero.one_le]⟩
  by_contra
  apply (@norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ _ _ _ 0 √W⁻¹ U (fun z ↦ (F z - z *
    ∑ n ∈ range ⌈U.exp⌉₊ with .log (n : ℕ) < U, term a (1 + z) n) / (2 - U * z - √W / 4 *
    (1 + √W * z) ^ 2).exp) 0 (by simpa) (DifferentiableOn.diffContOnCl_ball (fun s b ↦
    DifferentiableAt.differentiableWithinAt (by fun_prop (disch := simp_all) [logDeriv])) le_rfl)
    fun z u ↦ ?_).not_gt
  simp [F, field, Real.exp_sub] at *
  grw [hV.2, q.totient_le, M.cast_pow, hq]; grind
  obtain := z.sq_norm_sub_sq_re, z.abs_re_le_norm, sq_sqrt p.le
  simp [div_le_iff₀, exp_pos, -sub_re, sq, abs_le] at *; set E := re _
  obtain ⟨⟨⟩ : ∃ τ ≥ 0, τ ≤ W ∧ 2 - (U + τ) * z.re ≤ E, b : re (F D / D) ≤ 2 * U⟩ :=
    ⟨W / 2 * (1 + √W * z.re), by simp [u, field, E] at *; split_ands <;> nlinarith⟩, by
    grw [re_le_norm, norm_div, (hb _).2] <;> simp [abs_of_pos d, field] <;> nlinarith
  have G := (hasSum_re (e D d)).congr_fun fun n ↦ (re_eq_norm.2 (mod_cast term_nonneg
    (by simp [a, residueClass_nonneg]) _)).symm
  have key (n : ℕ) σ (h : .log n * (σ - z.re) ≤ E) : ‖term a (1 + z) n‖ ≤ E.exp *
      ‖term a (1 + σ) n‖ := by grw [← h]; by_cases n = 0 <;>
    simp [*, ↓cpow_add, cpow_def, field, mul_sub, Real.exp_sub, ← natCast_log]
  obtain ⟨v, x | x⟩ := u ▸ inv_anti₀ (by simp) g, le_or_gt z.re D
  · grw [norm_sub_le, norm_mul, (hb u.le).2, v, norm_sum_le, key, ← mul_sum,
      sum_le_hasSum _ (by simp) G, b] <;> simp at * <;> nlinarith [E.one_le_exp (by nlinarith)]
  grw [← mul_div_cancel₀ (F z) (ne_zero_of_re_pos (d.trans x)), ← mul_sub, norm_mul, v,
    sum_filter, (HasSum.sub (e z (by bound)) (hasSum_sum_of_ne_finset_zero (by grind [Nat.lt_ceil,
    lt_exp_of_log_lt]))).norm_le_of_bounded ((hC.add G).mul_left E.exp) fun n ↦ ?_, b]
  nlinarith [exp_pos E]
  split <;> simp; bound
  by_cases U + W < .log n <;> [grw [key n D (by nlinarith)]; grw [← @norm_term_le a _ _ _
    (by simp [a, indicator]; grind), key n (-4⁻¹) (by nlinarith)]] <;> bound
