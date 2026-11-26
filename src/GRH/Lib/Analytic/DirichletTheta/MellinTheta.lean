import GRH.Lib.Analytic.PolyaVinogradov.PolyaVinogradov
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: the transformation formula and the Mellin transform of the theta series of a
Dirichlet character. The transformation is proved only in absolute value, so no root number appears,
first for any non-principal character against its finite Fourier transform and then for a primitive
character against itself. The Mellin formula holds for any bounded coefficients to the right of 1
and for such characters to the right of 0. Source: Davenport, Multiplicative Number Theory;
Montgomery–Vaughan ch. 10.

This file: Gaussian theta series of a character: Poisson symmetry, Mellin transform is Gamma times
L. -/

open Complex Filter HurwitzZeta MeasureTheory Real Set ZMod

/-- The function g(x) = x^j e^{−πx²} of a real variable x. -/
noncomputable def gaussianMonomial (j : Fin 2) x := x ^ j.1 * rexp (-π * x ^ 2)

/-- The theta series ∑_{n ≥ 1} c(n) g(nt) with coefficients c, where g(x) = x^j e^{−πx²}. -/
noncomputable def gaussianTheta j (c : ℕ → ℂ) t := ∑' n : ℕ+, c n * gaussianMonomial j (n * t)

/-- The integral ∫_r^∞ |θ(t)| dt/√t, where θ(t) = ∑_{n ≥ 1} c(n) g(nt), g(x) = x^j e^{−πx²}, is
the theta series `gaussianTheta` j c. -/
noncomputable abbrev thetaTailIntegral j c r := ∫ t in Ioi r, ‖gaussianTheta j c t‖ / √t

/-- The gamma factor Γ_j(s) = ∫_0^∞ g(t) t^{s−1} dt, the Mellin transform of g(t) = t^j
e^{−πt²}. -/
noncomputable def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin (gaussianMonomial j ·)

variable {j : Fin 2} {c : ℕ → ℂ} {q} {t : ℝ} {s : ℂ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- If f is measurable and |f(t)| ≤ D e^{−t} for t > 0, then its Mellin transform is holomorphic
in Re s > 0 and bounded on the strip 1/2 ≤ Re s ≤ 2. -/
lemma mellin_differentiableOn_and_bounded {D} {f : ℝ → ℂ} (b : ∀ {t}, 0 < t → ‖f t‖ ≤ D * rexp (-t))
    (m : AEStronglyMeasurable f := by fun_prop (disch := simp) [gaussianTheta, gaussianMonomial]) :
  DifferentiableOn ℂ (mellin f) {z | 0 < z.re} ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖mellin f z‖ ≤ G := by
  refine (fun o p a ↦ have c s := mellinConvergent_of_isBigO_rpow_exp (s := s) one_pos a o p
    ⟨fun _ ↦ (mellin_differentiableAt_of_isBigO_rpow_exp one_pos a o p · |>.differentiableWithinAt),
    _, fun z _ ↦ norm_integral_le_of_norm_le ((c 2⁻¹ ?_).prodMk (c 2 ?_)).norm
    (ae_restrict_of_forall_mem ?_ fun t ↦ ?_)⟩) ?_ ?_ fun _ _ ↦ (volume.finiteAt_nhdsWithin
    ..).integrableAtFilter ⟨⊤, ?_⟩ ?_ <;> simp_all [Asymptotics.isBigO_iff]
  use D, 1, by grind
  iterate 2 exact ⟨_, mem_inf_of_right fun t k ↦ (b k).trans (by grw [le_abs_self D, ← k.out])⟩
  bound [le_total t 1]

lemma norm_gaussianMonomial_le (h : 0 ≤ t) : ‖gaussianMonomial j t‖ ≤ 3 * rexp (-t) ^ 2 := by
  grw [gaussianMonomial, norm_of_nonneg (by bound), show t ^ j.1 ≤ t + 1 by fin_cases j <;> grind,
    add_one_le_exp, ← exp_one_lt_three, ← pi_gt_three]
  simp [sq, ← Real.exp_add]; grind [sq_nonneg (t - 2⁻¹)]

/-- The trivial bound: for j ∈ {0, 1}, |c(n)| ≤ 1 and t > 0, the series ∑_{n ≥ 1} c(n) g(nt),
g(x) = x^j e^{−πx²}, converges absolutely and has modulus at most 3e^{−t}/t. -/
lemma summable_and_norm_gaussianTheta_le (hc : ∀ n, ‖c n‖ ≤ 1) (ht : 0 < t) : (Summable fun n : ℕ+ ↦
  c n * gaussianMonomial j (n * t)) ∧ ‖gaussianTheta j c t‖ ≤ 3 * rexp (-t) / t := by
  have H := hasSum_pnat_iff_hasSum_succ.2 ((hasSum_nat_add_iff' 1).2
    ((hasSum_geometric_of_abs_lt_one (by simpa : |rexp (-t) ^ 2| < 1)).mul_left 3))
  refine (fun b ↦ ⟨H.summable.of_norm_bounded b, (tsum_of_norm_bounded H b).trans ?_⟩) fun n ↦ ?_
  · grw [norm_mul, hc, norm_real, norm_gaussianMonomial_le] <;> simp [← Real.exp_nat_mul, field,
      ht.le]
  simp [t.exp_neg, field, *]; nlinarith [t.add_one_le_exp]

/-- For Re s > 0, Γ_j(s) = ½ π^{−(s+j)/2} Γ((s+j)/2). -/
lemma gaussianMellin_eq (hs : 0 < s.re) : gaussianMellin j s = Gammaℝ (s + j) / 2 := by
  simpa [gaussianMellin, gaussianMonomial, field] using (mellin_cpow_smul _ s j).trans
    ((mellin_comp_rpow _ _ 2).trans (congrArg _ (@hasSum_mellin_pi_mul_sq Unit _ 1 1
    (rexp <| -π * ·) _ (by simp; bound) (by simp) .of_finite).tsum_eq.symm))

/-- Riemann's formula: if |c| ≤ 1 and Re s > 1, the Mellin transform at s of t ↦ ∑_{n ≥ 1} c(n)
g(nt), g = `gaussianMonomial` j, is Γ_j(s) ∑_{n ≥ 1} c(n) n^{−s}. -/
lemma mellin_gaussianTheta (hc : ∀ n, ‖c n‖ ≤ 1) (hs : 1 < s.re) :
    mellin (gaussianTheta j c) s = gaussianMellin j s * LSeries c s := by
  rw [gaussianMellin_eq (by bound), LSeries, ← tsum_pnat_eq_tsum_of_eq_zero rfl]
  convert (mellin_cpow_smul _ s j.1).trans ((mellin_comp_rpow _ _ 2).trans (congrArg _
    (@hasSum_mellin_pi_mul_sq ℕ+ _ (fun n ↦ c n * n ^ j.1) (·) _ _ (by simp; bound)
    (fun u (h : 0 < u) ↦ (((@summable_and_norm_gaussianTheta_le j c √u hc ?_).1.div_const
    (√u ^ j.1)).congr ?_).hasSum) ((summable_pnat_iff_summable_nat.2 (summable_nat_rpow_inv.2
    hs)).of_nonneg_of_le ?_ ?_)).tsum_eq.symm)) using 1 <;> simp [← tsum_mul_left, cpow_add,
    rpow_add, field, mellin, gaussianTheta, gaussianMonomial, mul_pow, division_def, mul_assoc,
    mul_left_comm, le_of_lt, ne_of_gt, *]

omit [NeZero q] in
/-- If Φ on ℤ/q satisfies Φ(−x) = (−1)^j Φ(x) and Φ(0) = 0, and ∑_{n ∈ ℤ} Φ(n) g(nt) converges
to S, g = `gaussianMonomial` j, then S = 2 ∑_{n ≥ 1} Φ(n) g(nt). -/
lemma two_mul_gaussianTheta t {Φ : ZMod q → ℂ} {S} (h : ∀ x, Φ (-x) = (-1) ^ j.1 * Φ x) (h0 : Φ 0 =
  0) (H : HasSum (fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t)) S) : 2 * gaussianTheta j (Φ ·) t =
  S := by rw [← H.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ H.summable] <;> fin_cases j <;>
  simp [Function.Even, gaussianMonomial, gaussianTheta, *]

/-- Poisson summation for g = `gaussianMonomial` j, j ≤ 1: for real a and t > 0, ∑_{n ∈ ℤ} g((n +
a)t) converges to some S, and ∑_{n ∈ ℤ} e^{2πian} g(n/t) converges to i^j t S. -/
lemma poisson_summation_gaussianMonomial a (ht : 0 < t) : ∃ S,
  HasSum (fun n : ℤ ↦ gaussianMonomial j ((n + a) * t)) S ∧ HasSum (fun n : ℤ ↦ cexp
  (2 * π * I * a * n) * gaussianMonomial j (n * t⁻¹)) (I ^ j.1 * t * S) := have h := pow_pos ht 2
  by fin_cases j <;> [obtain ⟨u, v⟩ := hasSum_int_evenKernel a h, hasSum_int_cosKernel a (inv_pos.2
                h); obtain ⟨u, v⟩ := (hasSum_int_oddKernel a h).mul_left t, (hasSum_int_sinKernel a
    (inv_pos.2 h)).mul_left (I / t)] <;> refine ⟨_, u.congr_fun ?_, (v.congr_fun ?_).trans_eq
    (congrArg _ ?_)⟩ <;> simp [gaussianMonomial, mul_pow, mul_assoc, evenKernel_functional_equation,
    ht.ne', oddKernel_functional_equation, ← rpow_natCast_mul ht.le, field, mul_div_cancel₀]

lemma gaussianMellin_differentiableOn_and_bdd : DifferentiableOn ℂ (gaussianMellin j) {z | 0 < z.re}
  ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖gaussianMellin j z‖ ≤ G := mellin_differentiableOn_and_bounded
  fun h ↦ by grw [norm_real, norm_gaussianMonomial_le, _root_.sq_le] <;> simp [h.le, exp_nonneg]

/-- For j ≤ 1, |Γ_j| has a positive lower bound on every compact subset of the half-plane Re s >
0. -/
lemma exists_pos_le_norm_gaussianMellin {K} (hK : IsCompact K) (h : ∀ s ∈ K, 0 < s.re) :
    ∃ c > 0, ∀ s ∈ K, c ≤ ‖gaussianMellin j s‖ :=
  hK.exists_forall_le' (gaussianMellin_differentiableOn_and_bdd.1.continuousOn.mono h).norm
  fun s k ↦ by simp [gaussianMellin_eq, Gammaℝ_ne_zero_of_re_pos, (h s k).trans_le]

variable (h1 : χ ≠ 1) (hp : χ (-1) = (-1) ^ j.1)

include h1 hp

/-- For j ≤ 1, non-principal χ mod q with χ(−1) = (−1)^j and t > 0: t |θ_χ(t)| = |θ_φ(1/(qt))|,
where θ_c = `gaussianTheta` j c and φ(n) = q⁻¹ ∑_a χ(a) e^{2πian/q}.

Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
lemma gaussianTheta_poisson_summation (ht : 0 < t) :
  t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (𝓕⁻ χ ·) (q * t)⁻¹‖ := by
  have e (x : ZMod q) := hp ▸ neg_one_mul x ▸ map_mul χ _ x
  choose S h h' using fun a : ZMod q ↦
    @poisson_summation_gaussianMonomial j (q * t) (a.val / q) (by simpa)
  have a := two_mul_gaussianTheta t e (χ.map_zero' (h1 ∘ χ.level_one')) ((hasSum_sum fun a _ ↦
    (Function.Injective.hasSum_iff (g := fun n : ℤ ↦ a.cast + q * n) (fun _ ↦ by simp) (by
    simp_all [intCast_eq_iff, ne_comm])).1 (((hasSum_ofReal.2 (h a)).mul_left (χ a)).congr_fun
    (by simp [← mul_assoc, add_mul]; grind))).congr_fun (Fintype.sum_pi_single' ↑· _ |>.symm))
  have b := @two_mul_gaussianTheta j _ (q * t)⁻¹ (𝓕⁻ χ) _ (fun n ↦ by
    simp_rw [invDFT_apply', ← congr($(dft_comp_neg χ) (-n)), e, dft_const_mul]; ring)
    (by simp [invDFT_apply, χ.sum_eq_zero_of_ne_one h1]) (((hasSum_sum (s := ⊤) fun a _ ↦
    (h' a).mul_left (χ a)).div_const q).congr_fun fun n ↦ by
    simp_rw [invDFT_apply, ← zsmul_eq_mul', AddChar.map_zsmul_eq_zpow, stdAddChar_apply]
    simp [toCircle_apply, ← exp_int_mul, Finset.sum_mul, -natCast_val, field]; grind)
  simp_all [mul_left_comm, ← Finset.mul_sum, ← a, abs_of_pos, field]

/-- Theta functional equation in absolute value: for j ≤ 1, primitive non-principal χ mod q with
χ(−1) = (−1)^j and t > 0, √q t |θ(t)| = |θ(1/(qt))|, where θ = `gaussianTheta` j χ.

Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
lemma norm_gaussianTheta_functional_equation (hχ :
  χ.IsPrimitive) (ht : 0 < t) : √q * t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (χ ·)
  (q * t)⁻¹‖ := by rw [mul_assoc, gaussianTheta_poisson_summation, eq_comm, ← norm_star] <;>
  simp [gaussianTheta, tsum_star, invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum,
  χ.star_apply', mul_assoc, mul_left_comm, tsum_mul_left, norm_gaussSum_of_isPrimitive, *, field]

/-- For a non-principal character χ mod q with χ(−1) = (−1)^j, j ∈ {0, 1}, and t > 0: |∑_{n ≥ 1}
χ(n) g(nt)| ≤ 3q·e^{1−t}, where g(x) = x^j e^{−πx²}. -/
lemma norm_gaussianTheta_char_le (h : 0 < t) : ‖gaussianTheta j (χ ·) t‖ ≤ 3 * q * rexp 1 * rexp
  (-t) := by
  cases le_total 1 t
  · grw [(summable_and_norm_gaussianTheta_le (by simp) h).2, div_le_self,
      ← @NeZero.one_le q] <;> bound
  grw [← mul_le_mul_iff_right₀ h, gaussianTheta_poisson_summation,
    (summable_and_norm_gaussianTheta_le (fun n ↦ by grw [invDFT_apply, norm_smul,
    norm_sum_le_of_le _ (n := 1)] <;> simp) _).2, exp_le_one_iff.2] <;> simp [field, t.exp_neg, *]

/-- For j ≤ 1 and non-principal χ with χ(−1) = (−1)^j, the Mellin transform of t ↦ ∑_{n ≥ 1}
χ(n) g(nt), g = `gaussianMonomial` j, equals Γ_j(s) L(s, χ) for Re s > 0. -/
lemma mellin_gaussianTheta_char (hs : 0 < s.re) : mellin (gaussianTheta j (χ ·)) s =
  gaussianMellin j s * χ.LFunction s := have o := isOpen_re_gt
  ((mellin_differentiableOn_and_bounded (norm_gaussianTheta_char_le h1 hp)).1.analyticOnNhd
    (o 0)).eqOn_of_preconnected_of_eventuallyEq
  ((gaussianMellin_differentiableOn_and_bdd.1.mul (by fun_prop)).analyticOnNhd (o 0))
    (convex_halfSpace_re_gt 0).isPreconnected (by simp : 0 < re 2) (.mono ((o 1).mem_nhds (by simp))
  (by simp_all [mellin_gaussianTheta, χ.LFunction_eq_LSeries])) hs

/-- For j ≤ 1, primitive non-principal χ mod q with χ(−1) = (−1)^j, T > 0 and q ≤ T²: ∫_0^∞
|θ(t)| dt/√t ≤ 2 ∫_{1/T}^∞ |θ(t)| dt/√t, where θ = `gaussianTheta` j χ. -/
lemma thetaTailIntegral_zero_le_two_mul (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 < T) (h : q ≤ T ^ 2) :
    thetaTailIntegral j (χ ·) 0 ≤ 2 * thetaTailIntegral j (χ ·) T⁻¹ := by_cases (fun i ↦ by
  grw [two_mul, ← sub_le_iff_le_add, ← setIntegral_sdiff _ i, Ioi_sdiff_Ioi, thetaTailIntegral,
    ← show _ '' Ioo 0 T⁻¹ ⊆ Ioi T⁻¹ from forall_mem_image.2 fun t ⟨a, b⟩ ↦ inv_strictAnti₀
    (b := q * t) ?_ (by grw [h, b]; simp [sq]), integral_image_eq_integral_abs_deriv_smul _
    fun t k ↦ (hasDerivAt_const_mul _).hasDerivWithinAt.fun_inv (by simp [k.1.ne']),
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun]
  any_goals simp +contextual [← norm_gaussianTheta_functional_equation, abs_div, field, EqOn,
    le_of_lt, -mul_inv_rev, *]
  exacts [.of_forall fun _ ↦ by positivity, i.mono_measure (by gcongr; bound)]) (integral_undef ·
    |>.trans_le (by positivity))
