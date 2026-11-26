import GRH.Lib.General.NumberTheory.ZeroSymmetry
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character.
It is proved here for initial intervals only, with the explicit bound 2√q(1+log q) for any
non-principal character. The bound is obtained by sieving the inducing primitive character over
divisors. Source: Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory;
Montgomery–Vaughan Thm 9.18.

This file: Pólya–Vinogradov inequality for non-principal characters; modulus of primitive Gauss
sums. -/

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

attribute [simp] Real.log_mul log_div log_rpow log_sqrt norm_le_one ne pos
  norm_cpow_eq_rpow_re_of_pos


variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive character mod q has absolute value √q. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  simpa [funext hχ.fourierTransform_eq_inv_mul_gaussSum, dft_mul_const, dft_comp_neg,
    fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift, ← star_gaussSum_eq] using
    congr(√‖$(dft_dft χ) (-1)‖)

/-- Pólya–Vinogradov inequality for a non-principal character χ mod q: |∑_{1 ≤ v ≤ X} χ(v)| ≤
2√q (1 + log q) for all X.

Known result: Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. -/
lemma polya_vinogradov (h : χ ≠ 1) (X : ℕ) : ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + .log q) := by
  let ⟨M, ⟨r, hr⟩, ψ, _, hψ, E⟩ := exists_isPrimitive_changeLevel_eq χ
  have e (v : ℕ) : χ v = ∑ e ∈ (v.gcd r).divisors, μ e • ψ v := by
    rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply, ← Int.cast_natCast]
    split <;> grind [Int.cast_natCast, apply_eq_zero_iff, changeLevel_eq_cast_of_dvd',
      coprime_mul_iff_right, isCoprime_iff_coprime]
  grw [funext e, sum_comm' (t' := r.divisors) (s' := fun e ↦ (Ioc 0 (X / e)).image (e * ·)) (by
    rintro v ⟨⟩ <;> simp [Nat.dvd_gcd_iff, le_div_iff_mul_le, dvd_def (b := v), mul_comm]
    aesop), norm_sum_le, sum_le_card_nsmul _ _ (√M * (1 + .log q)) fun d he ↦ ?_, card_le_card
    (t := Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image (r / ·)) fun d he ↦ ?_, card_union_le,
    Finset.card_image_le, congr(√$hr)] <;> clear e <;> simp [zero_lt_iff] at *
  · grw [nat_sqrt_le_real_sqrt]; grind
  -- of two complementary divisors one is at most `√r`
  · cases he.1; cases le_sqrt_of_eq_mul ‹_› <;> aesop
  -- the primitive character: its sums are at most `√M (1 + log M)`
  simp [← mul_sum, ← Int.cast_abs, ne_zero_of_dvd_ne_zero he.2 he.1]
  let f (n : ℕ) := √M * M / 2 * ((↑n)⁻¹ + (↑(M - n))⁻¹)
  grw [norm_le_one, abs_moebius_le_one, ← dft.symm_apply_apply ψ]
  simp_rw [invDFT_apply, ← nsmul_eq_mul', AddChar.map_nsmul_eq_pow, ← smul_sum, @sum_comm _ _ ℕ,
    ← sum_smul, hψ.fourierTransform_eq_inv_mul_gaussSum]
  grw [norm_smul, ← sum_erase _ (a := 0) (by simp [map_zero', ψ.level_one'.mt (by grind)]),
    norm_sum_le_of_le _ (n := (f ·.val)) fun k hk ↦ ?_, ← sum_image (val_injective M).injOn,
    (by grind : image _ _ ⊆ range (M + 1)), ← le_of_dvd _ ⟨r, hr⟩, ← harmonic_le_one_add_log]
  iterate 3 simp [harmonic, field, sum_range_succ', two_mul, f, ↓sum_flip (·⁻¹ : ℕ → ℝ), ← mul_sum]
  -- a geometric sum is at most `1 / sin (π x)`, `x = k / M`, and `sin (π x) ≥ 2 x (1 - x)`
  simp_all [norm_gaussSum_of_isPrimitive]
  obtain ⟨x, c, hx, d⟩ : ∃ x > (0 : ℝ), k.val = M * x ∧ 0 < 1 - x := ⟨k.val / M, by
    simp [field, val_lt, -natCast_val, *]⟩
  grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico (injective_stdAddChar.ne hk ∘ by
    simp) (by simp), norm_div, norm_sub_le, ← (?_ : 2 * (2 * x * (1 - x)) ≤ ‖(_ : ℂ) - 1‖)]
  · simp [val_le, field, ← two_mul, *]
  grw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, mul_comm _ I, hx,
    norm_exp_I_mul_ofReal_sub_one, ← le_norm_self, (by field : _ / 2 = 2 * (π / 2 * x)),
    Real.sin_two_mul, ← one_sub_mul_le_cos] <;> simp [field, pi_pos] <;> grind [le_sin_mul]
