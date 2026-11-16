/- GID: D5/S3/Quantum/Foundation/QubitWeightedCommutator
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/QubitWeightedCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density-weighted Frobenius commutators of arbitrary complex qubit matrices. -/

import D5.S3.Quantum.GNSMatrix

/-! A dimension-two density-weighted estimate in the Frobenius norm. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Foundation.QubitWeightedCommutator

private abbrev Q := Matrix (Fin 2) (Fin 2) ℂ

private theorem hs_sq_entries (A : Q) :
    ‖A‖ ^ 2 = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 +
      (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

private theorem traceless_commutator_hs_sq (A V : Q)
    (hA : A.trace = 0) (hV : V.trace = 0) :
    ‖A * V - V * A‖ ^ 2 =
      2 * (‖A‖ ^ 2 * ‖V‖ ^ 2 - ‖(A * Vᴴ).trace‖ ^ 2) := by
  have ha : A 1 1 = -A 0 0 := by
    rw [Matrix.trace_fin_two] at hA
    exact eq_neg_of_add_eq_zero_right hA
  have hv : V 1 1 = -V 0 0 := by
    rw [Matrix.trace_fin_two] at hV
    exact eq_neg_of_add_eq_zero_right hV
  simp only [hs_sq_entries, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.conjTranspose_apply,
    RCLike.star_def, ha, hv, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem traceless_square (H : Q) (ht : H.trace = 0) :
    H * H = ((H * H).trace / 2) • (1 : Q) := by
  have hd : H 1 1 = -H 0 0 := by
    rw [Matrix.trace_fin_two] at ht
    exact eq_neg_of_add_eq_zero_right ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.smul_apply, hd] <;> ring

private theorem weighted_hermitian_norm (b H : Q) (hb : b.PosSemidef)
    (htrace : b.trace = 1) (hH : H.IsHermitian) (ht : H.trace = 0) :
    ‖H‖ = Real.sqrt 2 * ‖CFC.sqrt b * H‖ := by
  have hB : (CFC.sqrt b)ᴴ = CFC.sqrt b := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hBB := CFC.sqrt_mul_sqrt_self b hb.nonneg
  have hnorm : ((‖H‖ ^ 2 : ℝ) : ℂ) = (H * H).trace := by
    simpa only [hH.eq] using GNSMatrix.frobenius_norm_sq_eq_trace H
  have hSquare : H * H = (((‖H‖ ^ 2 / 2 : ℝ) : ℂ)) • (1 : Q) := by
    rw [traceless_square H ht, ← hnorm, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hs : ‖CFC.sqrt b * H‖ ^ 2 = ‖H‖ ^ 2 / 2 := by
    apply Complex.ofReal_injective
    calc
      ((‖CFC.sqrt b * H‖ ^ 2 : ℝ) : ℂ) =
          ((CFC.sqrt b * H)ᴴ * (CFC.sqrt b * H)).trace :=
        GNSMatrix.frobenius_norm_sq_eq_trace _
      _ = (H * b * H).trace := by
        simp only [Matrix.conjTranspose_mul, hB, hH.eq, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (CFC.sqrt b), hBB]
      _ = (b * (H * H)).trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm H (b * H), Matrix.mul_assoc]
      _ = ((‖H‖ ^ 2 / 2 : ℝ) : ℂ) := by
        rw [hSquare, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, htrace]
        simp
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := norm_nonneg H
  have hw := norm_nonneg (CFC.sqrt b * H)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  apply (sq_eq_sq₀ hn (mul_nonneg hp hw)).mp
  rw [mul_pow, hsqrt, hs]
  ring

private theorem sqrt_hs_norm_one (b : Q) (hb : b.PosSemidef)
    (ht : b.trace = 1) : ‖CFC.sqrt b‖ = 1 := by
  have hB : (CFC.sqrt b)ᴴ = CFC.sqrt b := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have h := GNSMatrix.frobenius_norm_sq_eq_trace (CFC.sqrt b)
  rw [hB, CFC.sqrt_mul_sqrt_self b hb.nonneg, ht] at h
  have hs : ‖CFC.sqrt b‖ ^ 2 = 1 := by
    exact_mod_cast h
  nlinarith [norm_nonneg (CFC.sqrt b)]

private theorem traceless_bound (X V b : Q)
    (hX : X.trace = 0) (hV : V.trace = 0)
    (hb : b.PosSemidef) (ht : b.trace = 1) :
    ‖X * V - V * X‖ ≤
      Real.sqrt 2 * ‖CFC.sqrt b * (X * V - V * X)‖ +
        (1 + Real.sqrt 2) * ‖X * Vᴴ - Vᴴ * X‖ := by
  by_cases hv : V = 0
  · subst V
    simp
  have hq : ((‖V‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  let α : ℂ := (X * V).trace / ((‖V‖ ^ 2 : ℝ) : ℂ)
  let D : Q := X - α • Vᴴ
  let H : Q := Vᴴ * V - V * Vᴴ
  let N : Q := α • H
  let R : Q := D * V - V * D
  have hVs : Vᴴ.trace = 0 := by
    rw [Matrix.trace_conjTranspose, hV, star_zero]
  have hD : D.trace = 0 := by
    simp only [D, Matrix.trace_sub, Matrix.trace_smul, hX, hVs, smul_zero, sub_zero]
  have hDV : (D * V).trace = 0 := by
    dsimp [D, α]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      ← GNSMatrix.frobenius_norm_sq_eq_trace V, smul_eq_mul, div_mul_cancel₀ _ hq,
      sub_self]
  have hR : ‖R‖ ≤ ‖X * Vᴴ - Vᴴ * X‖ := by
    have hr := traceless_commutator_hs_sq D V hD hV
    have hk := traceless_commutator_hs_sq D Vᴴ hD hVs
    rw [Matrix.frobenius_norm_conjTranspose, Matrix.conjTranspose_conjTranspose,
      hDV, norm_zero, zero_pow (by omega), sub_zero] at hk
    have he : D * Vᴴ - Vᴴ * D = X * Vᴴ - Vᴴ * X := by
      simp only [D, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul]
      abel
    rw [he] at hk
    dsimp [R]
    nlinarith [norm_nonneg (D * V - V * D), norm_nonneg (X * Vᴴ - Vᴴ * X),
      sq_nonneg ‖(D * Vᴴ).trace‖]
  have hH : H.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self V).sub
      (Matrix.isHermitian_mul_conjTranspose_self V)
  have hHt : H.trace = 0 := by
    dsimp [H]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hN : ‖N‖ = Real.sqrt 2 * ‖CFC.sqrt b * N‖ := by
    have h := weighted_hermitian_norm b H hb ht hH hHt
    simp only [N, Matrix.mul_smul, norm_smul]
    rw [h]
    ring
  have hsplit : X * V - V * X = N + R := by
    simp only [N, R, H, D, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hweight : ‖CFC.sqrt b * R‖ ≤ ‖R‖ := by
    calc
      _ ≤ ‖CFC.sqrt b‖ * ‖R‖ := Matrix.frobenius_norm_mul _ _
      _ = ‖R‖ := by rw [sqrt_hs_norm_one b hb ht, one_mul]
  have htriangle : ‖CFC.sqrt b * N‖ ≤
      ‖CFC.sqrt b * (X * V - V * X)‖ + ‖CFC.sqrt b * R‖ := by
    have he : CFC.sqrt b * N =
        CFC.sqrt b * (X * V - V * X) - CFC.sqrt b * R := by
      rw [hsplit, Matrix.mul_add]
      abel
    rw [he]
    exact norm_sub_le _ _
  have hsum : ‖X * V - V * X‖ ≤ ‖N‖ + ‖R‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  rw [hN] at hsum
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private theorem scalar_sub_commutator (X W : Q) (a c : ℂ) :
    (X - a • 1) * (W - c • 1) - (W - c • 1) * (X - a • 1) =
      X * W - W * X := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, mul_comm a c]
  abel

/-- The Hilbert-Schmidt norm is explicitly the Frobenius matrix norm. The density
weight can be singular, and both matrices can be arbitrary complex matrices. -/
theorem qubit_weighted_commutator_bound (X W b : Matrix (Fin 2) (Fin 2) ℂ)
    (hb : b.PosSemidef) (htrace : Matrix.trace b = 1) :
    ‖X * W - W * X‖ ≤
      Real.sqrt 2 * ‖CFC.sqrt b * (X * W - W * X)‖ +
        (1 + Real.sqrt 2) * ‖X * Wᴴ - Wᴴ * X‖ := by
  let X₀ : Q := X - (X.trace / 2) • 1
  let V : Q := W - (W.trace / 2) • 1
  have hX : X₀.trace = 0 := by
    simp [X₀, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  have hV : V.trace = 0 := by
    simp [V, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  have hc : X₀ * V - V * X₀ = X * W - W * X :=
    scalar_sub_commutator X W _ _
  have hcs : X₀ * Vᴴ - Vᴴ * X₀ = X * Wᴴ - Wᴴ * X := by
    dsimp [X₀, V]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    exact scalar_sub_commutator X Wᴴ _ _
  simpa only [hc, hcs] using traceless_bound X₀ V b hX hV hb htrace

end D5.S3.Quantum.Foundation.QubitWeightedCommutator
