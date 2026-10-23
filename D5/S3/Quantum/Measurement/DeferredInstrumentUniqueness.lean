/- GID: D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal upper-boundary meter, channel, instrument, and uniqueness claim. -/
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
def Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.single x x (1 : ℂ) *
    (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose
def Qs {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (s : ℝ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (s : ℂ) • Q U x + (((1 - s) / (d : ℝ) : ℝ) : ℂ) • 1
def It {d : ℕ} (t : ℝ) : MatrixMap (Fin d) (Fin d) ℂ :=
  depolarized (d := d) LinearMap.id (1 - t)
def sMax (d : ℕ) (t : ℝ) : ℝ :=
  (((d : ℝ) ^ 2 - 2) * (1 - t) +
      2 * Real.sqrt ((1 - (d : ℝ) ^ 2) * t ^ 2 + ((d : ℝ) ^ 2 - 2) * t + 1)) /
    (d : ℝ) ^ 2
def a2 (d : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (t * ((d : ℝ) ^ 2 - 1) + 1) - Real.sqrt (1 - t)) / (d : ℝ)
def b (t : ℝ) : ℝ := Real.sqrt (1 - t)
def Itilde {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (t : ℝ) (x : Fin d) :
    MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := (1 / (d : ℂ)) •
    (((((b t) ^ 2 : ℝ) : ℂ) * Matrix.trace (ρ * Q U x)) • 1 +
      (((a2 d t * b t : ℝ) : ℂ) • (ρ * Q U x + Q U x * ρ)) +
      (((a2 d t) ^ 2 : ℝ) : ℂ) • ρ)
  map_add' ρ σ := by
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, smul_add, add_smul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    ring_nf
  map_smul' c ρ := by
    ext i j
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_apply,
      Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> ring
def claim : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
    ∀ (U : Matrix.unitaryGroup (Fin d) ℂ),
    ∀ (t : ℝ), -1 / ((d : ℝ) ^ 2 - 1) ≤ t → t ≤ 1 →
    ∀ (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ),
      ((∀ x, (J x).IsCompletelyPositive) ∧
        (∑ x, J x = It t) ∧
        (∀ x ρ, Matrix.trace (J x ρ) = Matrix.trace (ρ * Qs U (sMax d t) x))) ↔
      (∀ x, J x = Itilde U t x)
/-- The auxiliary square-root coordinate appearing in the Choi certificate. -/
private def c (d : ℕ) (t : ℝ) : ℝ := Real.sqrt (t * ((d : ℝ) ^ 2 - 1) + 1)
/-- The distinguished diagonal coefficient. -/
private def k (d : ℕ) (t : ℝ) : ℝ := a2 d t + b t
private lemma It_apply {d : ℕ} (t : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    It t ρ = (t : ℂ) • ρ +
      (((((1 - t) / (d : ℝ)) : ℝ) : ℂ) * Matrix.trace ρ) • 1 := by
  ext i j
  simp [It, depolarized, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
private lemma Itilde_apply {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (t : ℝ)
    (x : Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Itilde U t x ρ = (1 / (d : ℂ)) •
      (((((b t) ^ 2 : ℝ) : ℂ) * Matrix.trace (ρ * Q U x)) • 1 +
        (((a2 d t * b t : ℝ) : ℂ) • (ρ * Q U x + Q U x * ρ)) +
        (((a2 d t) ^ 2 : ℝ) : ℂ) • ρ) := rfl
private lemma sum_Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ x, Q U x = 1 := by
  unfold Q; rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp U.2
/-- The quadratic certificate used in the standard-basis argument. -/
private def qCertificate (d : ℕ) (aa bb cc : ℝ) (x : Fin d)
    (w : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ k' : Fin d, ∑ j : Fin d,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0) +
    ((aa + bb) / bb) *
      ((∑ i : Fin d, Complex.normSq (w i i)) -
        (aa / cc) * Complex.normSq (∑ i : Fin d, w i i)) -
    Complex.normSq (w x x)
private lemma b_sq {t : ℝ} (ht : t ≤ 1) : (b t) ^ 2 = 1 - t := by
  rw [b, Real.sq_sqrt]; linarith
private lemma c_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (ht : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) :
    (c d t) ^ 2 = t * ((d : ℝ) ^ 2 - 1) + 1 := by
  rw [c, Real.sq_sqrt]
  have hd' : 0 < (d : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hm := mul_le_mul_of_nonneg_right ht (le_of_lt hd')
  have hm' : -1 ≤ t * ((d : ℝ) ^ 2 - 1) := by
    convert hm using 1 <;> field_simp
  nlinarith
private lemma bc_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    (b t * c d t) ^ 2 = (1 - (d : ℝ) ^ 2) * t ^ 2 +
      ((d : ℝ) ^ 2 - 2) * t + 1 := by
  rw [mul_pow, b_sq htu, c_sq hd htl]; ring
private lemma a2_channel_coeff {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    2 * a2 d t * b t / d + (a2 d t) ^ 2 = t := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hb := b_sq htu
  have hc := c_sq hd htl
  dsimp [a2]; change 2 * ((c d t - b t) / d) * b t / d + ((c d t - b t) / d) ^ 2 = t; field_simp
  nlinarith [c_sq hd htl, hb]
private lemma sMax_eq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    sMax d t = b t ^ 2 + 2 * a2 d t * b t / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hb : 0 ≤ b t := Real.sqrt_nonneg _
  have hc : 0 ≤ c d t := Real.sqrt_nonneg _
  have hbc : 0 ≤ b t * c d t := mul_nonneg hb hc
  have hroot : Real.sqrt ((1 - (d : ℝ) ^ 2) * t ^ 2 +
      ((d : ℝ) ^ 2 - 2) * t + 1) = b t * c d t := by
    rw [← bc_sq hd htl htu, Real.sqrt_sq hbc]
  rw [sMax, hroot]
  have hb' : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  dsimp [a2, c, b]; rw [hb']; field_simp; nlinarith [hb']
private lemma one_sub_sMax_eq_a2_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    1 - sMax d t = (a2 d t) ^ 2 := by
  rw [sMax_eq hd htl htu, b_sq htu]; nlinarith [a2_channel_coeff hd htl htu]
private lemma c_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (ht : -1 / ((d : ℝ) ^ 2 - 1) < t) : 0 < c d t := by
  unfold c; apply Real.sqrt_pos.2
  have hd' : 0 < (d : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have : -1 < t * ((d : ℝ) ^ 2 - 1) := by
    calc
      -1 = (-1 / ((d : ℝ) ^ 2 - 1)) * ((d : ℝ) ^ 2 - 1) := by field_simp
      _ < t * ((d : ℝ) ^ 2 - 1) := by gcongr
  nlinarith
private lemma k_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t < 1) : 0 < k d t := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 ≤ c d t := by
    rcases eq_or_lt_of_le htl with h | h
    · exact Real.sqrt_nonneg _
    · exact (c_pos hd h).le
  have hb : 0 < b t := Real.sqrt_pos.2 (by linarith)
  change 0 < (c d t - b t) / d + b t
  apply (mul_pos_iff_of_pos_right (by linarith : (0 : ℝ) < d)).mp
  rw [add_mul, div_mul_cancel₀ _ (by linarith)]; nlinarith
private lemma Itilde_sum {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    ∑ x, Itilde U t x = It t := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have ha : 2 * (a2 d t : ℂ) * (b t : ℂ) / d + (a2 d t : ℂ) ^ 2 = t := by
    exact_mod_cast a2_channel_coeff hd htl htu
  have hb : (b t : ℂ) ^ 2 = 1 - t := by exact_mod_cast b_sq htu
  apply LinearMap.ext; intro ρ
  have htr : ∑ x, Matrix.trace (ρ * Q U x) = Matrix.trace ρ := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, sum_Q U, Matrix.mul_one]
  have hmul : ∑ x, (ρ * Q U x + Q U x * ρ) = ρ + ρ := by
    rw [Finset.sum_add_distrib, ← Matrix.mul_sum, ← Matrix.sum_mul, sum_Q U,
      Matrix.mul_one, Matrix.one_mul]
  rw [LinearMap.sum_apply, It_apply]; simp_rw [Itilde_apply]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.mul_sum, htr, ← Finset.smul_sum, hmul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]; ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Nat.cast_comm, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast]
  field_simp at ha ⊢
  linear_combination ρ i j * ha + Matrix.trace ρ * (1 : Matrix (Fin d) (Fin d) ℂ) i j * hb
private lemma Itilde_trace {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1)
    (x : Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (Itilde U t x ρ) =
      Matrix.trace (ρ * Qs U (sMax d t) x) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs : (sMax d t : ℂ) = (b t : ℂ) ^ 2 + 2 * (a2 d t : ℂ) * b t / d := by
    exact_mod_cast sMax_eq hd htl htu
  have h1 : 1 - (sMax d t : ℂ) = (a2 d t : ℂ) ^ 2 := by
    exact_mod_cast one_sub_sMax_eq_a2_sq hd htl htu
  rw [Itilde_apply]
  simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul, Qs, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [Matrix.trace_mul_comm (Q U x) ρ]
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_natCast]
  rw [h1, hs]; field_simp; ring
private def choiVector {d : ℕ} (aa bb : ℝ) (x : Fin d) (p : Fin d × Fin d) : ℂ :=
  (aa : ℂ) * (if p.1 = p.2 then 1 else 0) +
    (bb : ℂ) * (if p = (x, x) then 1 else 0)
private lemma choi_of_boundary_formula {d : ℕ}
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) (aa bb : ℝ) (x : Fin d)
    (hΦ : ∀ ρ, Φ ρ = (1 / (d : ℂ)) •
      ((((bb ^ 2 : ℝ) : ℂ) * Matrix.trace
        (ρ * Q (1 : Matrix.unitaryGroup (Fin d) ℂ) x)) • 1 +
        (((aa * bb : ℝ) : ℂ) •
          (ρ * Q (1 : Matrix.unitaryGroup (Fin d) ℂ) x +
            Q (1 : Matrix.unitaryGroup (Fin d) ℂ) x * ρ)) +
        (((aa ^ 2 : ℝ) : ℂ) • ρ))) :
    MatrixMap.choi_matrix Φ = (1 / (d : ℝ)) •
      (Matrix.vecMulVec (choiVector aa bb x) (star (choiVector aa bb x)) +
        Matrix.diagonal (fun p : Fin d × Fin d =>
          if p.2 = x ∧ p.1 ≠ x then ((bb : ℂ) ^ 2) else 0)) := by
  ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  have hr : Matrix.single i₁ i₂ (1 : ℂ) * Matrix.single x x 1 =
      if i₂ = x then Matrix.single i₁ x 1 else 0 := by
    by_cases h : i₂ = x
    · subst i₂; simp
    · simpa only [if_neg h] using
        Matrix.single_mul_single_of_ne (1 : ℂ) i₁ i₂ x h (1 : ℂ)
  have hl : Matrix.single x x (1 : ℂ) * Matrix.single i₁ i₂ 1 =
      if x = i₁ then Matrix.single x i₂ 1 else 0 := by
    by_cases h : x = i₁
    · subst i₁; simp
    · simpa only [if_neg h] using
        Matrix.single_mul_single_of_ne (1 : ℂ) x x i₁ h (1 : ℂ)
  rw [MatrixMap.choi_matrix, hΦ]
  simp only [Q, OneMemClass.coe_one, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one]
  rw [Matrix.trace_mul_single, hr, hl]
  simp only [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
    Matrix.vecMulVec_apply, Pi.star_apply, choiVector,
    Matrix.diagonal_apply, Matrix.single_apply, Matrix.one_apply,
    Complex.ofReal_pow, Complex.ofReal_mul, MulOpposite.op_one, one_smul, star_add, star_mul,
    star_one, star_zero, Complex.star_def, Complex.conj_ofReal, ite_apply]
  clear hr hl hΦ Φ
  apply congrArg (fun z : ℂ => (1 / (d : ℂ)) * z)
  by_cases h₁ : i₁ = x <;> by_cases h₂ : i₂ = x <;>
    by_cases h₃ : j₁ = x <;> by_cases h₄ : j₂ = x
  all_goals
    simp [h₁, h₂, h₃, h₄, Matrix.single_apply, Prod.mk.injEq, eq_comm]
  all_goals try split_ifs
  all_goals try simp_all
  all_goals ring
private lemma choi_Itilde_standard (d : ℕ) (t : ℝ) (x : Fin d) :
    MatrixMap.choi_matrix (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) =
      (1 / (d : ℝ)) •
        (Matrix.vecMulVec (choiVector (a2 d t) (b t) x)
          (star (choiVector (a2 d t) (b t) x)) +
        Matrix.diagonal (fun p : Fin d × Fin d =>
          if p.2 = x ∧ p.1 ≠ x then ((b t : ℂ) ^ 2) else 0)) := by
  exact choi_of_boundary_formula _ _ _ x (Itilde_apply 1 t x)
private lemma choi_It_formula (d : ℕ) (t : ℝ) (j₁ i₁ j₂ i₂ : Fin d) :
    MatrixMap.choi_matrix (It (d := d) t) (j₁, i₁) (j₂, i₂) =
      (t : ℂ) * (if i₁ = j₁ ∧ i₂ = j₂ then 1 else 0) +
        (((1 - t) / (d : ℝ) : ℝ) : ℂ) *
          (if i₁ = i₂ then 1 else 0) * (if j₁ = j₂ then 1 else 0) := by
  rw [MatrixMap.choi_matrix, It_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    Matrix.one_apply]
  by_cases h : i₁ = i₂ <;> simp [h] <;> ring
private lemma Itilde_standard_cp {d : ℕ} (t : ℝ) (x : Fin d) :
    (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x).IsCompletelyPositive := by
  apply (MatrixMap.choi_PSD_iff_CP_map _).mpr; rw [choi_Itilde_standard]
  apply Matrix.PosSemidef.smul
  · apply (Matrix.posSemidef_vecMulVec_self_star _).add
    apply Matrix.PosSemidef.diagonal; intro p
    change 0 ≤ if p.2 = x ∧ p.1 ≠ x then (b t : ℂ) ^ 2 else 0
    split_ifs
    · rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (sq_nonneg (b t))
    · exact le_rfl
  · positivity
private lemma choi_competitor_psd {d : ℕ} {J : Fin d → MatrixMap (Fin d) (Fin d) ℂ}
    (x : Fin d) (hJ : (J x).IsCompletelyPositive) :
    (MatrixMap.choi_matrix (J x)).PosSemidef := by
  exact (MatrixMap.choi_PSD_iff_CP_map (J x)).mp hJ
private lemma choi_sum (d : ℕ) (t : ℝ) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hJ : ∑ x, J x = It t) :
    ∑ x, MatrixMap.choi_matrix (J x) = MatrixMap.choi_matrix (It t) := by
  have hlin : MatrixMap.choi_matrix (∑ x, J x) =
      ∑ x, MatrixMap.choi_matrix (J x) := by
    ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩; simp [MatrixMap.choi_matrix, Matrix.sum_apply, LinearMap.sum_apply]
  rw [← hJ, hlin]
private lemma trace_condition_entry {d : ℕ} {U : Matrix.unitaryGroup (Fin d) ℂ}
    {s : ℝ} {J : Fin d → MatrixMap (Fin d) (Fin d) ℂ}
    (x i₁ i₂ : Fin d)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) = Matrix.trace (ρ * Qs U s x)) :
    ∑ j : Fin d, MatrixMap.choi_matrix (J x) (j, i₁) (j, i₂) =
      Qs U s x i₂ i₁ := by
  calc
    ∑ j : Fin d, MatrixMap.choi_matrix (J x) (j, i₁) (j, i₂) =
        Matrix.trace (J x (Matrix.single i₁ i₂ 1)) := by
      simp [MatrixMap.choi_matrix, Matrix.trace]
    _ = Matrix.trace (Matrix.single i₁ i₂ 1 * Qs U s x) := htrace x _
    _ = Qs U s x i₂ i₁ := by
      simp only [Matrix.trace_single_mul, one_smul]
private lemma choi_gram_rows {d : ℕ} {C : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hC : C.PosSemidef) :
    ∃ (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      C = B.conjTranspose * B := by
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp; exact Matrix.nonneg_iff_posSemidef.mpr hC
private lemma sum_except {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (x : ι) :
    (∑ i, if i ≠ x then f i else 0) = (∑ i, f i) - f x := by
  rw [← Finset.sum_filter, Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ x)]
private lemma gram_entry_norm {d : ℕ}
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (p : Fin d × Fin d) :
    (∑ r, Complex.normSq (star (B r p))) = ((B.conjTranspose * B) p p).re := by
  have h : ((∑ r, Complex.normSq (star (B r p))) : ℂ) =
      (B.conjTranspose * B) p p := by
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
    apply Finset.sum_congr rfl; intro r hr; simp only [Complex.conj_conj]; exact mul_comm _ _
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re h
private lemma gram_diagonal_norm {d : ℕ}
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ r, Complex.normSq (∑ i, star (B r (i, i)))) =
      (∑ i, ∑ j, (B.conjTranspose * B) (i, i) (j, j)).re := by
  have hrow (r : Fin d × Fin d) :
      Complex.normSq (∑ i, star (B r (i, i))) =
        Complex.normSq (∑ i, B r (i, i)) := by
    simp only [Complex.star_def, ← map_sum, Complex.normSq_conj]
  simp_rw [hrow]
  have h : ((∑ r, Complex.normSq (∑ i, B r (i, i))) : ℂ) =
      ∑ i, ∑ j, (B.conjTranspose * B) (i, i) (j, j) := by
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, map_sum,
      Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re h
private lemma qCertificate_gram {d : ℕ} (aa bb cc : ℝ) (x : Fin d)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∑ r, qCertificate d aa bb cc x (fun j i => star (B r (j, i)))) =
      (∑ i, ∑ j, if j ≠ i then ((B.conjTranspose * B) (j, i) (j, i)).re else 0) -
      (∑ j, ((B.conjTranspose * B) (j, x) (j, x)).re) +
      ((aa + bb) / bb) * ((∑ i, ((B.conjTranspose * B) (i, i) (i, i)).re) -
        (aa / cc) * (∑ i, ∑ j, (B.conjTranspose * B) (i, i) (j, j)).re) := by
  have hoff : (∑ r, ∑ i, ∑ j,
      if i ≠ x ∧ j ≠ i then Complex.normSq (star (B r (j, i))) else 0) =
      (∑ i, ∑ j, if j ≠ i then ((B.conjTranspose * B) (j, i) (j, i)).re else 0) -
      (∑ j, if j ≠ x then ((B.conjTranspose * B) (j, x) (j, x)).re else 0) := by
    have hswap : (∑ r, ∑ i, ∑ j,
        if i ≠ x ∧ j ≠ i then Complex.normSq (star (B r (j, i))) else 0) =
        ∑ i, ∑ j, if i ≠ x ∧ j ≠ i then
          (∑ r, Complex.normSq (star (B r (j, i)))) else 0 := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [hswap]; simp_rw [gram_entry_norm, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    exact sum_except _ x
  have hcol := sum_except (fun j => ((B.conjTranspose * B) (j, x) (j, x)).re) x
  simp only [qCertificate, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hoff, Finset.sum_comm (f := fun r i => Complex.normSq (star (B r (i, i))))]
  simp_rw [gram_entry_norm]; rw [gram_diagonal_norm]; linarith
private lemma certificate_identity {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t < 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x))
    (B : Fin d → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : ∀ x, MatrixMap.choi_matrix (J x) = (B x).conjTranspose * B x) :
    (∑ x, ∑ r, qCertificate d (a2 d t) (b t) (c d t) x
      (fun j i => star (B x r (j, i)))) = 0 ∧
      (∑ x, ∑ r, Complex.normSq (∑ i, star (B x r (i, i)))) = (c d t) ^ 2 := by
  let C := fun x => MatrixMap.choi_matrix (J x)
  have hC (p q : Fin d × Fin d) :
      (∑ x, (C x p q).re) = (MatrixMap.choi_matrix (It t) p q).re := by
    have h := congrArg (fun M => (M p q).re) (choi_sum d t J hsum)
    simpa only [Matrix.sum_apply, Complex.re_sum] using h
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hD : (∑ x, ∑ i, (C x (i, i) (i, i)).re) = d * t + 1 - t := by
    rw [Finset.sum_comm]; simp_rw [hC, choi_It_formula]
    simp only [and_self, ite_true, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_one, mul_zero,
      sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring
  have hO : (∑ x, ∑ i, ∑ j, if j ≠ i then (C x (j, i) (j, i)).re else 0) =
      ((d : ℝ) - 1) * (1 - t) := by
    have hswap : (∑ x, ∑ i, ∑ j, if j ≠ i then (C x (j, i) (j, i)).re else 0) =
        ∑ i, ∑ j, if j ≠ i then (∑ x, (C x (j, i) (j, i)).re) else 0 := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [hswap]; simp_rw [hC]
    have he (i j : Fin d) : (if j ≠ i then
        (MatrixMap.choi_matrix (It t) (j, i) (j, i)).re else 0) =
        if j ≠ i then (1 - t) / d else 0 := by
      by_cases h : j = i
      · subst j; simp [choi_It_formula]
      · simp [choi_It_formula, h, Ne.symm h]
    simp_rw [he, sum_except]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring
  have hM : (∑ x, (∑ i, ∑ j, C x (i, i) (j, j)).re) = (c d t) ^ 2 := by
    simp only [Complex.re_sum]; rw [Finset.sum_comm]
    have hs (i : Fin d) : (∑ x, ∑ j, (C x (i, i) (j, j)).re) =
        ∑ j, (MatrixMap.choi_matrix (It t) (i, i) (j, j)).re := by
      rw [Finset.sum_comm]; simp_rw [hC]
    simp_rw [hs]
    have he (i j : Fin d) :
        (MatrixMap.choi_matrix (It t) (i, i) (j, j)).re =
        t + if j = i then (1 - t) / d else 0 := by
      by_cases h : j = i
      · subst j; simp [choi_It_formula]
      · simp [choi_It_formula, h, Ne.symm h]
    simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [c_sq hd htl]
    field_simp <;> ring
  have hR : (∑ x, ∑ j, (C x (j, x) (j, x)).re) =
      d * sMax d t + 1 - sMax d t := by
    have he (x : Fin d) : (∑ j, (C x (j, x) (j, x)).re) =
        sMax d t + (1 - sMax d t) / d := by
      have h := congrArg Complex.re (trace_condition_entry x x x htrace)
      simpa [C, Complex.re_sum, Qs, Q] using h
    simp_rw [he]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring
  constructor
  · simp_rw [qCertificate_gram, ← hB]
    change (∑ x, ((∑ i, ∑ j, if j ≠ i then (C x (j, i) (j, i)).re else 0) -
      (∑ j, (C x (j, x) (j, x)).re) +
      ((a2 d t + b t) / b t) * ((∑ i, (C x (i, i) (i, i)).re) -
        (a2 d t / c d t) * (∑ i, ∑ j, C x (i, i) (j, j)).re))) = 0
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hO, hR, hD, hM]
    have hb0 : b t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    have hb := b_sq (le_of_lt htu)
    have hs := sMax_eq hd htl (le_of_lt htu)
    have h1 := one_sub_sMax_eq_a2_sq hd htl (le_of_lt htu)
    have ha := a2_channel_coeff hd htl (le_of_lt htu)
    have hrel : c d t = b t + d * a2 d t := by
      change c d t = b t + d * ((c d t - b t) / d)
      field_simp <;> ring
    field_simp at ha hs
    have hds : d * t + 1 - t - a2 d t * c d t = b t * (a2 d t + b t) := by
      rw [hrel]; nlinarith only [ha, hb]
    have hrs : d * sMax d t + 1 - sMax d t =
        ((d : ℝ) - 1) * (b t) ^ 2 + (a2 d t + b t) ^ 2 := by
      nlinarith only [hs, h1]
    have hcancel : (a2 d t / c d t) * (c d t) ^ 2 = a2 d t * c d t := by
      by_cases hc0 : c d t = 0
      · simp [hc0]
      · field_simp <;> ring
    rw [hcancel, hds, hrs, ← hb]; field_simp <;> ring
  · simp_rw [gram_diagonal_norm, ← hB]
    exact hM
private def realDiagonalForm (d : ℕ) (aa bb cc : ℝ) (x : Fin d) (v : Fin d → ℝ) : ℝ :=
  ((aa + bb) / bb) * ((∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2) - v x ^ 2
private lemma real_diagonal_shift {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 ≤ cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (v : Fin d → ℝ)
    (horth : cc = 0 → ∑ i, v i = 0) :
    realDiagonalForm d aa bb cc x v =
      ((aa + bb) / bb) *
        ((∑ i, (v i - (v x / (aa + bb)) * (aa + if i = x then bb else 0)) ^ 2) -
          (aa / cc) * (∑ i, (v i - (v x / (aa + bb)) *
            (aa + if i = x then bb else 0))) ^ 2) := by
  let u : Fin d → ℝ := fun i => aa + if i = x then bb else 0
  let r : ℝ := v x / (aa + bb)
  let z : Fin d → ℝ := fun i => v i - r * u i
  have hu : ∑ i, u i = cc := by
    dsimp [u]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linarith
  have huv : ∑ i, v i * u i = aa * (∑ i, v i) + bb * v x := by
    dsimp [u]
    simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have huu : ∑ i, u i ^ 2 = aa * cc + bb * (aa + bb) := by
    have heach (i : Fin d) : u i ^ 2 = aa ^ 2 +
        (2 * aa * bb + bb ^ 2) * (if i = x then 1 else 0) := by
      dsimp [u]
      split_ifs <;> ring
    simp_rw [heach]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hc]; ring
  have hzsum : ∑ i, z i = (∑ i, v i) - r * cc := by
    dsimp [z]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hu]
  have hzsq : ∑ i, z i ^ 2 = (∑ i, v i ^ 2) -
      2 * r * (aa * (∑ i, v i) + bb * v x) +
      r ^ 2 * (aa * cc + bb * (aa + bb)) := by
    have heach (i : Fin d) : z i ^ 2 = v i ^ 2 -
        (2 * r) * (v i * u i) + r ^ 2 * u i ^ 2 := by dsimp [z]; ring
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, huv, huu]
  change realDiagonalForm d aa bb cc x v =
    ((aa + bb) / bb) * ((∑ i, z i ^ 2) - (aa / cc) * (∑ i, z i) ^ 2)
  rw [hzsum, hzsq]; dsimp [realDiagonalForm, r]
  have hb0 := ne_of_gt hbb
  have hk0 := ne_of_gt hkk
  by_cases hc0 : cc = 0
  · have hs := horth hc0
    simp only [hc0, hs, div_zero, mul_zero, zero_mul, zero_add, add_zero, sub_zero]
    field_simp <;> ring
  · field_simp <;> ring
private lemma diagonal_energy {d : ℕ} {aa bb cc : ℝ}
    (hbb : 0 < bb) (hcc : 0 ≤ cc) (hc : cc = bb + d * aa) (v : Fin d → ℝ) :
    0 ≤ (∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2 ∧
      (((∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2) = 0 → ∀ i, v i = 0) := by
  by_cases hc0 : cc = 0
  · simp only [hc0, div_zero, zero_mul, sub_zero]
    refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg (v i)), ?_⟩
    intro hz i
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (v i))).mp hz i (Finset.mem_univ i))
  have hcc : 0 < cc := lt_of_le_of_ne hcc (Ne.symm hc0)
  let N : ℝ := ∑ i, v i ^ 2
  let S : ℝ := ∑ i, v i
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : S ^ 2 ≤ d * N := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun _ => (1 : ℝ))
    simpa [N, S, mul_comm] using h
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * N ≤ N - (aa / cc) * S ^ 2 := by
    by_cases haa : 0 ≤ aa
    · refine ⟨bb / cc, div_pos hbb hcc, ?_⟩
      have hid : N - (aa / cc) * S ^ 2 = (cc * N - aa * S ^ 2) / cc := by
        field_simp <;> ring
      rw [hid, div_mul_eq_mul_div]; apply (div_le_div_iff_of_pos_right hcc).mpr; rw [hc]
      nlinarith [mul_nonneg haa (sub_nonneg.mpr hcs)]
    · refine ⟨1, zero_lt_one, ?_⟩
      have ha : aa / cc ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge haa) hcc.le
      have hp := mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg S)
      linarith
  have hE : 0 ≤ N - (aa / cc) * S ^ 2 :=
    le_trans (mul_nonneg hδ.le hN) hbound
  refine ⟨hE, ?_⟩
  intro hzero i
  have hmul : δ * N = 0 := le_antisymm (by linarith) (mul_nonneg hδ.le hN)
  have hNz : N = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hδ)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp hNz i
    (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi
private lemma real_diagonal_nonneg {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 ≤ cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (v : Fin d → ℝ)
    (horth : cc = 0 → ∑ i, v i = 0) :
    0 ≤ realDiagonalForm d aa bb cc x v ∧
      (realDiagonalForm d aa bb cc x v = 0 →
        ∀ i, v i = (v x / (aa + bb)) * (aa + if i = x then bb else 0)) := by
  let z : Fin d → ℝ := fun i => v i - (v x / (aa + bb)) *
    (aa + if i = x then bb else 0)
  have he := diagonal_energy hbb hcc hc z
  have hs := real_diagonal_shift x hbb hcc hkk hc v horth
  change realDiagonalForm d aa bb cc x v =
    ((aa + bb) / bb) * ((∑ i, z i ^ 2) - (aa / cc) * (∑ i, z i) ^ 2) at hs
  have hp : 0 < (aa + bb) / bb := div_pos hkk hbb
  constructor
  · rw [hs]
    exact mul_nonneg hp.le he.1
  · intro hz i
    rw [hs] at hz
    have hE := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
    exact sub_eq_zero.mp (he.2 hE i)
private lemma qCertificate_decomposition {d : ℕ} (aa bb cc : ℝ) (x : Fin d)
    (w : Matrix (Fin d) (Fin d) ℂ) :
    qCertificate d aa bb cc x w =
      (∑ k', ∑ j, if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0) +
        realDiagonalForm d aa bb cc x (fun i => (w i i).re) +
        realDiagonalForm d aa bb cc x (fun i => (w i i).im) := by
  simp only [qCertificate, realDiagonalForm, Complex.normSq_apply, Complex.re_sum,
    Complex.im_sum, Finset.sum_add_distrib, pow_two]
  ring
private lemma qCertificate_nonneg {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 ≤ cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (w : Matrix (Fin d) (Fin d) ℂ)
    (horth : cc = 0 → ∑ i, w i i = 0) :
    0 ≤ qCertificate d aa bb cc x w := by
  have hre : cc = 0 → ∑ i, (w i i).re = 0 := by
    intro h; simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re (horth h)
  have him : cc = 0 → ∑ i, (w i i).im = 0 := by
    intro h; simpa only [Complex.im_sum, Complex.zero_im] using congrArg Complex.im (horth h)
  have hoff : 0 ≤ ∑ k', ∑ j,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 := by
    apply Finset.sum_nonneg; intro k' hk'; apply Finset.sum_nonneg; intro j hj
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  rw [qCertificate_decomposition]
  exact add_nonneg (add_nonneg hoff
    (real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).re) hre).1)
    (real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).im) him).1
private lemma qCertificate_eq_zero {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 ≤ cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (w : Matrix (Fin d) (Fin d) ℂ)
    (horth : cc = 0 → ∑ i, w i i = 0)
    (hzero : qCertificate d aa bb cc x w = 0) :
    (∀ k' j, k' ≠ x → j ≠ k' → w j k' = 0) ∧
      (∀ i, w i i = (w x x / ((aa + bb : ℝ) : ℂ)) *
        ((aa + if i = x then bb else 0 : ℝ) : ℂ)) := by
  have hre : cc = 0 → ∑ i, (w i i).re = 0 := by
    intro h; simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re (horth h)
  have him : cc = 0 → ∑ i, (w i i).im = 0 := by
    intro h; simpa only [Complex.im_sum, Complex.zero_im] using congrArg Complex.im (horth h)
  have hterm (k' j : Fin d) :
      0 ≤ if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 := by
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  have hoff : 0 ≤ ∑ k', ∑ j,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 :=
    Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun j _ => hterm k' j
  have hr := real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).re) hre
  have hi := real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).im) him
  rw [qCertificate_decomposition] at hzero
  have hrz : realDiagonalForm d aa bb cc x (fun i => (w i i).re) = 0 := by linarith [hr.1, hi.1]
  have hiz : realDiagonalForm d aa bb cc x (fun i => (w i i).im) = 0 := by linarith [hr.1, hi.1]
  have hoz : (∑ k', ∑ j,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0) = 0 := by linarith
  constructor
  · intro k' j hk' hj
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k' _ => Finset.sum_nonneg fun j _ => hterm k' j)).mp hoz k' (Finset.mem_univ k')
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm k' j)).mp hz j
      (Finset.mem_univ j)
    apply Complex.normSq_eq_zero.mp
    simpa only [if_pos (And.intro hk' hj)] using hz'
  · intro i
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.div_ofReal_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using hr.2 hrz i
    · simpa only [Complex.mul_im, Complex.div_ofReal_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add] using hi.2 hiz i
private lemma support_rows {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t < 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x))
    (B : Fin d → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : ∀ x, MatrixMap.choi_matrix (J x) = (B x).conjTranspose * B x) :
    ∀ x r, (∀ k' j, k' ≠ x → j ≠ k' → B x r (j, k') = 0) ∧
      (∀ i, star (B x r (i, i)) =
        (star (B x r (x, x)) / ((a2 d t + b t : ℝ) : ℂ)) *
          ((a2 d t + if i = x then b t else 0 : ℝ) : ℂ)) := by
  have hb : 0 < b t := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 ≤ c d t := Real.sqrt_nonneg _
  have hk : 0 < a2 d t + b t := k_pos hd htl htu
  have hrel : c d t = b t + d * a2 d t := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    change c d t = b t + d * ((c d t - b t) / d)
    field_simp <;> ring
  have htotal := certificate_identity hd htl htu J hsum htrace B hB
  have horth (x : Fin d) (r : Fin d × Fin d) (hc0 : c d t = 0) :
      (∑ i, star (B x r (i, i))) = 0 := by
    have hω : (∑ x, ∑ r, Complex.normSq (∑ i, star (B x r (i, i)))) = 0 := by
      simpa [hc0] using htotal.2
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      Finset.sum_nonneg fun r _ => Complex.normSq_nonneg _)).mp hω x (Finset.mem_univ x)
    have hr := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ =>
      Complex.normSq_nonneg _)).mp hx r (Finset.mem_univ r)
    exact Complex.normSq_eq_zero.mp hr
  have hnonneg (x : Fin d) (r : Fin d × Fin d) :
      0 ≤ qCertificate d (a2 d t) (b t) (c d t) x
        (fun j i => star (B x r (j, i))) :=
    qCertificate_nonneg x hb hc hk hrel _ (horth x r)
  intro x r
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun r _ => hnonneg x r)).mp htotal.1 x (Finset.mem_univ x)
  have hr := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r _ => hnonneg x r)).mp hx r (Finset.mem_univ r)
  obtain ⟨hoff, hdiag⟩ := qCertificate_eq_zero x hb hc hk hrel _ (horth x r) hr
  refine ⟨?_, hdiag⟩
  intro k' j hk' hj; exact star_eq_zero.mp (hoff k' j hk' hj)
private lemma elimination_standard {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t < 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x := by
  choose B hB using fun x => choi_gram_rows (choi_competitor_psd x (hCP x))
  have hS := support_rows hd htl htu J hsum htrace B hB
  let C := fun x => MatrixMap.choi_matrix (J x)
  let A := fun x => MatrixMap.choi_matrix (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x)
  have hCzero (x j i : Fin d) (q : Fin d × Fin d) (hji : j ≠ i) (hix : i ≠ x) :
      C x (j, i) q = 0 := by
    change MatrixMap.choi_matrix (J x) (j, i) q = 0; rw [hB x]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]; apply Finset.sum_eq_zero; intro r hr
    rw [(hS x r).1 i j hix hji, star_zero, zero_mul]
  have hAzero (x j i : Fin d) (q : Fin d × Fin d) (hji : j ≠ i) (hix : i ≠ x) :
      A x (j, i) q = 0 := by
    dsimp [A]; rw [choi_Itilde_standard]
    simp [Matrix.smul_apply, Matrix.vecMulVec_apply, choiVector, hji, hix,
      Matrix.diagonal_apply, Prod.mk.injEq]
  have hOff (x j i : Fin d) (q : Fin d × Fin d) (hji : j ≠ i) :
      C x (j, i) q = A x (j, i) q := by
    by_cases hix : i = x
    · subst i
      have hc := congrArg (fun M => M (j, x) q) (choi_sum d t J hsum)
      have ha := congrArg (fun M => M (j, x) q)
        (choi_sum d t (Itilde 1 t) (Itilde_sum hd 1 htl htu.le))
      simp only [Matrix.sum_apply] at hc ha
      have hcx : (∑ y, C y (j, x) q) = C x (j, x) q := by
        apply Finset.sum_eq_single x
        · intro y hy hyx; exact hCzero y j x q hji (Ne.symm hyx)
        · simp
      have hax : (∑ y, A y (j, x) q) = A x (j, x) q := by
        apply Finset.sum_eq_single x
        · intro y hy hyx; exact hAzero y j x q hji (Ne.symm hyx)
        · simp
      exact hcx.symm.trans (hc.trans (ha.symm.trans hax))
    · rw [hCzero x j i q hji hix, hAzero x j i q hji hix]
  have hxx (x : Fin d) : C x (x, x) (x, x) = A x (x, x) (x, x) := by
    have hc := trace_condition_entry x x x htrace
    have ha := trace_condition_entry x x x
      (fun x ρ => Itilde_trace hd 1 htl htu.le x ρ)
    have hz : (∑ j, (C x (j, x) (j, x) - A x (j, x) (j, x))) = 0 := by
      rw [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr (hc.trans ha.symm)
    have he : (∑ j, (C x (j, x) (j, x) - A x (j, x) (j, x))) =
        C x (x, x) (x, x) - A x (x, x) (x, x) := by
      apply Finset.sum_eq_single x
      · intro j hj hjx; rw [hOff x j x (j, x) hjx, sub_self]
      · simp
    exact sub_eq_zero.mp (he.symm.trans hz)
  let v := fun x i : Fin d => ((a2 d t + if i = x then b t else 0 : ℝ) : ℂ)
  let kk : ℂ := ((a2 d t + b t : ℝ) : ℂ)
  have hk : kk ≠ 0 := by
    have hkr : a2 d t + b t ≠ 0 := ne_of_gt (k_pos hd htl htu)
    dsimp [kk]
    exact_mod_cast hkr
  have hDiag (x i j : Fin d) :
      C x (i, i) (j, j) = C x (x, x) (x, x) * (v x i / kk) * (v x j / kk) := by
    change MatrixMap.choi_matrix (J x) (i, i) (j, j) =
      MatrixMap.choi_matrix (J x) (x, x) (x, x) * _ * _
    rw [hB x]; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_congr rfl; intro r hr
    have hi := (hS x r).2 i
    have hj : B x r (j, j) = (B x r (x, x) / kk) * v x j := by
      simpa [v, kk, Complex.star_def] using congrArg star ((hS x r).2 j)
    rw [hi, hj]; dsimp [v, kk]; ring
  have hAv (x i j : Fin d) : A x (i, i) (j, j) = (1 / (d : ℂ)) * v x i * v x j := by
    have hv (x i : Fin d) : choiVector (a2 d t) (b t) x (i, i) = v x i := by
      by_cases h : i = x <;> simp [choiVector, v, h]
    dsimp [A]; rw [choi_Itilde_standard]
    simp [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.diagonal_apply, hv, Complex.real_smul, v]
    <;> ring
  intro x; apply MatrixMap.choi_matrix_inj; change C x = A x; ext ⟨j, i⟩ ⟨l, k'⟩
  by_cases hji : j = i
  · subst j
    by_cases hlk : l = k'
    · subst l
      rw [hDiag, hxx, hAv, hAv]
      have hvx : v x x = kk := by simp [v, kk]
      rw [hvx]
      field_simp <;> ring
    · have hc := (choi_competitor_psd x (hCP x)).isHermitian
      have ha := ((MatrixMap.choi_PSD_iff_CP_map _).mp (Itilde_standard_cp t x)).isHermitian
      exact (hc.apply _ _).symm.trans
        ((congrArg star (hOff x l k' (i, i) hlk)).trans (ha.apply _ _))
  · exact hOff x j i (l, k') hji
private lemma lower_endpoint_standard {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It (-1 / ((d : ℝ) ^ 2 - 1)))
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ)
        (sMax d (-1 / ((d : ℝ) ^ 2 - 1))) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ)
      (-1 / ((d : ℝ) ^ 2 - 1)) x := by
  apply elimination_standard hd le_rfl ?_ J hCP hsum htrace
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hn : -1 / ((d : ℝ) ^ 2 - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) hden
  linarith
private lemma upper_endpoint_standard {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It 1)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d 1) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) 1 x := by
  let C := fun x => MatrixMap.choi_matrix (J x)
  have hC (x : Fin d) : (C x).PosSemidef := choi_competitor_psd x (hCP x)
  have hsumC := choi_sum d 1 J hsum
  have hker (v : (Fin d × Fin d) → ℂ)
      (hv : Matrix.mulVec (MatrixMap.choi_matrix (It (d := d) 1)) v = 0) (x : Fin d) :
      Matrix.mulVec (C x) v = 0 := by
    apply (hC x).dotProduct_mulVec_zero_iff.mp
    have hz : (∑ y, dotProduct (star v) (Matrix.mulVec (C y) v)) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec]
      change dotProduct (star v) (Matrix.mulVec (∑ y, MatrixMap.choi_matrix (J y)) v) = 0
      rw [hsumC, hv, dotProduct_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => (hC y).dotProduct_mulVec_nonneg v)).mp hz x (Finset.mem_univ x)
  have hoff (x : Fin d) (p q : Fin d × Fin d) (hp : p.1 ≠ p.2) : C x q p = 0 := by
    rcases p with ⟨l, k'⟩
    have hv : Matrix.mulVec (MatrixMap.choi_matrix (It (d := d) 1))
        (Pi.single (l, k') 1) = 0 := by
      ext ⟨j, i⟩; simp [Matrix.mulVec_single_one, choi_It_formula, hp, Ne.symm hp]
    simpa [Matrix.mulVec_single_one] using congrFun (hker _ hv x) q
  have hdiag (x i j : Fin d) (q : Fin d × Fin d) : C x q (i, i) = C x q (j, j) := by
    have hv : Matrix.mulVec (MatrixMap.choi_matrix (It (d := d) 1))
        (Pi.single (i, i) 1 - Pi.single (j, j) 1) = 0 := by
      ext ⟨j, k'⟩; simp [Matrix.mulVec_sub, Matrix.mulVec_single_one, choi_It_formula]
    apply sub_eq_zero.mp
    simpa [Matrix.mulVec_sub, Matrix.mulVec_single_one] using congrFun (hker _ hv x) q
  have hs : sMax d 1 = 0 := by unfold sMax; ring_nf; simp
  have hxx (x : Fin d) : C x (x, x) (x, x) = 1 / (d : ℂ) := by
    have h := trace_condition_entry x x x htrace
    have he : (∑ j, C x (j, x) (j, x)) = C x (x, x) (x, x) := by
      apply Finset.sum_eq_single x
      · intro j hj hjx; exact hoff x (j, x) (j, x) hjx
      · simp
    rw [he] at h
    simpa [Qs, hs] using h
  have ha : a2 d 1 = 1 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    simp [a2, Real.sqrt_sq_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ d from Nat.cast_nonneg d), hd0]
  intro x; apply MatrixMap.choi_matrix_inj; ext ⟨j, i⟩ ⟨l, k'⟩
  have he : C x (j, i) (l, k') =
      if j = i ∧ l = k' then (1 / (d : ℂ)) else 0 := by
    by_cases hji : j = i
    · subst j
      by_cases hlk : l = k'
      · subst l
        simp only [and_self, ite_true]
        calc C x (i, i) (k', k') = C x (i, i) (x, x) := hdiag x k' x _
          _ = star (C x (x, x) (i, i)) := ((hC x).isHermitian.apply _ _).symm
          _ = star (C x (x, x) (x, x)) := congrArg star (hdiag x i x _)
          _ = C x (x, x) (x, x) := (hC x).isHermitian.apply _ _
          _ = _ := hxx x
      · simp only [hlk, and_false, ite_false]
        exact hoff x (l, k') (i, i) hlk
    · simp only [hji, false_and, ite_false]
      rw [← (hC x).isHermitian.apply]; rw [hoff x (j, i) (l, k') hji, star_zero]
  change C x (j, i) (l, k') = _; rw [he, choi_Itilde_standard]
  simp [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, choiVector,
    ha, b, Complex.real_smul, Matrix.diagonal_apply, ite_and]
  <;> split_ifs <;> simp_all
private lemma standard_basis_forward {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x := by
  by_cases hl : t = -1 / ((d : ℝ) ^ 2 - 1)
  · subst t
    exact lower_endpoint_standard hd J hCP hsum htrace
  by_cases hu : t = 1
  · subst t
    exact upper_endpoint_standard hd J hCP hsum htrace
  exact elimination_standard hd htl
    (lt_of_le_of_ne htu hu) J hCP hsum htrace
private def transformMap {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := W * Φ (W.conjTranspose * ρ * W) * W.conjTranspose
  map_add' ρ σ := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' z ρ := by simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]
private lemma transformMap_apply {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    transformMap W Φ ρ = W * Φ (W.conjTranspose * ρ * W) * W.conjTranspose := rfl
private lemma transformMap_cp {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) (hΦ : Φ.IsCompletelyPositive) :
    (transformMap W Φ).IsCompletelyPositive := by
  obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hΦ
  have hmap : transformMap W (MatrixMap.of_kraus K K) =
      MatrixMap.of_kraus (fun r => W * K r * W.conjTranspose)
        (fun r => W * K r * W.conjTranspose) := by
    apply LinearMap.ext; intro ρ; rw [transformMap_apply]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl; intro r hr
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hmap]; exact MatrixMap.of_kraus_isCompletelyPositive _
private lemma Itilde_transform {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (t : ℝ) (x : Fin d) :
    transformMap (U : Matrix (Fin d) (Fin d) ℂ)
      (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) = Itilde U t x := by
  have hUV : (U : Matrix (Fin d) (Fin d) ℂ) *
      (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  apply LinearMap.ext; intro ρ
  let W : Matrix (Fin d) (Fin d) ℂ := U
  let V := W.conjTranspose
  let P := Matrix.single x x (1 : ℂ)
  let Y := V * ρ * W
  have hWV : W * V = 1 := hUV
  have hWY : W * Y = ρ * W := by
    dsimp [Y]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
  have hYV : Y * V = V * ρ := by
    dsimp [Y]; rw [Matrix.mul_assoc, Matrix.mul_assoc, hWV, Matrix.mul_one]
  have hYP : W * (Y * P) * V = ρ * (W * P * V) := by
    calc
      _ = (W * Y) * (P * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWY]; simp only [Matrix.mul_assoc]
  have hPY : W * (P * Y) * V = (W * P * V) * ρ := by
    calc
      _ = W * P * (Y * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hYV]; simp only [Matrix.mul_assoc]
  have hY : W * Y * V = ρ := by
    rw [hWY, Matrix.mul_assoc, hWV, Matrix.mul_one]
  have htr : Matrix.trace (Y * P) = Matrix.trace (ρ * (W * P * V)) := by
    change Matrix.trace (V * ρ * W * P) = _
    rw [Matrix.mul_assoc (V * ρ) W P, Matrix.trace_mul_cycle V ρ (W * P),
      Matrix.trace_mul_comm (W * P * V) ρ]
  rw [transformMap_apply, Itilde_apply, Itilde_apply]
  change W * ((1 / (d : ℂ)) •
    (((((b t) ^ 2 : ℝ) : ℂ) * Matrix.trace (Y * Q 1 x)) • 1 +
      (((a2 d t * b t : ℝ) : ℂ) • (Y * Q 1 x + Q 1 x * Y)) +
      (((a2 d t) ^ 2 : ℝ) : ℂ) • Y)) * V = _
  have hQ1 : Q (1 : Matrix.unitaryGroup (Fin d) ℂ) x = P := by
    simp only [Q, OneMemClass.coe_one, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, P]
  have hQU : Q U x = W * P * V := rfl
  rw [hQ1, hQU]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one]
  rw [hWV, hYP, hPY, hY, htr]
private lemma transport_forward {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) = Matrix.trace (ρ * Qs U (sMax d t) x)) :
    ∀ x, J x = Itilde U t x := by
  let W : Matrix (Fin d) (Fin d) ℂ := U
  let V := W.conjTranspose
  have hWV : W * V = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hVW : V * W = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hc (ρ : Matrix (Fin d) (Fin d) ℂ) : V * (W * ρ * V) * W = ρ := by
    calc _ = (V * W) * ρ * (V * W) := by simp only [Matrix.mul_assoc]
         _ = ρ := by rw [hVW]; simp
  have hc' (ρ : Matrix (Fin d) (Fin d) ℂ) : W * (V * ρ * W) * V = ρ := by
    calc _ = (W * V) * ρ * (W * V) := by simp only [Matrix.mul_assoc]
         _ = ρ := by rw [hWV]; simp
  have ht (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace (W * ρ * V) = Matrix.trace ρ := by
    rw [Matrix.trace_mul_cycle, hVW, Matrix.one_mul]
  have ht' (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace (V * ρ * W) = Matrix.trace ρ := by
    rw [Matrix.trace_mul_cycle, hWV, Matrix.one_mul]
  let J' := fun x => transformMap V (J x)
  have hCP' (x : Fin d) : (J' x).IsCompletelyPositive := transformMap_cp V (J x) (hCP x)
  have hsum' : ∑ x, J' x = It t := by
    apply LinearMap.ext; intro ρ
    simp only [LinearMap.sum_apply, J', V, transformMap_apply,
      Matrix.conjTranspose_conjTranspose]
    change (∑ x, V * J x (W * ρ * V) * W) = It t ρ
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← LinearMap.sum_apply, hsum,
      It_apply, It_apply]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc, ht, Matrix.mul_one, hVW]
  have hQs (s : ℝ) (x : Fin d) :
      Qs U s x = W * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) s x * V := by
    simp only [Qs, Q, OneMemClass.coe_one, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul]
    change (s : ℂ) • (W * Matrix.single x x 1 * V) + _ =
      (s : ℂ) • (W * Matrix.single x x 1 * V) + _
    rw [hWV]
  have htrace' (x : Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
      Matrix.trace (J' x ρ) = Matrix.trace (ρ * Qs 1 (sMax d t) x) := by
    simp only [J', V, transformMap_apply, Matrix.conjTranspose_conjTranspose]
    change Matrix.trace (V * J x (W * ρ * V) * W) = _; rw [ht', htrace, hQs]
    have hp (σ : Matrix (Fin d) (Fin d) ℂ) :
        (W * ρ * V) * (W * σ * V) = W * (ρ * σ) * V := by
      calc _ = W * ρ * (V * W) * σ * V := by simp only [Matrix.mul_assoc]
           _ = _ := by rw [hVW]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [hp, ht]
  have hstd := standard_basis_forward hd htl htu J' hCP' hsum' htrace'
  intro x
  have hinv : transformMap W (J' x) = J x := by
    apply LinearMap.ext; intro ρ
    simp only [J', V, transformMap_apply, Matrix.conjTranspose_conjTranspose]
    change W * (V * J x (W * (V * ρ * W) * V) * W) * V = J x ρ; rw [hc', hc']
  rw [← hinv, hstd x]; exact Itilde_transform U t x
private lemma Itilde_cp {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    ∀ x, (Itilde U t x).IsCompletelyPositive := by
  intro x; rw [← Itilde_transform U t x]; exact transformMap_cp _ _ (Itilde_standard_cp t x)
private lemma backward_direction {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (t : ℝ) (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    (∀ x, (Itilde U t x).IsCompletelyPositive) ∧
      (∑ x, Itilde U t x = It t) ∧
      (∀ x ρ, Matrix.trace (Itilde U t x ρ) =
        Matrix.trace (ρ * Qs U (sMax d t) x)) := by
  refine ⟨Itilde_cp hd U htl htu, Itilde_sum hd U htl htu, ?_⟩
  intro x ρ; exact Itilde_trace hd U htl htu x ρ
theorem result : claim := by
  intro d hd U t htl htu J
  constructor
  · rintro ⟨hCP, hsum, htrace⟩
    exact transport_forward hd U htl htu J hCP hsum htrace
  · intro hJ
    have hJEq : J = Itilde U t := funext hJ
    subst J; exact backward_direction hd U t htl htu

end D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
