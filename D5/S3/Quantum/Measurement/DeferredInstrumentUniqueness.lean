/- GID: D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal upper-boundary meter, channel, instrument, and uniqueness claim. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

def Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.single x x (1 : ℂ) *
    (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose

def Qs {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (s : ℝ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (s : ℂ) • Q U x + (((1 - s) / (d : ℝ) : ℝ) : ℂ) • 1

def It {d : ℕ} (t : ℝ) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := (t : ℂ) • ρ +
    ((((1 - t) / (d : ℝ) : ℝ) : ℂ) * Matrix.trace ρ) • 1
  map_add' ρ σ := by
    ext i j
    simp only [Matrix.trace_add, smul_add, add_smul, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply]
    ring_nf
  map_smul' c ρ := by
    ext i j
    simp [Matrix.trace_smul, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> ring

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

end D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness

namespace D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

/-- The auxiliary square-root coordinate appearing in the Choi certificate. -/
def c (d : ℕ) (t : ℝ) : ℝ := Real.sqrt (t * ((d : ℝ) ^ 2 - 1) + 1)

/-- The coefficient of the distinguished diagonal vector. -/
def a (d : ℕ) (t : ℝ) : ℝ := a2 d t

/-- The distinguished diagonal coefficient. -/
def k (d : ℕ) (t : ℝ) : ℝ := a d t + b t

lemma It_apply {d : ℕ} (t : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    It t ρ = (t : ℂ) • ρ +
      (((((1 - t) / (d : ℝ)) : ℝ) : ℂ) * Matrix.trace ρ) • 1 := rfl

lemma Itilde_apply {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (t : ℝ)
    (x : Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Itilde U t x ρ = (1 / (d : ℂ)) •
      (((((b t) ^ 2 : ℝ) : ℂ) * Matrix.trace (ρ * Q U x)) • 1 +
        (((a2 d t * b t : ℝ) : ℂ) • (ρ * Q U x + Q U x * ρ)) +
        (((a2 d t) ^ 2 : ℝ) : ℂ) • ρ) := rfl

lemma sum_Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ x, Q U x = 1 := by
  unfold Q
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp U.2

/-- The quadratic certificate used in the standard-basis argument. -/
def qCertificate (d : ℕ) (aa bb cc : ℝ) (x : Fin d)
    (w : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ k' : Fin d, ∑ j : Fin d,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0) +
    ((aa + bb) / bb) *
      ((∑ i : Fin d, Complex.normSq (w i i)) -
        (aa / cc) * Complex.normSq (∑ i : Fin d, w i i)) -
    Complex.normSq (w x x)

lemma b_sq {t : ℝ} (ht : t ≤ 1) : (b t) ^ 2 = 1 - t := by
  rw [b, Real.sq_sqrt]
  linarith

lemma c_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (ht : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) :
    (c d t) ^ 2 = t * ((d : ℝ) ^ 2 - 1) + 1 := by
  rw [c, Real.sq_sqrt]
  have hd' : 0 < (d : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hden : 0 < (d : ℝ) ^ 2 - 1 := hd'
  have hm := mul_le_mul_of_nonneg_right ht (le_of_lt hd')
  have hm' : -1 ≤ t * ((d : ℝ) ^ 2 - 1) := by
    convert hm using 1 <;> field_simp
  nlinarith

lemma bc_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    (b t * c d t) ^ 2 = (1 - (d : ℝ) ^ 2) * t ^ 2 +
      ((d : ℝ) ^ 2 - 2) * t + 1 := by
  rw [mul_pow, b_sq htu, c_sq hd htl]
  ring

lemma a2_channel_coeff {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    2 * a2 d t * b t / d + (a2 d t) ^ 2 = t := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hb := b_sq htu
  have hc := c_sq hd htl
  dsimp [a2]
  change 2 * ((c d t - b t) / d) * b t / d + ((c d t - b t) / d) ^ 2 = t
  field_simp
  nlinarith [c_sq hd htl, hb]

lemma sMax_eq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    sMax d t = b t ^ 2 + 2 * a2 d t * b t / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hb : 0 ≤ b t := Real.sqrt_nonneg _
  have hc : 0 ≤ c d t := Real.sqrt_nonneg _
  have hbc : 0 ≤ b t * c d t := mul_nonneg hb hc
  have hD : 0 ≤ (1 - (d : ℝ) ^ 2) * t ^ 2 + ((d : ℝ) ^ 2 - 2) * t + 1 := by
    rw [← bc_sq hd htl htu]
    positivity
  have hroot : Real.sqrt ((1 - (d : ℝ) ^ 2) * t ^ 2 +
      ((d : ℝ) ^ 2 - 2) * t + 1) = b t * c d t := by
    have hs := Real.sq_sqrt hD
    have hbcs := bc_sq hd htl htu
    have hr := Real.sqrt_nonneg ((1 - (d : ℝ) ^ 2) * t ^ 2 +
      ((d : ℝ) ^ 2 - 2) * t + 1)
    nlinarith
  rw [sMax, hroot]
  have hb' : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  dsimp [a2, c, b]
  rw [hb']
  field_simp
  nlinarith [hb']

lemma one_sub_sMax_eq_a2_sq {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    1 - sMax d t = (a2 d t) ^ 2 := by
  rw [sMax_eq hd htl htu]
  have hb' : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hc' : (Real.sqrt (t * ((d : ℝ) ^ 2 - 1) + 1)) ^ 2 =
      t * ((d : ℝ) ^ 2 - 1) + 1 := c_sq hd htl
  dsimp [a2, c, b]
  field_simp
  nlinarith [hb', hc']

lemma c_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (ht : -1 / ((d : ℝ) ^ 2 - 1) < t) : 0 < c d t := by
  unfold c
  apply Real.sqrt_pos.2
  have hd' : 0 < (d : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have : -1 < t * ((d : ℝ) ^ 2 - 1) := by
    calc
      -1 = (-1 / ((d : ℝ) ^ 2 - 1)) * ((d : ℝ) ^ 2 - 1) := by field_simp
      _ < t * ((d : ℝ) ^ 2 - 1) := by gcongr
  nlinarith

lemma k_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) < t) (htu : t < 1) : 0 < k d t := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := c_pos hd htl
  have hb : 0 < b t := Real.sqrt_pos.2 (by linarith)
  change 0 < (c d t - b t) / d + b t
  apply (mul_pos_iff_of_pos_right (by linarith : (0 : ℝ) < d)).mp
  rw [add_mul, div_mul_cancel₀ _ (by linarith)]
  nlinarith

lemma Itilde_sum {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    ∑ x, Itilde U t x = It t := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have ha : 2 * (a2 d t : ℂ) * (b t : ℂ) / d + (a2 d t : ℂ) ^ 2 = t := by
    exact_mod_cast a2_channel_coeff hd htl htu
  have hb : (b t : ℂ) ^ 2 = 1 - t := by exact_mod_cast b_sq htu
  apply LinearMap.ext
  intro ρ
  have htr : ∑ x, Matrix.trace (ρ * Q U x) = Matrix.trace ρ := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, sum_Q U, Matrix.mul_one]
  have hmul : ∑ x, (ρ * Q U x + Q U x * ρ) = ρ + ρ := by
    rw [Finset.sum_add_distrib, ← Matrix.mul_sum, ← Matrix.sum_mul, sum_Q U,
      Matrix.mul_one, Matrix.one_mul]
  rw [LinearMap.sum_apply, It_apply]
  simp_rw [Itilde_apply]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.mul_sum, htr, ← Finset.smul_sum, hmul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Nat.cast_comm, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast]
  field_simp at ha ⊢
  linear_combination ρ i j * ha + Matrix.trace ρ * (1 : Matrix (Fin d) (Fin d) ℂ) i j * hb

lemma Itilde_trace {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
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
  rw [h1, hs]
  field_simp
  ring

def choiVector {d : ℕ} (aa bb : ℝ) (x : Fin d) (p : Fin d × Fin d) : ℂ :=
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

lemma choi_Itilde_standard (d : ℕ) (t : ℝ) (x : Fin d) :
    MatrixMap.choi_matrix (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) =
      (1 / (d : ℝ)) •
        (Matrix.vecMulVec (choiVector (a2 d t) (b t) x)
          (star (choiVector (a2 d t) (b t) x)) +
        Matrix.diagonal (fun p : Fin d × Fin d =>
          if p.2 = x ∧ p.1 ≠ x then ((b t : ℂ) ^ 2) else 0)) := by
  exact choi_of_boundary_formula _ _ _ x (Itilde_apply 1 t x)

lemma choi_It_formula (d : ℕ) (t : ℝ) (j₁ i₁ j₂ i₂ : Fin d) :
    MatrixMap.choi_matrix (It (d := d) t) (j₁, i₁) (j₂, i₂) =
      (t : ℂ) * (if i₁ = j₁ ∧ i₂ = j₂ then 1 else 0) +
        (((1 - t) / (d : ℝ) : ℝ) : ℂ) *
          (if i₁ = i₂ then 1 else 0) * (if j₁ = j₂ then 1 else 0) := by
  rw [MatrixMap.choi_matrix, It_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    Matrix.one_apply]
  by_cases h : i₁ = i₂ <;> simp [h] <;> ring

lemma Itilde_standard_cp {d : ℕ} (t : ℝ) (x : Fin d) :
    (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x).IsCompletelyPositive := by
  apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
  rw [choi_Itilde_standard]
  apply Matrix.PosSemidef.smul
  · apply (Matrix.posSemidef_vecMulVec_self_star _).add
    apply Matrix.PosSemidef.diagonal
    intro p
    change 0 ≤ if p.2 = x ∧ p.1 ≠ x then (b t : ℂ) ^ 2 else 0
    split_ifs
    · rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (sq_nonneg (b t))
    · exact le_rfl
  · positivity

lemma choi_competitor_psd {d : ℕ} {J : Fin d → MatrixMap (Fin d) (Fin d) ℂ}
    (x : Fin d) (hJ : (J x).IsCompletelyPositive) :
    (MatrixMap.choi_matrix (J x)).PosSemidef := by
  exact (MatrixMap.choi_PSD_iff_CP_map (J x)).mp hJ

lemma choi_sum (d : ℕ) (t : ℝ) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hJ : ∑ x, J x = It t) :
    ∑ x, MatrixMap.choi_matrix (J x) = MatrixMap.choi_matrix (It t) := by
  have hlin : MatrixMap.choi_matrix (∑ x, J x) =
      ∑ x, MatrixMap.choi_matrix (J x) := by
    ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
    simp [MatrixMap.choi_matrix, Matrix.sum_apply, LinearMap.sum_apply]
  rw [← hJ, hlin]

lemma trace_condition_entry {d : ℕ} {U : Matrix.unitaryGroup (Fin d) ℂ}
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

lemma choi_gram_rows {d : ℕ} {C : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hC : C.PosSemidef) :
    ∃ (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      C = B.conjTranspose * B := by
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
  exact Matrix.nonneg_iff_posSemidef.mpr hC

lemma certificate_identity {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) < t) (htu : t < 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x))
    (B : Fin d → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hB : ∀ x, MatrixMap.choi_matrix (J x) = (B x).conjTranspose * B x) :
    ∑ x, ∑ r, qCertificate d (a2 d t) (b t) (c d t) x
      (fun j i => star (B x r (j, i))) = 0 := by
  sorry

private def realDiagonalForm (d : ℕ) (aa bb cc : ℝ) (x : Fin d) (v : Fin d → ℝ) : ℝ :=
  ((aa + bb) / bb) * ((∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2) - v x ^ 2

private lemma real_diagonal_shift {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 < cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (v : Fin d → ℝ) :
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
    rw [hc]
    ring
  have hzsum : ∑ i, z i = (∑ i, v i) - r * cc := by
    dsimp [z]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hu]
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
  rw [hzsum, hzsq]
  dsimp [realDiagonalForm, r]
  have hb0 := ne_of_gt hbb
  have hc0 := ne_of_gt hcc
  have hk0 := ne_of_gt hkk
  field_simp
  <;> ring

private lemma diagonal_energy {d : ℕ} {aa bb cc : ℝ}
    (hbb : 0 < bb) (hcc : 0 < cc) (hc : cc = bb + d * aa) (v : Fin d → ℝ) :
    0 ≤ (∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2 ∧
      (((∑ i, v i ^ 2) - (aa / cc) * (∑ i, v i) ^ 2) = 0 → ∀ i, v i = 0) := by
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
        field_simp
        <;> ring
      rw [hid, div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hcc).mpr
      rw [hc]
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
    (hbb : 0 < bb) (hcc : 0 < cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (v : Fin d → ℝ) :
    0 ≤ realDiagonalForm d aa bb cc x v ∧
      (realDiagonalForm d aa bb cc x v = 0 →
        ∀ i, v i = (v x / (aa + bb)) * (aa + if i = x then bb else 0)) := by
  let z : Fin d → ℝ := fun i => v i - (v x / (aa + bb)) *
    (aa + if i = x then bb else 0)
  have he := diagonal_energy hbb hcc hc z
  have hs := real_diagonal_shift x hbb hcc hkk hc v
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

lemma qCertificate_nonneg {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 < cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (w : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ qCertificate d aa bb cc x w := by
  have hoff : 0 ≤ ∑ k', ∑ j,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 := by
    apply Finset.sum_nonneg
    intro k' hk'
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  rw [qCertificate_decomposition]
  exact add_nonneg (add_nonneg hoff
    (real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).re)).1)
    (real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).im)).1

lemma qCertificate_eq_zero {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 < cc) (hkk : 0 < aa + bb)
    (hc : cc = bb + d * aa) (w : Matrix (Fin d) (Fin d) ℂ)
    (hzero : qCertificate d aa bb cc x w = 0) :
    (∀ k' j, k' ≠ x → j ≠ k' → w j k' = 0) ∧
      (∀ i, w i i = (w x x / ((aa + bb : ℝ) : ℂ)) *
        ((aa + if i = x then bb else 0 : ℝ) : ℂ)) := by
  have hterm (k' j : Fin d) :
      0 ≤ if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 := by
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  have hoff : 0 ≤ ∑ k', ∑ j,
      if k' ≠ x ∧ j ≠ k' then Complex.normSq (w j k') else 0 :=
    Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun j _ => hterm k' j
  have hr := real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).re)
  have hi := real_diagonal_nonneg x hbb hcc hkk hc (fun i => (w i i).im)
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

lemma support_rows {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) < t) (htu : t < 1)
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
  have hc := c_pos hd htl
  have hk : 0 < a2 d t + b t := k_pos hd htl htu
  have hrel : c d t = b t + d * a2 d t := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    change c d t = b t + d * ((c d t - b t) / d)
    field_simp
    <;> ring
  have hnonneg (x : Fin d) (r : Fin d × Fin d) :
      0 ≤ qCertificate d (a2 d t) (b t) (c d t) x
        (fun j i => star (B x r (j, i))) :=
    qCertificate_nonneg x hb hc hk hrel _
  have htotal := certificate_identity hd htl htu J hsum htrace B hB
  intro x r
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun r _ => hnonneg x r)).mp htotal x (Finset.mem_univ x)
  have hr := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r _ => hnonneg x r)).mp hx r (Finset.mem_univ r)
  obtain ⟨hoff, hdiag⟩ := qCertificate_eq_zero x hb hc hk hrel _ hr
  refine ⟨?_, hdiag⟩
  intro k' j hk' hj
  exact star_eq_zero.mp (hoff k' j hk' hj)

lemma elimination_standard {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
    (htl : -1 / ((d : ℝ) ^ 2 - 1) < t) (htu : t < 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x := by
  sorry

lemma lower_endpoint_standard {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It (-1 / ((d : ℝ) ^ 2 - 1)))
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ)
        (sMax d (-1 / ((d : ℝ) ^ 2 - 1))) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ)
      (-1 / ((d : ℝ) ^ 2 - 1)) x := by
  sorry

lemma upper_endpoint_standard {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It 1)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d 1) x)) :
    ∀ x, J x = Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) 1 x := by
  sorry

lemma standard_basis_forward {d : ℕ} (hd : 2 ≤ d) {t : ℝ}
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
  exact elimination_standard hd (lt_of_le_of_ne htl (Ne.symm hl))
    (lt_of_le_of_ne htu hu) J hCP hsum htrace

def transformMap {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := W * Φ (W.conjTranspose * ρ * W) * W.conjTranspose
  map_add' ρ σ := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' z ρ := by simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

lemma transformMap_apply {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    transformMap W Φ ρ = W * Φ (W.conjTranspose * ρ * W) * W.conjTranspose := rfl

lemma transformMap_cp {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (Φ : MatrixMap (Fin d) (Fin d) ℂ) (hΦ : Φ.IsCompletelyPositive) :
    (transformMap W Φ).IsCompletelyPositive := by
  obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hΦ
  have hmap : transformMap W (MatrixMap.of_kraus K K) =
      MatrixMap.of_kraus (fun r => W * K r * W.conjTranspose)
        (fun r => W * K r * W.conjTranspose) := by
    apply LinearMap.ext
    intro ρ
    rw [transformMap_apply]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hmap]
  exact MatrixMap.of_kraus_isCompletelyPositive _

lemma Itilde_transform {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (t : ℝ) (x : Fin d) :
    transformMap (U : Matrix (Fin d) (Fin d) ℂ)
      (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) = Itilde U t x := by
  have hUV : (U : Matrix (Fin d) (Fin d) ℂ) *
      (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  apply LinearMap.ext
  intro ρ
  let W : Matrix (Fin d) (Fin d) ℂ := U
  let V := W.conjTranspose
  let P := Matrix.single x x (1 : ℂ)
  let Y := V * ρ * W
  have hWV : W * V = 1 := hUV
  have hWY : W * Y = ρ * W := by
    dsimp [Y]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
  have hYV : Y * V = V * ρ := by
    dsimp [Y]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hWV, Matrix.mul_one]
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

lemma transport_forward {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1)
    (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) = Matrix.trace (ρ * Qs U (sMax d t) x)) :
    ∀ x, J x = Itilde U t x := by
  sorry

lemma Itilde_cp {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    ∀ x, (Itilde U t x).IsCompletelyPositive := by
  intro x
  rw [← Itilde_transform U t x]
  exact transformMap_cp _ _ (Itilde_standard_cp t x)

lemma backward_direction {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (t : ℝ) (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    (∀ x, (Itilde U t x).IsCompletelyPositive) ∧
      (∑ x, Itilde U t x = It t) ∧
      (∀ x ρ, Matrix.trace (Itilde U t x ρ) =
        Matrix.trace (ρ * Qs U (sMax d t) x)) := by
  refine ⟨Itilde_cp hd U htl htu, Itilde_sum hd U htl htu, ?_⟩
  intro x ρ
  exact Itilde_trace hd U htl htu x ρ

theorem result : claim := by
  intro d hd U t htl htu J
  constructor
  · rintro ⟨hCP, hsum, htrace⟩
    exact transport_forward hd U htl htu J hCP hsum htrace
  · intro hJ
    have hJEq : J = Itilde U t := funext hJ
    subst J
    exact backward_direction hd U t htl htu

end D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
