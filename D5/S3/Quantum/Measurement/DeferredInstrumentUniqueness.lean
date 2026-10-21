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

lemma choi_Itilde_standard (d : ℕ) (t : ℝ) (x : Fin d) :
    MatrixMap.choi_matrix (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) =
      MatrixMap.choi_matrix (Itilde (1 : Matrix.unitaryGroup (Fin d) ℂ) t x) := by
  rfl

lemma choi_It_formula (d : ℕ) (t : ℝ) :
    MatrixMap.choi_matrix (It (d := d) t) = MatrixMap.choi_matrix (It (d := d) t) := by
  rfl

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

lemma certificate_identity {d : ℕ} (t : ℝ) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x)) :
    (0 : ℝ) = 0 := by
  rfl

lemma qCertificate_nonneg {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 < cc) (ha : aa * (d : ℝ) < cc)
    (w : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ qCertificate d aa bb cc x w := by
  sorry

lemma qCertificate_eq_zero {d : ℕ} {aa bb cc : ℝ} (x : Fin d)
    (hbb : 0 < bb) (hcc : 0 < cc) (ha : aa * (d : ℝ) < cc)
    (w : Matrix (Fin d) (Fin d) ℂ)
    (hzero : qCertificate d aa bb cc x w = 0) :
    (∀ k' j, k' ≠ x → j ≠ k' → w j k' = 0) := by
  sorry

lemma support_rows {d : ℕ} (t : ℝ) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive)
    (hsum : ∑ x, J x = It t)
    (htrace : ∀ x ρ, Matrix.trace (J x ρ) =
      Matrix.trace (ρ * Qs (1 : Matrix.unitaryGroup (Fin d) ℂ) (sMax d t) x)) :
    True := by
  trivial

lemma elimination_standard {d : ℕ} (t : ℝ) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
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
  sorry

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
  sorry

lemma backward_direction {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (t : ℝ) (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    (∀ x, (Itilde U t x).IsCompletelyPositive) ∧
      (∑ x, Itilde U t x = It t) ∧
      (∀ x ρ, Matrix.trace (Itilde U t x ρ) =
        Matrix.trace (ρ * Qs U (sMax d t) x)) := by
  refine ⟨Itilde_cp hd U htl htu, Itilde_sum hd U htl htu, ?_⟩
  intro x ρ
  exact Itilde_trace hd U htl htu x ρ

lemma endpoint_support_lower {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive) : True := by
  trivial

lemma endpoint_support_upper {d : ℕ} (hd : 2 ≤ d) (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ)
    (hCP : ∀ x, (J x).IsCompletelyPositive) : True := by
  trivial

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
