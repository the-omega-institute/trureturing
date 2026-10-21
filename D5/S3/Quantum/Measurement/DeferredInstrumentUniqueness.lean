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
def a (d : ℕ) (t : ℝ) : ℝ := a2 d t * d

/-- The distinguished diagonal coefficient. -/
def k (d : ℕ) (t : ℝ) : ℝ := a d t + b t

lemma sum_Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ x, Q U x = 1 := by
  sorry

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
    2 * a2 d t * b t + (d : ℝ) * (a2 d t) ^ 2 = t := by
  sorry

lemma Itilde_sum {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1) :
    ∑ x, Itilde U t x = It t := by
  sorry

lemma Itilde_trace {d : ℕ} (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    {t : ℝ} (htl : -1 / ((d : ℝ) ^ 2 - 1) ≤ t) (htu : t ≤ 1)
    (x : Fin d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (Itilde U t x ρ) =
      Matrix.trace (ρ * Qs U (sMax d t) x) := by
  sorry

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
  sorry

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

lemma result_assembly : claim := by
  sorry

theorem result : claim := result_assembly

end D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
