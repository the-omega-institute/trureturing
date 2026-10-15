/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact spectra of symmetric two-qubit entanglement witnesses. -/

import Mathlib

set_option linter.style.longLine false

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum

noncomputable def coherent (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![v 0 ^ 2, (Real.sqrt 2 : ℂ) * v 0 * v 1, v 1 ^ 2]

def IsSymmetricWitness (W : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  W.IsHermitian ∧ ∀ v : Fin 2 → ℂ, 0 ≤ (star (coherent v) ⬝ᵥ (W *ᵥ coherent v)).re

def claim : Prop :=
  ∀ μ₁ μ₂ μ₃ : ℝ, μ₂ ≤ μ₁ → μ₃ ≤ μ₂ →
    ((∃ W : Matrix (Fin 3) (Fin 3) ℂ, IsSymmetricWitness W ∧
        W.charpoly = (Polynomial.X - Polynomial.C (μ₁ : ℂ)) * (Polynomial.X - Polynomial.C (μ₂ : ℂ)) *
          (Polynomial.X - Polynomial.C (μ₃ : ℂ))) ↔
      (0 ≤ μ₂ ∧ -Real.sqrt (μ₁ * μ₂) ≤ μ₃))

private def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℂ :=
  x ⬝ᵥ (A *ᵥ x)

private def energy (p q : ℝ) (x : Fin 2 → ℂ) : ℝ :=
  p * Complex.normSq (x 0) + q * Complex.normSq (x 1)

private def corner (G : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  G.submatrix Fin.castSucc Fin.castSucc

private def J : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, -1; 0, 1, 0; -1, 0, 0]

private theorem coherent_iff_null (x : Fin 3 → ℂ) :
    (∃ v : Fin 2 → ℂ, coherent v = x) ↔ qform J x = 0 := by
  have hj : qform J x = x 1 ^ 2 - 2 * x 0 * x 2 := by
    simp [qform, J, mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hj]
  constructor
  · rintro ⟨v, rfl⟩
    change ((Real.sqrt 2 : ℂ) * v 0 * v 1) ^ 2 - 2 * v 0 ^ 2 * v 1 ^ 2 = 0
    linear_combination (v 0 * v 1) ^ 2 * hs
  · intro hx
    by_cases h0 : x 0 = 0
    · have h1 : x 1 = 0 := by
        have : x 1 ^ 2 = 0 := by simpa [h0] using hx
        exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp this
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (x 2) (by norm_num : 0 < 2)
      refine ⟨![0, b], ?_⟩
      ext i
      fin_cases i <;> simp [coherent, h0, h1, hb]
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (x 0) (by norm_num : 0 < 2)
      have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact h0 ha.symm
      have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
      refine ⟨![a, x 1 / ((Real.sqrt 2 : ℂ) * a)], ?_⟩
      ext i
      fin_cases i
      · simpa [coherent] using ha
      · change (Real.sqrt 2 : ℂ) * a * (x 1 / ((Real.sqrt 2 : ℂ) * a)) = x 1
        field_simp
      · change (x 1 / ((Real.sqrt 2 : ℂ) * a)) ^ 2 = x 2
        field_simp
        rw [hs, ha]
        linear_combination hx

private theorem quadratic_pair (a b d : ℂ) (ha : a ≠ 0) :
    ∃ r s : ℂ, a * r ^ 2 + 2 * b * r + d = 0 ∧
      a * s ^ 2 + 2 * b * s + d = 0 ∧ a * r * s = d := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - a * d) (by norm_num : 0 < 2)
  refine ⟨(-b + t) / a, (-b - t) / a, ?_, ?_, ?_⟩
  all_goals field_simp
  all_goals first | linear_combination ht | linear_combination -ht

private theorem two_root_bound (a b d : ℂ) (ha : a ≠ 0) (c L : ℝ) (hc : 0 < c)
    (h : ∀ z : ℂ, a * z ^ 2 + 2 * b * z + d = 0 → c * Complex.normSq z ≤ L) :
    c * ‖d‖ ≤ ‖a‖ * L := by
  obtain ⟨r, s, hr, hs, hrs⟩ := quadratic_pair a b d ha
  have h1 := h r hr
  have h2 := h s hs
  rw [Complex.normSq_eq_norm_sq] at h1 h2
  have hprod : c * (‖r‖ * ‖s‖) ≤ L := by nlinarith [sq_nonneg (‖r‖ - ‖s‖)]
  have hn := congrArg norm hrs
  simp only [norm_mul] at hn
  nlinarith [norm_nonneg a]

private theorem bilinear_sq_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᵀ = A)
    (p q : ℝ) (h : ∀ u : Fin 2 → ℂ, ‖qform A u‖ ≤ energy p q u)
    (x y : Fin 2 → ℂ) :
    ‖x ⬝ᵥ (A *ᵥ y)‖ ^ 2 ≤ energy p q x * energy p q y := by
  let B := A.toBilin'
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  have pol (v w : Fin 2 → ℂ) :
      4 * (v ⬝ᵥ (A *ᵥ w)) = qform A (v + w) - qform A (v - w) := by
    have hp := hB.polarization v w
    have hm := hB.polarization v (-w)
    simp only [map_neg, LinearMap.neg_apply, neg_neg, ← sub_eq_add_neg] at hm
    change B v w = (B (v + w) (v + w) - B v v - B w w) / 2 at hp
    change -B v w = (B (v - w) (v - w) - B v v - B w w) / 2 at hm
    simp only [B, Matrix.toBilin'_apply'] at hp hm
    unfold qform
    linear_combination 2 * hp - 2 * hm
  have half (v w : Fin 2 → ℂ) :
      2 * ‖v ⬝ᵥ (A *ᵥ w)‖ ≤ energy p q v + energy p q w := by
    have hn := norm_sub_le (qform A (v+w)) (qform A (v-w))
    rw [← pol, norm_mul] at hn
    norm_num only [Complex.norm_ofNat] at hn
    have he : energy p q (v+w) + energy p q (v-w) =
        2 * (energy p q v + energy p q w) := by
      simp only [energy, Pi.add_apply, Pi.sub_apply, Complex.normSq_add, Complex.normSq_sub]
      ring
    linarith [h (v+w), h (v-w)]
  have scale (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      2 * s * t * ‖x ⬝ᵥ (A *ᵥ y)‖ ≤
        s ^ 2 * energy p q x + t ^ 2 * energy p q y := by
    have hh := half ((s : ℂ) • x) ((t : ℂ) • y)
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg ht,
      energy, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      ← pow_two, norm_mul] at hh
    dsimp [energy]
    nlinarith only [hh]
  have hP : 0 ≤ energy p q x := le_trans (norm_nonneg _) (h x)
  have hR : 0 ≤ energy p q y := le_trans (norm_nonneg _) (h y)
  by_cases h0 : energy p q x = 0
  · have hh := scale (energy p q y + 1) ‖x ⬝ᵥ (A *ᵥ y)‖ (by linarith) (norm_nonneg _)
    rw [h0] at hh ⊢
    nlinarith [sq_nonneg ‖x ⬝ᵥ (A *ᵥ y)‖]
  · have hh := scale ‖x ⬝ᵥ (A *ᵥ y)‖ (energy p q x) (norm_nonneg _) hP
    have hPpos : 0 < energy p q x := lt_of_le_of_ne hP (Ne.symm h0)
    nlinarith

private theorem det_bound (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᵀ = A)
    (p q : ℝ) (h : ∀ u : Fin 2 → ℂ, ‖qform A u‖ ≤ energy p q u) :
    0 ≤ p ∧ 0 ≤ q ∧ ‖A.det‖ ≤ p * q := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  have hp' := h ![1, 0]
  have hq' := h ![0, 1]
  simp [qform, energy, mulVec, dotProduct, Fin.sum_univ_two] at hp' hq'
  have hp : 0 ≤ p := le_trans (norm_nonneg _) hp'
  have hq : 0 ≤ q := le_trans (norm_nonneg _) hq'
  refine ⟨hp, hq, ?_⟩
  let a := A 0 0
  let b := A 0 1
  let S := q * Complex.normSq a + p * Complex.normSq b
  have hS : 0 ≤ S := add_nonneg (mul_nonneg hq (Complex.normSq_nonneg _))
    (mul_nonneg hp (Complex.normSq_nonneg _))
  have hb1 : (![1, 0] : Fin 2 → ℂ) ⬝ᵥ
      (A *ᵥ ![(q : ℂ) * star a, (p : ℂ) * star b]) = (S : ℂ) := by
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_mul, add_zero]
    change a * (↑q * star a) + b * (↑p * star b) = ↑S
    rw [show a * (↑q * star a) + b * (↑p * star b) =
      ↑q * (a * star a) + ↑p * (b * star b) by ring]
    simp only [Complex.star_def, Complex.mul_conj, S, Complex.ofReal_add, Complex.ofReal_mul]
  have h1 := bilinear_sq_le A hA p q h ![1, 0]
    ![(q : ℂ) * star a, (p : ℂ) * star b]
  rw [hb1] at h1
  simp only [energy, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one,
    Complex.normSq_zero, mul_one, mul_zero, add_zero, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.star_def, Complex.normSq_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hS] at h1
  have hSb : S ≤ p ^ 2 * q := by
    have hfac : S * S ≤ p ^ 2 * q * S := by dsimp [S] at *; nlinarith only [h1]
    by_cases hz : S = 0
    · rw [hz]; positivity
    · have : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      exact le_of_mul_le_mul_right hfac this
  have h2 := bilinear_sq_le A hA p q h ![0, 1] ![b, -a]
  have hb2 : (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (A *ᵥ ![b, -a]) = -A.det := by
    simp [mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, h10, a, b]
    ring
  rw [hb2, norm_neg] at h2
  simp only [energy, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_one,
    Complex.normSq_zero, mul_one, mul_zero, zero_add, Complex.normSq_neg] at h2
  have hdet : ‖A.det‖ ^ 2 ≤ (p * q) ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hSb hq
    dsimp [S] at h3
    nlinarith only [h2, h3]
  nlinarith [norm_nonneg A.det, mul_nonneg hp hq]

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
