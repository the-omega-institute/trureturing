/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound
   mirror-E: none(waiver:kernel-checked-spectral-construction)
   anchors: []
   utility: none
   digest: Inserting or deleting a middle spectral value yields the sharp dimension-sixteen bound. -/

/-
proof_shape: spectral_purity_bound: content
escape_witness: the dimension-sixteen inequality is obtained by a new ordered
  insertion/deletion argument preserving both extremal-coordinate LMIs.
admission_basis: content
Direct frozen dependencies: QutritN5PurityBound, QutritN6PurityBound.
   A four-by-four spectral bridge.  The argument only uses the two necessary
   qutrit Bell-compression LMIs on the six smallest and three largest
   coordinates, together with the already checked qutrit certificates at
   lengths 15 and 18.  It is an ordinary spectral inequality; the literal
   APPT-to-LMI reduction is supplied by the consuming four-by-four module.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN5PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768
open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSpectralPurityBound

open D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction

def K1 (l : Fin 16 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*l 15, l 14-l 0, l 12-l 1;
     l 14-l 0, 2*l 13, l 11-l 2;
     l 12-l 1, l 11-l 2, 2*l 10]

def K2 (l : Fin 16 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*l 15, l 14-l 0, l 13-l 1;
     l 14-l 0, 2*l 12, l 11-l 2;
     l 13-l 1, l 11-l 2, 2*l 10]

private def insert18 (l : Fin 16 → ℝ) : Fin 18 → ℝ :=
  ![l 0, l 1, l 2, l 3, l 4, l 5, l 6, l 7, l 8, l 9,
    l 9, l 9, l 10, l 11, l 12, l 13, l 14, l 15]

private def delete15 (l : Fin 16 → ℝ) : Fin 15 → ℝ :=
  ![l 0, l 1, l 2, l 3, l 4, l 5, l 6, l 7, l 8,
    l 10, l 11, l 12, l 13, l 14, l 15]

private theorem insert18_antitone (l : Fin 16 → ℝ) (hl : Antitone l) :
    Antitone (insert18 l) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  fin_cases i <;> simp [insert18]
  all_goals exact hl (by decide)

private theorem delete15_antitone (l : Fin 16 → ℝ) (hl : Antitone l) :
    Antitone (delete15 l) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  fin_cases i <;> simp [delete15]
  all_goals exact hl (by decide)

private theorem insert18_sum (l : Fin 16 → ℝ) :
    (∑ i, insert18 l i) = (∑ i, l i) + 2 * l 9 := by
  simp [insert18, Fin.sum_univ_succ]
  ring

private theorem delete15_sum (l : Fin 16 → ℝ) :
    (∑ i, delete15 l i) = (∑ i, l i) - l 9 := by
  simp [delete15, Fin.sum_univ_succ]
  ring

private theorem insert18_sq_sum (l : Fin 16 → ℝ) :
    (∑ i, (insert18 l i)^2) = (∑ i, (l i)^2) + 2 * (l 9)^2 := by
  simp [insert18, Fin.sum_univ_succ]
  ring

private theorem delete15_sq_sum (l : Fin 16 → ℝ) :
    (∑ i, (delete15 l i)^2) = (∑ i, (l i)^2) - (l 9)^2 := by
  simp [delete15, Fin.sum_univ_succ]
  ring

private theorem insert18_K1 (l : Fin 16 → ℝ) :
    QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 3 (insert18 l)) = K1 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QutritSpectralReduction.K1, QutritSpectralReduction.boundaryValues,
      insert18, K1]

private theorem insert18_K2 (l : Fin 16 → ℝ) :
    QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 3 (insert18 l)) = K2 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QutritSpectralReduction.K2, QutritSpectralReduction.boundaryValues,
      insert18, K2]

private theorem delete15_K1 (l : Fin 16 → ℝ) :
    QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 2 (delete15 l)) = K1 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QutritSpectralReduction.K1, QutritSpectralReduction.boundaryValues,
      delete15, K1]

private theorem delete15_K2 (l : Fin 16 → ℝ) :
    QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 2 (delete15 l)) = K2 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QutritSpectralReduction.K2, QutritSpectralReduction.boundaryValues,
      delete15, K2]

theorem spectral_purity_bound (l : Fin 16 → ℝ) (horder : Antitone l)
    (hnonneg : ∀ i, 0 ≤ l i) (htrace : ∑ i, l i = 1)
    (h1 : (K1 l).PosSemidef) (h2 : (K2 l).PosSemidef) :
    ∑ i, (l i)^2 ≤ (2 : ℝ) / 27 := by
  have ht : 0 ≤ l 9 := hnonneg 9
  have hquad := h1.dotProduct_mulVec_nonneg (![1, 1, 1] : Fin 3 → ℝ)
  have htopbottom : l 0 + l 1 + l 2 ≤
      l 10 + l 11 + l 12 + l 13 + l 14 + l 15 := by
    -- The displayed quadratic form is exactly twice (bottom six minus top three).
    norm_num [K1, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] at hquad
    linarith
  have htcap : l 9 ≤ (1 : ℝ) / 13 := by
    have htop : 3 * l 9 ≤ l 0 + l 1 + l 2 := by
      linarith [horder (show (0 : Fin 16) ≤ 9 by decide),
        horder (show (1 : Fin 16) ≤ 9 by decide),
        horder (show (2 : Fin 16) ≤ 9 by decide)]
    have hmid : 7 * l 9 ≤ l 3 + l 4 + l 5 + l 6 + l 7 + l 8 + l 9 := by
      linarith [horder (show (3 : Fin 16) ≤ 9 by decide),
        horder (show (4 : Fin 16) ≤ 9 by decide),
        horder (show (5 : Fin 16) ≤ 9 by decide),
        horder (show (6 : Fin 16) ≤ 9 by decide),
        horder (show (7 : Fin 16) ≤ 9 by decide),
        horder (show (8 : Fin 16) ≤ 9 by decide)]
    have htrace' := htrace
    norm_num [Fin.sum_univ_succ] at htrace'
    change l 0 + (l 1 + (l 2 + (l 3 + (l 4 + (l 5 + (l 6 + (l 7 + (l 8 + (l 9 + (l 10 + (l 11 + (l 12 + (l 13 + (l 14 + (l 15))))))))))))))) = 1 at htrace'
    have hsum : 13 * l 9 ≤ 1 := by
      linarith [htop, hmid, htopbottom, htrace']
    linarith
  by_cases hsmall : l 9 ≤ (1 : ℝ) / 18
  · let s : ℝ := 1 + 2 * l 9
    let μ : Fin 18 → ℝ := insert18 l
    let ν : Fin 18 → ℝ := fun i => μ i / s
    have hs : 0 < s := by dsimp [s]; linarith
    have hμorder : Antitone μ := by exact insert18_antitone l horder
    have hμnonneg : ∀ i, 0 ≤ μ i := by
      intro i; fin_cases i <;> simp [μ, insert18]
      all_goals exact hnonneg _
    have hμtrace : ∑ i, μ i = s := by
      dsimp [μ, s]
      rw [insert18_sum, htrace]
    have hνorder : Antitone ν := by
      intro i j hij
      exact (div_le_div_of_nonneg_right (hμorder hij) (le_of_lt hs))
    have hνnonneg : ∀ i, 0 ≤ ν i := by
      intro i; exact div_nonneg (hμnonneg i) (le_of_lt hs)
    have hνtrace : ∑ i, ν i = 1 := by
      simp only [ν]
      rw [← Finset.sum_div, hμtrace]
      exact div_self hs.ne'
    have hμ1 : (QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 3 μ)).PosSemidef := by
      rw [insert18_K1]
      exact h1
    have hμ2 : (QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 3 μ)).PosSemidef := by
      rw [insert18_K2]
      exact h2
    have hν1 : (QutritSpectralReduction.K1
        (QutritSpectralReduction.boundaryValues 3 ν)).PosSemidef := by
      have heq : QutritSpectralReduction.K1
          (QutritSpectralReduction.boundaryValues 3 ν) = (1 / s) •
            QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 3 μ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ν, μ, insert18, s, QutritSpectralReduction.K1,
            QutritSpectralReduction.boundaryValues, Matrix.smul_apply, div_eq_mul_inv]
        all_goals ring
      rw [heq]
      exact hμ1.smul (by positivity)
    have hν2 : (QutritSpectralReduction.K2
        (QutritSpectralReduction.boundaryValues 3 ν)).PosSemidef := by
      have heq : QutritSpectralReduction.K2
          (QutritSpectralReduction.boundaryValues 3 ν) = (1 / s) •
            QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 3 μ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ν, μ, insert18, s, QutritSpectralReduction.K2,
            QutritSpectralReduction.boundaryValues, Matrix.smul_apply, div_eq_mul_inv]
        all_goals ring
      rw [heq]
      exact hμ2.smul (by positivity)
    have hbound := QutritN6PurityBound.certificate_bound ν hνorder
      (hνnonneg 17) hνtrace hν1 hν2
    have hsquares : (∑ i, (ν i)^2) =
        (∑ i, (μ i)^2) / s^2 := by
      simp only [ν, div_pow, Finset.sum_div]
    rw [hsquares] at hbound
    have hb := (div_le_iff₀ (sq_pos_of_pos hs)).mp hbound
    rw [insert18_sq_sum] at hb
    dsimp [s] at hb ⊢
    nlinarith
  · have hlarge : (1 : ℝ) / 18 ≤ l 9 := le_of_not_ge hsmall
    let s : ℝ := 1 - l 9
    let μ : Fin 15 → ℝ := delete15 l
    let ν : Fin 15 → ℝ := fun i => μ i / s
    have hs : 0 < s := by dsimp [s]; linarith
    have hμorder : Antitone μ := by exact delete15_antitone l horder
    have hμnonneg : ∀ i, 0 ≤ μ i := by
      intro i; fin_cases i <;> simp [μ, delete15]
      all_goals exact hnonneg _
    have hμtrace : ∑ i, μ i = s := by
      dsimp [μ, s]
      rw [delete15_sum, htrace]
    have hνorder : Antitone ν := by
      intro i j hij
      exact (div_le_div_of_nonneg_right (hμorder hij) (le_of_lt hs))
    have hνnonneg : ∀ i, 0 ≤ ν i := by
      intro i; exact div_nonneg (hμnonneg i) (le_of_lt hs)
    have hνtrace : ∑ i, ν i = 1 := by
      simp only [ν]
      rw [← Finset.sum_div, hμtrace]
      exact div_self hs.ne'
    have hμ1 : (QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 2 μ)).PosSemidef := by
      rw [delete15_K1]
      exact h1
    have hμ2 : (QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 2 μ)).PosSemidef := by
      rw [delete15_K2]
      exact h2
    have hν1 : (QutritSpectralReduction.K1
        (QutritSpectralReduction.boundaryValues 2 ν)).PosSemidef := by
      have heq : QutritSpectralReduction.K1
          (QutritSpectralReduction.boundaryValues 2 ν) = (1 / s) •
            QutritSpectralReduction.K1 (QutritSpectralReduction.boundaryValues 2 μ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ν, μ, delete15, s, QutritSpectralReduction.K1,
            QutritSpectralReduction.boundaryValues, Matrix.smul_apply, div_eq_mul_inv]
        all_goals ring
      rw [heq]
      exact hμ1.smul (by positivity)
    have hν2 : (QutritSpectralReduction.K2
        (QutritSpectralReduction.boundaryValues 2 ν)).PosSemidef := by
      have heq : QutritSpectralReduction.K2
          (QutritSpectralReduction.boundaryValues 2 ν) = (1 / s) •
            QutritSpectralReduction.K2 (QutritSpectralReduction.boundaryValues 2 μ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ν, μ, delete15, s, QutritSpectralReduction.K2,
            QutritSpectralReduction.boundaryValues, Matrix.smul_apply, div_eq_mul_inv]
        all_goals ring
      rw [heq]
      exact hμ2.smul (by positivity)
    have hbound := QutritN5PurityBound.certificate_bound ν hνorder
      (hνnonneg 14) hνtrace hν1 hν2
    have hsquares : (∑ i, (ν i)^2) =
        (∑ i, (μ i)^2) / s^2 := by
      simp only [ν, div_pow, Finset.sum_div]
    rw [hsquares] at hbound
    have hb := (div_le_iff₀ (sq_pos_of_pos hs)).mp hbound
    rw [delete15_sq_sum] at hb
    dsimp [s] at hb ⊢
    nlinarith [hlarge, htcap]

#print axioms spectral_purity_bound

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSpectralPurityBound
