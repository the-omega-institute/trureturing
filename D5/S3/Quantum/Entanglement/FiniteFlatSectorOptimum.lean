/- GID: D5/S3/Quantum/Entanglement/FiniteFlatSectorOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteFlatSectorOptimum
   mirror-E: none(waiver:finite-physical-channel-construction)
   anchors: []
   utility: none
   digest: The original compact flat sector encodings and their common local-channel optimum. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
import D5.S3.Quantum.Entanglement.ExponentialSectorKernel
import D5.S3.Quantum.Reduction.CoherentFlagPort
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.Quantum.Entanglement.FiniteFlatSectorOptimum

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]

/-- A finite common ambient list; each physical flat residual uses its initial segment. -/
def flatSpectrum (J m : ℕ) (j : Fin J) : ℝ :=
  if j.val < m then (m : ℝ)⁻¹ else 0

private theorem initial_segment_sum (J m : ℕ) (hmJ : m ≤ J) (c : ℝ) :
    (∑ j : Fin J, if j.val < m then c else 0) = (m : ℝ) * c := by
  induction J with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero hmJ
    subst m
    simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hm : m ≤ J
    · rw [ih hm, if_neg (by omega)]
      ring
    · have hm : m = J + 1 := by omega
      subst m
      have hall : (∑ j : Fin J, if j.val < J + 1 then c else 0) = (J : ℝ) * c := by
        simp [show ∀ j : Fin J, j.val < J + 1 from fun j => by omega]
      rw [hall, if_pos (by omega)]
      push_cast
      ring

private theorem flat_spectrum_sum (J m : ℕ) (hm : 0 < m) (hmJ : m ≤ J) :
    (∑ j, flatSpectrum J m j) = 1 := by
  unfold flatSpectrum
  rw [initial_segment_sum J m hmJ]
  exact mul_inv_cancel₀ (by exact_mod_cast hm.ne')

private theorem flat_spectrum_antitone (J m : ℕ) : Antitone (flatSpectrum J m) := by
  intro i j hij
  unfold flatSpectrum
  split_ifs <;> first | positivity | omega | rfl

private theorem flat_gram (J m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmJ : m ≤ J) (hnJ : n ≤ J) :
    (∑ j, Real.sqrt (flatSpectrum J m j) * Real.sqrt (flatSpectrum J n j)) =
      Real.sqrt ((min m n : ℕ) / (max m n : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (j : Fin J) :
      Real.sqrt (flatSpectrum J m j) * Real.sqrt (flatSpectrum J n j) =
        if j.val < min m n then Real.sqrt ((m : ℝ)⁻¹) * Real.sqrt ((n : ℝ)⁻¹)
        else 0 := by
    simp only [flatSpectrum, lt_min_iff]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [initial_segment_sum J (min m n) (min_le_left _ _ |>.trans hmJ)]
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rcases le_total m n with h | h
  · rw [min_eq_left h, max_eq_right h]
    have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ)⁻¹ by positivity)
    have ht := Real.sq_sqrt (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    rw [mul_pow, mul_pow, hs, ht]
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ)⁻¹ by positivity)
    have ht := Real.sq_sqrt (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    rw [mul_pow, mul_pow, hs, ht]
    field_simp

private theorem flat_gram_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt ((min m n : ℕ) / (max m n : ℝ)) =
      Real.exp (-|Real.log (m : ℝ) - Real.log (n : ℝ)| / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (Real.exp_pos _).le).mpr
  rw [← Real.exp_nat_mul]
  rcases le_total m n with h | h
  · have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hm0 (by exact_mod_cast h)
    rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr hlog)]
    rw [show (2 : ℝ) * (-(-(Real.log (m : ℝ) - Real.log (n : ℝ))) / 2) =
      Real.log (m : ℝ) - Real.log (n : ℝ) by ring]
    rw [Real.exp_sub, Real.exp_log hm0, Real.exp_log hn0]
  · have hlog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log hn0 (by exact_mod_cast h)
    rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr hlog)]
    rw [show (2 : ℝ) * (-(Real.log (m : ℝ) - Real.log (n : ℝ)) / 2) =
      Real.log (n : ℝ) - Real.log (m : ℝ) by ring]
    rw [Real.exp_sub, Real.exp_log hn0, Real.exp_log hm0]

end D5.S3.Quantum.Entanglement.FiniteFlatSectorOptimum
