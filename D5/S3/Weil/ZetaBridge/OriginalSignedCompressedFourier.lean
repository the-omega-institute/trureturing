/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedCompressedFourier
   mirror-E: none(waiver:literal-Ioc-complex-integral)
   anchors: []
   utility: none
   digest: Literal Ioc compressed translations of all signed complex Fourier modes. -/

import D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix
import D5.S3.Weil.ZetaBridge.OriginalEvenCosineComplete
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The signed complex compressed Fourier matrix

The classical interval Fourier calculation is the compressed-translation part
of the Connes--Consani--Moscovici dictionary (Lemma 2.3 and Section 4).
The carrier is physical Lebesgue measure on `(-L/2,L/2]`.  Translation means
`T_h u x = u (x-h)`, hence the existing compression parameter is `-h`.
The mode is written with a shifted origin solely to incorporate `(-1)^n`.
This module proves no Gamma/full-density or positivity statement.
-/

noncomputable section
namespace OriginalSignedCompressedFourier

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix

private def wave (w x : ℝ) : ℂ := Complex.exp (((w * x : ℝ) : ℂ) * Complex.I)

def frequency (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / L

/-- Subject-local normalized character; no completeness claim is made here. -/
def mode (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  wave (frequency L n) (x + L / 2) / (Real.sqrt L : ℂ)

/-- Conjugate-first, literal line correlation of the original zero extensions. -/
def entry (L : ℝ) (m n : ℤ) (h : ℝ) : ℂ :=
  pairing (L / 2) (-h) (fun x => conj (mode L m x)) (mode L n)

private lemma wave_add (w x y : ℝ) : wave w (x + y) = wave w x * wave w y := by
  unfold wave
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private lemma wave_conj_mul (u v x : ℝ) :
    conj (wave u x) * wave v x = wave (v - u) x := by
  unfold wave
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma wave_norm (w x : ℝ) : ‖wave w x‖ = 1 := by
  simp [wave, Complex.norm_exp]

private lemma wave_period (L : ℝ) (hL : 0 < L) (n : ℤ) :
    wave (frequency L n) L = 1 := by
  unfold wave frequency
  rw [div_mul_cancel₀ _ hL.ne']
  convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;> push_cast <;> ring

private lemma frequency_sub (L : ℝ) (m n : ℤ) :
    frequency L n - frequency L m = frequency L (n - m) := by
  unfold frequency
  push_cast
  ring

lemma mode_continuous (L : ℝ) (n : ℤ) : Continuous (mode L n) := by
  unfold mode wave
  fun_prop

/-- Exact dictionary to the existing unnormalised physical character, and
simultaneously to the signed phase required by the original matrix. -/
theorem normalization_dictionary (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ) :
    mode L n x =
      ((-1 : ℂ) ^ n) * OriginalEvenCosineComplete.character (L / 2) n x /
        (Real.sqrt L : ℂ) := by
  have hp : wave (frequency L n) (L / 2) = (-1 : ℂ) ^ n := by
    unfold wave frequency
    rw [show ((2 * Real.pi * (n : ℝ) / L) * (L / 2)) =
        (n : ℝ) * Real.pi by field_simp [hL.ne']]
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hc : wave (frequency L n) x = OriginalEvenCosineComplete.character (L / 2) n x := by
    simp only [wave, frequency, OriginalEvenCosineComplete.character, fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [mode, wave_add, hp, hc]
  ring

private lemma mode_product (L : ℝ) (hL : 0 < L) (m n : ℤ) (x s : ℝ) :
    conj (mode L m x) * mode L n (x + s) =
      (wave (frequency L n) s / (L : ℂ)) *
        wave (frequency L (n - m)) (x + L / 2) := by
  have hr : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    norm_cast
    nlinarith [Real.sq_sqrt hL.le]
  simp only [mode, map_div₀, Complex.conj_ofReal]
  rw [show x + s + L / 2 = (x + L / 2) + s by ring,
    wave_add (frequency L n) (x + L / 2) s]
  rw [show conj (wave (frequency L m) (x + L / 2)) / (Real.sqrt L : ℂ) *
      (wave (frequency L n) (x + L / 2) * wave (frequency L n) s /
        (Real.sqrt L : ℂ)) =
      wave (frequency L n) s / ((Real.sqrt L : ℂ) * (Real.sqrt L : ℂ)) *
      (conj (wave (frequency L m) (x + L / 2)) *
        wave (frequency L n) (x + L / 2)) by ring]
  rw [hr, wave_conj_mul, frequency_sub]

private lemma integral_wave (w a b : ℝ) (hw : w ≠ 0) :
    (∫ x in a..b, wave w x) =
      (wave w b - wave w a) / ((w : ℂ) * Complex.I) := by
  have hc : (w : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) Complex.I_ne_zero
  unfold wave
  simp_rw [Complex.ofReal_mul, mul_right_comm (w : ℂ) _ Complex.I]
  exact integral_exp_mul_complex hc

private lemma frequency_ne (L : ℝ) (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) :
    frequency L (n - m) ≠ 0 := by
  unfold frequency
  have hd : (n - m : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (by exact_mod_cast hd)) hL.ne'

/-- Direct integration on `(h-L/2,L/2]`, including both removable shift
endpoints. The off-diagonal denominator is guarded by `m ≠ n`. -/
theorem entry_nonneg (L : ℝ) (hL : 0 < L) (m n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    entry L m n h = if m = n then
      (((L - h) / L : ℝ) : ℂ) * wave (frequency L n) (-h)
    else (wave (frequency L n) (-h) - wave (frequency L m) (-h)) /
      (Complex.I * (2 * Real.pi : ℝ) * ((n : ℂ) - (m : ℂ))) := by
  rw [entry, pairing_nonpos (L / 2) (-h) _ _ (by linarith) (by linarith)]
  simp_rw [mode_product L hL m n]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right]
  simp only [show -(L / 2) - -h + L / 2 = h by ring,
    show L / 2 + L / 2 = L by ring]
  split_ifs with hmn
  · subst n
    simp [frequency, wave, intervalIntegral.integral_const, smul_eq_mul]
    push_cast
    ring
  · rw [integral_wave _ _ _ (frequency_ne L hL hmn), wave_period L hL]
    have he : wave (frequency L n) (-h) * wave (frequency L (n - m)) h =
        wave (frequency L m) (-h) := by
      unfold wave frequency
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    have hd : (n : ℂ) - (m : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hmn))
    dsimp [frequency] at he ⊢
    push_cast at he ⊢
    field_simp [hLc, hd, Real.pi_ne_zero, Complex.I_ne_zero]
    linear_combination -he

lemma pairing_line (a s : ℝ) (f g : ℝ → ℂ) :
    pairing a s (fun x => conj (f x)) g =
      ∫ x : ℝ, conj (zeroExtension a f x) * zeroExtension a g (x + s) := by
  unfold pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ window a <;> simp [compression, zeroExtension, hx]

/-- The opposite shift is the conjugate transpose, by a literal line
translation of the two indicator functions, with no parity restriction. -/
theorem entry_adjoint (L : ℝ) (m n : ℤ) (h : ℝ) :
    entry L m n (-h) = conj (entry L n m h) := by
  simp only [entry, neg_neg, pairing_line]
  rw [← integral_conj]
  calc
    _ = ∫ x : ℝ, conj (zeroExtension (L / 2) (mode L m) x) *
        zeroExtension (L / 2) (mode L n) (x + h) := rfl
    _ = ∫ y : ℝ, conj (zeroExtension (L / 2) (mode L m) (y - h)) *
        zeroExtension (L / 2) (mode L n) y := by
      have ht := integral_add_right_eq_self
        (fun y : ℝ => conj (zeroExtension (L / 2) (mode L m) (y - h)) *
          zeroExtension (L / 2) (mode L n) y) h (μ := volume)
      simpa only [add_sub_cancel_right] using ht
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp [map_mul, mul_comm, sub_eq_add_neg]

/-- All shifts outside or at the two physical endpoint shifts vanish. -/
theorem entry_disjoint (L : ℝ) (m n : ℤ) (h : ℝ) (hh : L ≤ |h|) :
    entry L m n h = 0 := by
  rcases le_or_gt 0 h with hs | hs
  · rw [abs_of_nonneg hs] at hh
    exact pairing_zero_left (L / 2) (-h) _ _ (by linarith)
  · rw [abs_of_neg hs] at hh
    exact pairing_zero_right (L / 2) (-h) _ _ (by linarith)

/-- Explicit all-real-shift matrix. The branch at `|h| = L` is zero before
any division. The diagonal includes every signed zero-frequency case. -/
def matrix (L : ℝ) (m n : ℤ) (h : ℝ) : ℂ :=
  if L ≤ |h| then 0 else
  if 0 ≤ h then
    if m = n then (((L - h) / L : ℝ) : ℂ) * wave (frequency L n) (-h)
    else (wave (frequency L n) (-h) - wave (frequency L m) (-h)) /
      (Complex.I * (2 * Real.pi : ℝ) * ((n : ℂ) - (m : ℂ)))
  else conj (if n = m then (((L + h) / L : ℝ) : ℂ) * wave (frequency L m) h
    else (wave (frequency L m) h - wave (frequency L n) h) /
      (Complex.I * (2 * Real.pi : ℝ) * ((m : ℂ) - (n : ℂ))))

theorem entry_eq_matrix (L : ℝ) (hL : 0 < L) (m n : ℤ) (h : ℝ) :
    entry L m n h = matrix L m n h := by
  unfold matrix
  by_cases hc : L ≤ |h|
  · rw [if_pos hc]
    exact entry_disjoint L m n h hc
  · rw [if_neg hc]
    by_cases hs : 0 ≤ h
    · rw [if_pos hs]
      exact entry_nonneg L hL m n h hs (by linarith [le_abs_self h])
    · rw [if_neg hs]
      calc
        entry L m n h = conj (entry L n m (-h)) := by
          simpa only [neg_neg] using entry_adjoint L m n (-h)
        _ = _ := by
          rw [entry_nonneg L hL n m (-h) (by linarith) (by
            rw [abs_of_neg (lt_of_not_ge hs)] at hc
            linarith)]
          simp only [neg_neg, sub_neg_eq_add]

/-- Actual paired-shift entry. The real sine divided difference is obtained
only after the two independently compressed complex shifts are added. -/
theorem entry_paired (L : ℝ) (hL : 0 < L) (m n : ℤ) (h : ℝ)
    (hh : 0 ≤ h) (hcap : h ≤ L) :
    entry L m n h + entry L m n (-h) =
      if m = n then ((2 * (1 - h / L) * Real.cos (frequency L n * h) : ℝ) : ℂ)
      else (((Real.sin (frequency L m * h) - Real.sin (frequency L n * h)) /
        (Real.pi * ((n : ℝ) - (m : ℝ))) : ℝ) : ℂ) := by
  rw [entry_adjoint L, entry_nonneg L hL m n h hh hcap,
    entry_nonneg L hL n m h hh hcap]
  by_cases he : m = n
  · subst n
    simp only [ite_eq_left rfl, wave, Complex.exp_ofReal_mul_I, mul_neg,
      Real.cos_neg, Real.sin_neg, map_add, map_mul, map_neg, map_div₀,
      Complex.conj_ofReal, Complex.conj_I]
    push_cast
    simp only [map_mul, map_add, map_sub, map_div₀, map_neg, map_inv₀,
      Complex.conj_ofReal, Complex.conj_I, ← Complex.cos_conj, ← Complex.sin_conj]
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
    <;> ring
  · rw [ite_eq_right he, ite_eq_right (Ne.symm he), ite_eq_right he]
    simp only [wave, Complex.exp_ofReal_mul_I, mul_neg, Real.cos_neg, Real.sin_neg,
      map_div₀, map_sub, map_add, map_mul, map_neg, map_intCast,
      Complex.conj_I, Complex.conj_ofReal]
    have hd : (n : ℂ) - (m : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr (Ne.symm he))
    have hd' : (m : ℂ) - (n : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
    have hd'' : -(n : ℂ) + (m : ℂ) ≠ 0 := by
      simpa only [sub_eq_add_neg, add_comm] using hd'
    push_cast
    simp only [mul_comm]
    field_simp [hd, hd', hd'', Complex.I_ne_zero, Real.pi_ne_zero]
    <;> ring

/-- The uniform mode bound is obtained from the literal overlap integral.
In particular no desired matrix contraction is an input. -/
theorem entry_norm_le_one (L : ℝ) (hL : 0 < L) (m n : ℤ) (h : ℝ) :
    ‖entry L m n h‖ ≤ 1 := by
  have hp (i j : ℤ) (t : ℝ) (ht : 0 ≤ t) : ‖entry L i j t‖ ≤ 1 := by
    by_cases hc : t ≤ L
    · rw [entry, pairing_nonpos (L / 2) (-t) _ _ (by linarith) (by linarith)]
      have hn (x : ℝ) : ‖conj (mode L i x) * mode L j (x + -t)‖ = L⁻¹ := by
        rw [mode_product L hL i j x (-t), norm_mul, norm_div, wave_norm,
          wave_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
        simp
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -(L / 2) - -t) (b := L / 2)
        (fun x _ => (hn x).le)
      have he : |L / 2 - (-(L / 2) - -t)| = L - t := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [he] at hb
      apply hb.trans
      calc
        L⁻¹ * (L - t) = (L - t) / L := by ring
        _ ≤ 1 := (div_le_one hL).mpr (by linarith)
    · rw [entry_disjoint L i j t (by rw [abs_of_nonneg ht]; linarith)]
      simp
  rcases le_or_gt 0 h with hh | hh
  · exact hp m n h hh
  · rw [show h = -(-h) by ring, entry_adjoint, Complex.norm_conj]
    exact hp n m (-h) (by linarith)

end OriginalSignedCompressedFourier
