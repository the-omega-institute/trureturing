/- GID: D5/S3/FluidDynamics/Vortices/InverseChordCirculant
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Vortices/InverseChordCirculant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fourier values of inverse squared chord weights and products of circulants. -/

import D5.S3.Quantum.Matrix.CirculantCharpoly
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Bernoulli

/-! Fourier analysis of the inverse squared chord kernel on a finite cyclic group. -/

noncomputable section
open scoped BigOperators
open Finset Matrix
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

namespace D5.S3.FluidDynamics.Vortices.InverseChordCirculant

/-- The reciprocal squared chord length, with the diagonal entry removed. -/
def chordWeight (N : ℕ) [NeZero N] (l : ZMod N) : ℝ :=
  if l = 0 then 0 else 1 / (4 * Real.sin (Real.pi * (l.val : ℝ) / N) ^ 2)

/-- The common Fourier basis diagonalizes a product of two circulants. -/
theorem circulant_product_det (N : ℕ) [NeZero N] (b c : ZMod N → ℂ) (y : ℂ) :
    (y • 1 - Matrix.circulant b * Matrix.circulant c).det =
      ∏ k : ZMod N, (y - ZMod.dft b k * ZMod.dft c k) := by
  classical
  have hb := circulant_spectral N b
  have hc := circulant_spectral N c
  have hu := transform_unitary N
  have hi : IsUnit (transform N) := isUnit_iff_exists_inv.mpr ⟨(transform N)ᴴ, hu⟩
  have hd : (transform N).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hi).ne_zero
  have he : transform N * (y • 1 - Matrix.circulant b * Matrix.circulant c) =
      Matrix.diagonal (fun k => y - ZMod.dft b k * ZMod.dft c k) * transform N := by
    rw [mul_sub, Matrix.mul_smul, mul_one, ← mul_assoc, hb, mul_assoc, hc, ← mul_assoc]
    rw [Matrix.diagonal_mul_diagonal]
    change y • transform N - Matrix.diagonal (fun k => ZMod.dft b k * ZMod.dft c k) *
      transform N = _
    have hy : y • transform N = (y • (1 : Matrix (ZMod N) (ZMod N) ℂ)) * transform N := by
      rw [Matrix.smul_mul, one_mul]
    rw [hy, ← sub_mul]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h]
  have he' := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at he'
  exact mul_left_cancel₀ hd (by simpa only [mul_comm (transform N).det] using he')

private lemma half_character (m : ℕ) [NeZero (2 * m)] :
    ZMod.stdAddChar (m : ZMod (2 * m)) = (-1 : ℂ) := by
  have hm : (m : ℂ) ≠ 0 := by
    have h : m ≠ 0 := by
      intro h
      exact NeZero.ne (2 * m) (by simp [h])
    exact_mod_cast h
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  push_cast
  convert Complex.exp_pi_mul_I using 1
  congr 1
  field_simp

/-- Alternating signs shift the Fourier modes by half the even period. -/
theorem alternating_chord_dft (m : ℕ) [NeZero (2 * m)] (k : ZMod (2 * m)) :
    ZMod.dft (fun l => (((-1 : ℝ) ^ l.val * chordWeight (2 * m) l : ℝ) : ℂ)) k =
      ZMod.dft (fun l => (chordWeight (2 * m) l : ℂ)) (k + m) := by
  have hchar (l : ZMod (2 * m)) :
      ZMod.stdAddChar (-(l * (m : ZMod (2 * m)))) = (-1 : ℂ) ^ l.val := by
    calc
      _ = ZMod.stdAddChar (l.val • (-(m : ZMod (2 * m)))) := by
        congr 1
        simp [nsmul_eq_mul]
      _ = ZMod.stdAddChar (-(m : ZMod (2 * m))) ^ l.val :=
        AddChar.map_nsmul_eq_pow _ _ _
      _ = _ := by rw [AddChar.map_neg_eq_inv, half_character]; simp
  simp only [ZMod.dft_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_add, neg_add, AddChar.map_add_eq_mul, hchar]
  ring

private def modeValue (N : ℕ) [NeZero N] (k : ZMod N) : ℂ :=
  ((N : ℂ) ^ 2 - 1) / 12 - (k.val : ℂ) * ((N : ℂ) - k.val) / 2

private lemma modeValue_even (N : ℕ) [NeZero N] (k : ZMod N) :
    modeValue N (-k) = modeValue N k := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [modeValue, modeValue, ZMod.neg_val, ite_eq_right hk, Nat.cast_sub k.val_le]
    ring

private lemma modeValue_laplacian (N : ℕ) [NeZero N] (k : ZMod N) :
    modeValue N (k + 1) + modeValue N (k - 1) - 2 * modeValue N k =
      if k = 0 then 1 - (N : ℂ) else 1 := by
  by_cases hN : N = 1
  · subst N
    have hk : k = 0 := Subsingleton.elim _ _
    rw [show k + 1 = 0 from Subsingleton.elim _ _,
      show k - 1 = 0 from Subsingleton.elim _ _, hk]
    norm_num [modeValue]
  have hN1 : 1 < N := by have := NeZero.pos N; omega
  have hv1 : (1 : ZMod N).val = 1 := ZMod.val_one'' hN
  by_cases hk : k = 0
  · subst k
    have h1 : (1 : ZMod N) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      simp [hv1] at hv
    simp only [zero_add, zero_sub, modeValue, ZMod.val_zero]
    rw [ZMod.neg_val, ite_eq_right h1, hv1, Nat.cast_sub (by omega : 1 ≤ N)]
    push_cast
    ring
  have hkpos : 0 < k.val := ZMod.val_pos.mpr hk
  have hkm : (k - 1).val = k.val - 1 := by
    rw [ZMod.val_sub (show (1 : ZMod N).val ≤ k.val from by omega), hv1]
  rw [ite_eq_right hk, modeValue, modeValue, modeValue, hkm,
    Nat.cast_sub (by omega : 1 ≤ k.val)]
  by_cases htop : k.val + 1 < N
  · rw [ZMod.val_add_of_lt (by simpa [hv1] using htop), hv1]
    push_cast
    ring
  · have htop' : k.val + 1 = N := by have := k.val_lt; omega
    rw [ZMod.val_add, hv1, htop', Nat.mod_self]
    have hkc : (k.val : ℂ) + 1 = N := by exact_mod_cast htop'
    push_cast
    rw [← hkc]
    ring

private lemma dft_shift (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (a k : ZMod N) :
    ZMod.dft (fun j => f (j + a)) k =
      ZMod.stdAddChar (a * k) * ZMod.dft f k := by
  have h := congr_fun (Fourier.fourierIntegral_comp_add_right ZMod.toCircle
    MeasureTheory.Measure.count f a) k
  rw [← ZMod.dft_eq_fourier, ← ZMod.dft_eq_fourier] at h
  simpa only [Function.comp_def, Circle.smul_def, smul_eq_mul, ZMod.stdAddChar_apply] using h

private lemma modeValue_sum (N : ℕ) [NeZero N] : ∑ k : ZMod N, modeValue N k = 0 := by
  rw [← (ZMod.finEquiv N).toEquiv.sum_comp]
  have hv (k : Fin N) : ((ZMod.finEquiv N).toEquiv k).val = k.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N => rfl
  simp only [modeValue, hv]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ((N : ℂ) ^ 2 - 1) / 12 - (k : ℂ) * ((N : ℂ) - k) / 2)]
  have h1q := sum_range_pow N 1
  have h2q := sum_range_pow N 2
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two] at h1q h2q
  have h1 : (∑ k ∈ range N, (k : ℂ)) = (N : ℂ) ^ 2 / 2 - N / 2 := by
    have hq : (∑ k ∈ range N, (k : ℚ)) = (N : ℚ) ^ 2 / 2 - N / 2 := by
      linear_combination h1q
    have hc := congrArg (algebraMap ℚ ℂ) hq
    push_cast at hc
    exact hc
  have h2 : (∑ k ∈ range N, (k : ℂ) ^ 2) =
      (N : ℂ) ^ 3 / 3 - (N : ℂ) ^ 2 / 2 + N / 6 := by
    have hq : (∑ k ∈ range N, (k : ℚ) ^ 2) =
        (N : ℚ) ^ 3 / 3 - (N : ℚ) ^ 2 / 2 + N / 6 := by
      linear_combination h2q
    have hc := congrArg (algebraMap ℚ ℂ) hq
    push_cast at hc
    exact hc
  have ht (k : ℕ) : ((N : ℂ) ^ 2 - 1) / 12 - (k : ℂ) * ((N : ℂ) - k) / 2 =
      ((N : ℂ) ^ 2 - 1) / 12 - (N : ℂ) / 2 * k + (k : ℂ) ^ 2 / 2 := by ring
  simp_rw [ht]
  rw [sum_add_distrib, sum_sub_distrib, sum_const, ← mul_sum, ← sum_div, h1, h2]
  simp only [card_range, nsmul_eq_mul]
  ring

private lemma chord_multiplier (N : ℕ) [NeZero N] (l : ZMod N) :
    ZMod.stdAddChar l + ZMod.stdAddChar (-l) - 2 =
      -4 * (Real.sin (Real.pi * (l.val : ℝ) / N) : ℂ) ^ 2 := by
  let t : ℝ := Real.pi * (l.val : ℝ) / N
  have he : ZMod.stdAddChar l = Complex.exp ((2 * t : ℝ) * Complex.I) := by
    rw [← ZMod.natCast_zmod_val l, ← Int.cast_natCast, ZMod.stdAddChar_coe]
    congr 1
    dsimp [t]
    push_cast
    ring
  rw [AddChar.map_neg_eq_conj, he, Complex.exp_ofReal_mul_I]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [Real.cos_two_mul_eq_one_sub]
  push_cast
  dsimp [t]
  push_cast
  ring

private lemma dft_modeValue_laplacian (N : ℕ) [NeZero N] (l : ZMod N) (hl : l ≠ 0) :
    (ZMod.stdAddChar l + ZMod.stdAddChar (-l) - 2) * ZMod.dft (modeValue N) l =
      -(N : ℂ) := by
  have hs : (∑ k : ZMod N, ZMod.stdAddChar (-(k * l))) = 0 := by
    simpa only [AddChar.mulShift_apply, mul_neg, neg_mul, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N (neg_ne_zero.mpr hl)))
  have hd : ZMod.dft (fun k =>
      modeValue N (k + 1) + modeValue N (k - 1) - 2 * modeValue N k) l = -(N : ℂ) := by
    rw [ZMod.dft_apply]
    simp_rw [smul_eq_mul, modeValue_laplacian]
    have he (k : ZMod N) :
        ZMod.stdAddChar (-(k * l)) * (if k = 0 then 1 - (N : ℂ) else 1) =
          ZMod.stdAddChar (-(k * l)) - (if k = 0 then (N : ℂ) else 0) := by
      by_cases hk : k = 0 <;> simp [hk]
    simp_rw [he]
    rw [sum_sub_distrib, hs]
    simp
  have hfun : (fun k => modeValue N (k + 1) + modeValue N (k - 1) - 2 * modeValue N k) =
      (fun k => modeValue N (k + 1)) + (fun k => modeValue N (k + -1)) -
        (fun k => (2 : ℂ) * modeValue N k) := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg]
  rw [hfun, map_sub, map_add, ZMod.dft_const_mul] at hd
  simp only [Pi.sub_apply, Pi.add_apply, dft_shift, one_mul, neg_one_mul] at hd
  linear_combination hd

private lemma modeValue_dft (N : ℕ) [NeZero N] :
    ZMod.dft (modeValue N) = fun l => (N : ℂ) * (chordWeight N l : ℂ) := by
  funext l
  by_cases hl : l = 0
  · subst l
    rw [ZMod.dft_apply_zero, modeValue_sum]
    simp [chordWeight]
  have h := dft_modeValue_laplacian N l hl
  rw [chord_multiplier] at h
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlpos : (0 : ℝ) < l.val := by exact_mod_cast ZMod.val_pos.mpr hl
  have hllt : (l.val : ℝ) < N := by exact_mod_cast l.val_lt
  have ha0 : 0 < Real.pi * (l.val : ℝ) / N := div_pos (mul_pos Real.pi_pos hlpos) hN
  have haπ : Real.pi * (l.val : ℝ) / N < Real.pi := by
    apply (div_lt_iff₀ hN).mpr
    exact mul_lt_mul_of_pos_left hllt Real.pi_pos
  have hs : (Real.sin (Real.pi * (l.val : ℝ) / N) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi ha0 haπ).ne'
  simp only [chordWeight, ite_eq_right hl, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  linear_combination -h

/-- All Fourier coefficients of the inverse squared chord kernel. -/
theorem chordWeight_dft (N : ℕ) [NeZero N] (k : ZMod N) :
    ZMod.dft (fun l => (chordWeight N l : ℂ)) k =
      ((((N : ℝ) ^ 2 - 1) / 12 - (k.val : ℝ) * ((N : ℝ) - k.val) / 2 : ℝ) : ℂ) := by
  have h := congr_fun (congrArg (ZMod.dft (N := N) (E := ℂ)) (modeValue_dft N)) k
  rw [ZMod.dft_dft, ZMod.dft_const_mul] at h
  simp only [smul_eq_mul] at h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have he := mul_left_cancel₀ hN h
  rw [modeValue_even] at he
  rw [← he, modeValue]
  push_cast
  ring

#print axioms circulant_product_det
#print axioms alternating_chord_dft
#print axioms chordWeight_dft

end D5.S3.FluidDynamics.Vortices.InverseChordCirculant
