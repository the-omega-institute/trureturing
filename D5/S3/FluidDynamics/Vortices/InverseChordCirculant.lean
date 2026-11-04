/- GID: D5/S3/FluidDynamics/Vortices/InverseChordCirculant
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Vortices/InverseChordCirculant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: spectrum of the alternating inverse-chord block product. -/

import D5.S3.Quantum.Matrix.CirculantCharpoly
import D5.S3.Fourier.SparseGeneratorFamily
import D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
import D5.S3.ArithUnits.MercaCosetFiberLift
import D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse

/-! Fourier analysis of the inverse squared chord kernel on a finite cyclic group. -/

noncomputable section
open scoped BigOperators
open Finset Matrix
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

namespace D5.S3.FluidDynamics.Vortices.InverseChordCirculant

/-- The reciprocal squared chord length, with the diagonal entry removed. -/
private def chordWeight (N : ℕ) [NeZero N] (l : ZMod N) : ℝ :=
  if l = 0 then 0 else 1 / (4 * Real.sin (Real.pi * (l.val : ℝ) / N) ^ 2)

/-- The common Fourier basis diagonalizes a product of two circulants. -/
private theorem circulant_product_det (N : ℕ) [NeZero N] (b c : ZMod N → ℂ) (y : ℂ) :
    (y • 1 - Matrix.circulant b * Matrix.circulant c).det =
      ∏ k : ZMod N, (y - ZMod.dft b k * ZMod.dft c k) := by
  classical
  have hb := circulant_spectral N b
  have hc := circulant_spectral N c
  have hd := D5.S3.Quantum.Matrix.CirculantCharpoly.transform_det_ne_zero N
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
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
  have he' := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at he'
  exact mul_left_cancel₀ hd (he'.trans (mul_comm _ _))

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
  apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hm)).mpr
  ring

/-- Alternating signs shift the Fourier modes by half the even period. -/
private theorem alternating_chord_dft (m : ℕ) [NeZero (2 * m)] (k : ZMod (2 * m)) :
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
  simpa only [sub_neg_eq_add, mul_neg, neg_neg, mul_comm] using
    D5.S3.Fourier.FullBispectrumStability.dft_translation f (-a) k

private lemma modeValue_sum (N : ℕ) [NeZero N] : ∑ k : ZMod N, modeValue N k = 0 := by
  rw [← (ZMod.finEquiv N).toEquiv.sum_comp]
  simp only [modeValue, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.fin_equiv_val]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ((N : ℂ) ^ 2 - 1) / 12 - (k : ℂ) * ((N : ℂ) - k) / 2)]
  have h2q := sum_range_pow N 2
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two] at h2q
  have h1 : (∑ k ∈ range N, (k : ℂ)) = (N : ℂ) ^ 2 / 2 - N / 2 := by
    have hq := D5.S3.ArithUnits.MercaCosetFiberLift.sum_fin_rat N (NeZero.pos N)
    rw [Fin.sum_univ_eq_sum_range] at hq
    have hc := congrArg (algebraMap ℚ ℂ) hq
    simp only [map_sum, map_sub, map_mul, map_div₀, map_natCast, map_ofNat, map_one] at hc
    linear_combination hc
  have h2 : (∑ k ∈ range N, (k : ℂ) ^ 2) =
      (N : ℂ) ^ 3 / 3 - (N : ℂ) ^ 2 / 2 + N / 6 := by
    have hq : (∑ k ∈ range N, (k : ℚ) ^ 2) =
        (N : ℚ) ^ 3 / 3 - (N : ℚ) ^ 2 / 2 + N / 6 := by
      linear_combination h2q
    have hc := congrArg (algebraMap ℚ ℂ) hq
    simpa only [map_sum, map_pow, map_sub, map_add, map_div₀, map_natCast, map_ofNat] using hc
  have ht (k : ℕ) : ((N : ℂ) ^ 2 - 1) / 12 - (k : ℂ) * ((N : ℂ) - k) / 2 =
      ((N : ℂ) ^ 2 - 1) / 12 - (N : ℂ) / 2 * k + (k : ℂ) ^ 2 / 2 := by ring
  simp_rw [ht]
  rw [sum_add_distrib, sum_sub_distrib, sum_const, ← mul_sum, ← sum_div, h1, h2]
  simp only [card_range, nsmul_eq_mul]
  ring

private lemma chord_multiplier (N : ℕ) [NeZero N] (l : ZMod N) :
    ZMod.stdAddChar l + ZMod.stdAddChar (-l) - 2 =
      -4 * (Real.sin (Real.pi * (l.val : ℝ) / N) : ℂ) ^ 2 := by
  have hp := D5.S3.Quantum.Matrix.CirculantCharpoly.character_pair N 1 l.val l.val_le
  have hnl : ((N - l.val : ℕ) : ZMod N) = -l := by
    rw [Nat.cast_sub l.val_le]
    simp
  simp only [Nat.cast_one, one_mul, ZMod.natCast_zmod_val, hnl] at hp
  rw [hp]
  have ha : 2 * Real.pi * 1 * l.val / N = 2 * (Real.pi * (l.val : ℝ) / N) := by ring
  rw [ha, Real.cos_two_mul_eq_one_sub]
  push_cast
  ring

private lemma dft_modeValue_laplacian (N : ℕ) [NeZero N] (l : ZMod N) (hl : l ≠ 0) :
    (ZMod.stdAddChar l + ZMod.stdAddChar (-l) - 2) * ZMod.dft (modeValue N) l =
      -(N : ℂ) := by
  have hs : (∑ k : ZMod N, ZMod.stdAddChar (-(k * l))) = 0 := by
    simpa only [mul_neg, neg_mul, mul_comm, ite_eq_right (neg_ne_zero.mpr hl)] using
      D5.S3.Fourier.SparseGeneratorGapObstruction.char_sum (-l)
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
    simp [chordWeight.eq_1]
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
  simp only [chordWeight.eq_1, ite_eq_right hl, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  linear_combination -h

/-- All Fourier coefficients of the inverse squared chord kernel. -/
private theorem chordWeight_dft (N : ℕ) [NeZero N] (k : ZMod N) :
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

def weights (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun j k => if j = k then 0 else
    1 / (4 * Real.sin (Real.pi * ((j.val : ℝ) - k.val) / (2 * m))^2)

def chargeMatrix (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Nat.casesOn (motive := fun n => Matrix (Fin (2*n)) (Fin (2*n)) ℝ) m 0
    (fun n => D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse.indexParity (2*n+1) 2)

lemma chargeMatrix_diagonal (m : ℕ) :
    chargeMatrix m = Matrix.diagonal (fun j => (-1 : ℝ) ^ (j.val + 2)) := by
  cases m with
  | zero => ext i; exact Fin.elim0 i
  | succ m =>
    change Matrix.diagonal (fun j : Fin (2*(m+1)) => (-1 : ℝ) ^ (2+j.val)) = _
    congr 1
    funext i
    rw [Nat.add_comm 2]

def diagonalWeight (m : ℕ) : ℝ := (((2*m : ℕ) : ℝ)^2 - 1) / 12 - (m : ℝ)^2 / 2

def blockB (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (diagonalWeight m • 1 - weights m) * chargeMatrix m

def blockC (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  ((diagonalWeight m + 1) • 1 - weights m) * chargeMatrix m

private lemma spectrum_weights (m : ℕ) [NeZero (2 * m)] :
    weights m = Matrix.circulant (fun l : Fin (2 * m) =>
      InverseChordCirculant.chordWeight (2 * m) ((ZMod.finEquiv (2 * m)) l)) := by
  ext j k
  have hz : (ZMod.finEquiv (2 * m)) (j-k) = 0 ↔ j = k := by
    constructor
    · intro h
      apply sub_eq_zero.mp
      exact (ZMod.finEquiv (2 * m)).injective (h.trans (map_zero _).symm)
    · intro h
      simp [h]
  simp only [weights, Matrix.circulant_apply, InverseChordCirculant.chordWeight, hz,
    D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.fin_equiv_val]
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [ite_eq_right hjk]
    congr 2
    have hs : ((j-k).val : ℝ) = (j.val : ℝ) - k.val +
        (if k ≤ j then 0 else (2 * m : ℝ)) := by
      exact_mod_cast Fin.intCast_val_sub_eq_sub_add_ite j k
    have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by intro h; exact NeZero.ne (2 * m) (by simp [h]))
    split_ifs at hs with hle
    · rw [hs]
      push_cast; simp
    · have ha : Real.pi * ((j-k).val : ℝ) / (2 * m) =
          Real.pi * ((j.val : ℝ)-k.val) / (2 * m) + Real.pi := by
        rw [hs]; field_simp (discharger := first | exact hmR | norm_num | positivity)
      push_cast; rw [ha, Real.sin_add_pi]; simp

theorem alternating_weight_sum (m : ℕ) (hm : 3 ≤ m) (j : Fin (2 * m)) :
    (∑ k : Fin (2*m), (-1 : ℝ) ^ (k.val + 2)*weights m j k) =
      (-1 : ℝ) ^ (j.val + 2)*diagonalWeight m := by
  classical
  have : NeZero (2*m) := ⟨by omega⟩
  let e := (ZMod.finEquiv (2 * m)).toEquiv
  have hsign (k : Fin (2 * m)) :
      (-1 : ℝ) ^ (k.val + 2) = (-1 : ℝ) ^ (j.val + 2)*(-1:ℝ)^(j-k).val := by
    simp only [← pow_add]
    rw [neg_one_pow_eq_pow_mod_two (k.val+2),
      neg_one_pow_eq_pow_mod_two (j.val+2+(j-k).val)]
    congr 1
    have h := Fin.intCast_val_sub_eq_sub_add_ite j k
    split_ifs at h <;> omega
  have hw (k : Fin (2*m)) :
      weights m j k = InverseChordCirculant.chordWeight (2*m) (e (j-k)) := by
    rw [spectrum_weights]
    rfl
  have hfourier := InverseChordCirculant.alternating_chord_dft m 0
  rw [ZMod.dft_apply_zero, zero_add, InverseChordCirculant.chordWeight_dft] at hfourier
  have hmode : (m : ZMod (2 * m)).val = m := ZMod.val_natCast_of_lt (by omega)
  rw [hmode] at hfourier
  have hsum : (∑ l : ZMod (2*m), (-1:ℝ)^l.val *
      InverseChordCirculant.chordWeight (2*m) l) = diagonalWeight m := by
    have h := congrArg Complex.re hfourier
    simp only [Complex.re_sum, Complex.ofReal_re] at h
    dsimp only [diagonalWeight]; push_cast at h ⊢
    linear_combination h
  calc
    _ = (-1 : ℝ) ^ (j.val + 2) * ∑ k : Fin (2*m), (-1:ℝ)^(j-k).val *
        InverseChordCirculant.chordWeight (2*m) (e (j-k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsign, hw]; ring
    _ = (-1 : ℝ) ^ (j.val + 2) * ∑ k : Fin (2*m), (-1:ℝ)^k.val *
        InverseChordCirculant.chordWeight (2*m) (e k) := by
      congr 1
      simpa only [Equiv.subLeft_apply] using (Equiv.subLeft j).sum_comp
        (fun k : Fin (2*m) => (-1:ℝ)^k.val * InverseChordCirculant.chordWeight (2*m) (e k))
    _ = _ := by
      rw [← hsum, ← e.sum_comp]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (e k).val = k.val from
        D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.fin_equiv_val (2*m) k]

def gamma (m : ℕ) (k : ZMod (2 * m)) : ℝ :=
  let r := min k.val (2*m - k.val)
  ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4

private lemma spectrum_mode_product (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m)
    (k : ZMod (2 * m)) :
    (diagonalWeight m + 1 -
        ((((2 * m : ℕ) : ℝ)^2-1)/12 - (k.val : ℝ)*((2 * m : ℝ)-k.val)/2)) *
      (diagonalWeight m -
        ((((2 * m : ℕ) : ℝ)^2-1)/12 - ((k+m).val : ℝ)*((2 * m : ℝ)-(k+m).val)/2)) =
      gamma m (k+m) := by
  have hklt := ZMod.val_lt k
  have hmv : (m : ZMod (2 * m)).val = m := ZMod.val_natCast_of_lt (by omega)
  by_cases hk : k.val < m
  · have hv : (k+m).val = k.val+m := by
      rw [ZMod.val_add, hmv, Nat.mod_eq_of_lt (by omega)]
    have hr : min (k+m).val (2 * m-(k+m).val) = m-k.val := by rw [hv]; omega
    have hc : ((m-k.val : ℕ) : ℝ) = (m : ℝ)-k.val :=
      Nat.cast_sub (by omega)
    delta gamma; dsimp only; rw [hr, hv, hc]
    unfold diagonalWeight; push_cast; ring
  · have hv : (k+m).val = k.val-m := by
      rw [ZMod.val_add_of_le (by rw [hmv]; omega), hmv]; omega
    have hr : min (k+m).val (2 * m-(k+m).val) = k.val-m := by rw [hv]; omega
    have hc : ((k.val-m : ℕ) : ℝ) = (k.val : ℝ)-m :=
      Nat.cast_sub (by omega)
    delta gamma; dsimp only; rw [hr, hv, hc]
    unfold diagonalWeight; push_cast; ring

theorem product_spectrum (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m) (y : ℝ) :
    (y • 1 - blockC m * blockB m).det =
      ∏ k : ZMod (2 * m), (y - gamma m k) := by
  classical
  let e := ZMod.finEquiv (2 * m)
  let R := Matrix.reindexRingEquiv ℝ e.toEquiv
  let F := Complex.ofRealHom.mapMatrix.comp R.toRingHom
  let w : ZMod (2 * m) → ℂ := fun l => (InverseChordCirculant.chordWeight (2 * m) l : ℂ)
  let u : ZMod (2 * m) → ℂ := fun l =>
    (((-1 : ℝ)^l.val * InverseChordCirculant.chordWeight (2 * m) l : ℝ) : ℂ)
  let a := diagonalWeight m
  have hscalar (r : ℝ) : F (r • 1) = (r : ℂ) • 1 := by
    change Complex.ofRealHom.mapMatrix
      (Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv (r • 1)) = _
    rw [map_smul, map_one, Matrix.smul_one_eq_diagonal, RingHom.mapMatrix_apply,
      Matrix.diagonal_map (map_zero _), ← Matrix.smul_one_eq_diagonal]
    rfl
  have hW : F (weights m) = Matrix.circulant w := by
    ext i j
    change ((weights m (e.symm i) (e.symm j) : ℝ) : ℂ) = w (i-j)
    rw [spectrum_weights]
    change (InverseChordCirculant.chordWeight (2 * m) (e (e.symm i-e.symm j)) : ℂ) = _
    rw [map_sub]; simp only [RingEquiv.apply_symm_apply]
    rfl
  have hsign (i j : Fin (2 * m)) :
      (-1 : ℝ) ^ (i.val + 2) * (-1 : ℝ) ^ (j.val + 2) = (-1 : ℝ)^(i-j).val := by
    have hs := Fin.intCast_val_sub_eq_sub_add_ite i j
    have hp : ((i.val+2)+(j.val+2)) % 2 = (i-j).val % 2 := by
      split_ifs at hs <;> push_cast at hs <;> omega
    rw [← pow_add]
    rw [neg_one_pow_eq_pow_mod_two _, neg_one_pow_eq_pow_mod_two (i-j).val, hp]
  have hU : F (chargeMatrix m * weights m * chargeMatrix m) = Matrix.circulant u := by
    ext i j
    change (((chargeMatrix m * weights m * chargeMatrix m)
      (e.symm i) (e.symm j) : ℝ) : ℂ) = u (i-j)
    simp only [chargeMatrix_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [show (-1 : ℝ) ^ ((e.symm i).val + 2) * weights m (e.symm i) (e.symm j) *
        (-1 : ℝ) ^ ((e.symm j).val + 2) =
        ((-1 : ℝ) ^ ((e.symm i).val + 2) * (-1 : ℝ) ^ ((e.symm j).val + 2)) *
          weights m (e.symm i) (e.symm j) by ring,
      hsign (e.symm i) (e.symm j), spectrum_weights]
    change (((-1 : ℝ)^(e.symm i-e.symm j).val *
      InverseChordCirculant.chordWeight (2 * m) (e (e.symm i-e.symm j)) : ℝ) : ℂ) = _
    rw [← D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories.fin_equiv_val
      (2 * m) (e.symm i-e.symm j), map_sub]
    change (((-1 : ℝ)^(e (e.symm i)-e (e.symm j)).val *
      InverseChordCirculant.chordWeight (2 * m) (e (e.symm i)-e (e.symm j)) : ℝ) : ℂ) = _
    simp only [RingEquiv.apply_symm_apply]
    rfl
  have hD : chargeMatrix m * chargeMatrix m = 1 := by
    rw [chargeMatrix_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    simp only [← pow_add]
    rw [show j.val+2+(j.val+2) = 2*(j.val+2) by omega, pow_mul]; simp
  have hCB : blockC m * blockB m =
      ((a+1) • 1 - weights m) * (a • 1 - chargeMatrix m * weights m * chargeMatrix m) := by
    change (((a+1) • 1 - weights m) * chargeMatrix m) *
      ((a • 1 - weights m) * chargeMatrix m) = _
    have hmid : (chargeMatrix m * (a • 1 - weights m)) * chargeMatrix m =
        a • 1 - chargeMatrix m * weights m * chargeMatrix m := by
      rw [mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hD]
    simpa only [Matrix.mul_assoc] using
      congrArg (fun M => ((a+1) • 1 - weights m) * M) hmid
  let b : ZMod (2 * m) → ℂ := Pi.single 0 ((a+1 : ℝ) : ℂ) - w
  let c : ZMod (2 * m) → ℂ := Pi.single 0 (a : ℂ) - u
  have hb : F ((a+1) • 1 - weights m) = Matrix.circulant b := by
    rw [map_sub, hscalar, hW]
    rw [show b = Pi.single 0 (a+1 : ℂ) - w by simp only [b, Complex.ofReal_add,
      Complex.ofReal_one], Matrix.circulant_sub, Matrix.circulant_single]
    rw [Complex.ofReal_add, Complex.ofReal_one]
    exact congrArg (fun M => M - Matrix.circulant w) (Matrix.smul_one_eq_diagonal _)
  have hc : F (a • 1 - chargeMatrix m * weights m * chargeMatrix m) = Matrix.circulant c := by
    rw [map_sub, hscalar, hU, show c = Pi.single 0 (a : ℂ) - u from rfl,
      Matrix.circulant_sub, Matrix.circulant_single]
    exact congrArg (fun M => M - Matrix.circulant u) (Matrix.smul_one_eq_diagonal _)
  have hsingle (z : ℂ) (k : ZMod (2 * m)) : ZMod.dft (Pi.single 0 z) k = z := by
    simp [ZMod.dft_apply, Pi.single_apply]
  have hmode (k : ZMod (2 * m)) :
      ZMod.dft b k * ZMod.dft c k = (gamma m (k+m) : ℂ) := by
    simp only [b, c, map_sub, Pi.sub_apply]
    rw [hsingle, hsingle]
    change (((a+1 : ℝ) : ℂ) - ZMod.dft w k) * ((a : ℂ) - ZMod.dft u k) = _
    rw [InverseChordCirculant.alternating_chord_dft,
      InverseChordCirculant.chordWeight_dft, InverseChordCirculant.chordWeight_dft]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
    simpa only [a, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg Complex.ofReal (spectrum_mode_product m hm k)
  apply Complex.ofReal_injective
  have hdet : ((y • 1 - blockC m * blockB m).det : ℂ) =
      (F (y • 1 - blockC m * blockB m)).det := by
    change _ = (Complex.ofRealHom.mapMatrix (R (y • 1 - blockC m * blockB m))).det
    rw [← Complex.ofRealHom.map_det]
    congr 1
    exact (Matrix.det_reindex_self e.toEquiv _).symm
  rw [hdet, map_sub, hscalar, hCB, map_mul, hb, hc,
    InverseChordCirculant.circulant_product_det]
  simp only [hmode]
  change _ = Complex.ofRealHom (∏ k : ZMod (2 * m), (y - gamma m k))
  rw [map_prod Complex.ofRealHom]; simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_sub]
  exact Equiv.prod_comp (Equiv.addRight (m : ZMod (2 * m)))
    (fun k => (y : ℂ) - (gamma m k : ℂ))

end D5.S3.FluidDynamics.Vortices.InverseChordCirculant
