/- GID: D5/S3/Quantum/Matrix/CirculantCharpoly
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CirculantCharpoly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic, mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Fourier characteristic factors for circulants and paired cosine factors for odd real symmetric circulants. -/

import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option maxHeartbeats 2000000

noncomputable section
open Finset Matrix Polynomial Complex
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.CirculantCharpoly

variable (n : ℕ) [NeZero n]

theorem circulant_charpoly (b : ZMod n → ℂ) :
    (Matrix.circulant b).charpoly = ∏ j : ZMod n, (X - C (ZMod.dft b j)) := by
  have hs := D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.circulant_spectral n b
  have hu := D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform_unitary n
  have hi : IsUnit (D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform n) :=
    isUnit_iff_exists_inv.mpr
      ⟨(D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform n)ᴴ, hu⟩
  have hd : (D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform n).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hi).ne_zero
  have hcp := Matrix.charpoly_eq_of_mul_eq_mul hd hs.symm
  change (Matrix.diagonal (ZMod.dft b)).charpoly = (Matrix.circulant b).charpoly at hcp
  rw [Matrix.charpoly_diagonal] at hcp
  exact hcp.symm

theorem dft_real_of_even (b : ZMod n → ℝ) (hb : ∀ k, b (-k) = b k) (j : ZMod n) :
    ZMod.dft (fun k => (b k : ℂ)) j = (ZMod.dft (fun k => (b k : ℂ)) j).re := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal,
    ← AddChar.map_neg_eq_conj, neg_neg]
  apply Fintype.sum_equiv (Equiv.neg (ZMod n))
  intro k
  simp only [Equiv.neg_apply, neg_mul, neg_neg, hb]

theorem real_circulant_charpoly (b : ZMod n → ℝ) (hb : ∀ k, b (-k) = b k) :
    (Matrix.circulant b).charpoly =
      ∏ j : ZMod n, (X - C (ZMod.dft (fun k => (b k : ℂ)) j).re) := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← Matrix.charpoly_map, Matrix.map_circulant, circulant_charpoly]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro j _
  change (X - C (ZMod.dft (fun k => (b k : ℂ)) j) : ℂ[X]) =
    X - C ((ZMod.dft (fun k => (b k : ℂ)) j).re : ℂ)
  exact congrArg (fun z : ℂ => (X - C z : ℂ[X])) (dft_real_of_even n b hb j)

def realCirculant (m : ℕ) (f : ℕ → ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.circulant (fun k => f k.val)

def cosineValue (m : ℕ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  f 0 + 2 * ∑ l ∈ Icc 1 m, f l * Real.cos (2 * Real.pi * j * l / (2 * m + 1))

@[to_additive]
private lemma odd_prod {A : Type*} [CommMonoid A] (m : ℕ) (g : ℕ → A) :
    (∏ k ∈ range (2 * m + 1), g k) =
      g 0 * ∏ l ∈ Icc 1 m, (g l * g (2 * m + 1 - l)) := by
  have hs : (∏ i ∈ range m, g (1 + (m + i))) =
      ∏ i ∈ range m, g (2 * m + 1 - (1 + i)) := by
    rw [← prod_range_reflect (fun i => g (1 + (m + i))) m]
    apply prod_congr rfl
    intro i hi
    congr 1
    have := mem_range.mp hi
    omega
  rw [show 2 * m + 1 = 1 + (m + m) by omega, prod_range_add,
    prod_range_one, prod_range_add, hs]
  rw [← prod_mul_distrib, ← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, show 1 + (m + m) = 2 * m + 1 by omega]

private lemma character_pair (n : ℕ) [NeZero n] (j l : ℕ) (hl : l ≤ n) :
    ZMod.stdAddChar ((j : ZMod n) * (l : ZMod n)) +
      ZMod.stdAddChar ((j : ZMod n) * ((n - l : ℕ) : ZMod n)) =
        (2 * Real.cos (2 * Real.pi * j * l / n) : ℝ) := by
  have hn : ((n - l : ℕ) : ZMod n) = -(l : ZMod n) := by
    rw [Nat.cast_sub hl]
    simp
  rw [hn, mul_neg, AddChar.map_neg_eq_conj]
  have he : ZMod.stdAddChar ((j : ZMod n) * (l : ZMod n)) =
      Complex.exp ((2 * Real.pi * j * l / n : ℝ) * I) := by
    have h := ZMod.stdAddChar_coe (N := n) ((j * l : ℕ) : ℤ)
    push_cast at h
    rw [h]
    congr 1
    push_cast
    ring
  rw [he, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hc := (Complex.two_cos (((2 * Real.pi * j * l / n : ℝ) : ℂ))).symm
  push_cast at hc ⊢
  simpa only [mul_neg, neg_mul] using hc

private lemma dft_eq_cosineComplex (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k)
    (j : ZMod (2 * m + 1)) :
    ZMod.dft (fun k => (f k.val : ℂ)) j = (cosineValue m f j.val : ℂ) := by
  classical
  rw [ZMod.dft_apply]
  rw [← (ZMod.finEquiv (2 * m + 1)).toEquiv.sum_comp]
  simp only [smul_eq_mul]
  have hfin_val (x : Fin (2 * m + 1)) :
      ((ZMod.finEquiv (2 * m + 1)).toEquiv x).val = x.val := by
    simp only [ZMod.finEquiv]
    change x.val = x.val
    rfl
  have hcast_val (x : Fin (2 * m + 1)) :
      ((x.val : ZMod (2 * m + 1)).val) = x.val := by
    exact ZMod.val_cast_of_lt x.isLt
  have hfin (x : Fin (2 * m + 1)) :
      (ZMod.finEquiv (2 * m + 1)).toEquiv x = (x.val : ZMod (2 * m + 1)) := by
    apply (ZMod.val_injective (2 * m + 1))
    rw [hfin_val]
    simp [ZMod.val_cast_of_lt x.isLt]
  simp only [hfin, hcast_val]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ZMod.stdAddChar (-((k : ZMod (2 * m + 1)) * j)) * (f k : ℂ)), odd_sum]
  simp only [Nat.cast_zero, zero_mul, AddChar.map_zero_eq_one, one_mul,
    Complex.ofReal_zero, add_zero]
  rw [cosineValue]
  congr 1
  push_cast
  simp only [neg_zero, AddChar.map_zero_eq_one, one_mul]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro l hl
  have hl' := mem_Icc.mp hl
  have hpair :
      ZMod.stdAddChar (-(l : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) +
        ZMod.stdAddChar (-((2 * m + 1 - l : ℕ) : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) =
        (2 * Real.cos (2 * Real.pi * j.val * l / (2 * m + 1)) : ℂ) := by
    rw [show -(l : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1)) =
      -((j.val : ZMod (2 * m + 1)) * (l : ZMod (2 * m + 1))) by
        simp [mul_comm, ZMod.natCast_zmod_val]]
    rw [show -((2 * m + 1 - l : ℕ) : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1)) =
      -((j.val : ZMod (2 * m + 1)) * ((2 * m + 1 - l : ℕ) : ZMod (2 * m + 1))) by
        simp [mul_comm, ZMod.natCast_zmod_val]]
    rw [AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj]
    have hpos := character_pair (2 * m + 1) j.val l (by omega)
    rw [← map_add, hpos]
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [hf l (mem_Icc.mpr ⟨hl'.1, by omega⟩)]
  rw [← add_mul]
  have hsum :
      ZMod.stdAddChar (-(l : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) +
        ZMod.stdAddChar (-((2 * m + 1 - l : ℕ) : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) =
        2 * (cos (2 * Real.pi * j.val * l / (2 * m + 1)) : ℂ) := by
    convert hpair using 1 <;> simp [Complex.ofReal_cos] <;> (try congr 1) <;> ring
  have hsum' :
      ZMod.stdAddChar (-(l : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) +
        ZMod.stdAddChar (-((2 * m + 1 - l : ℕ) : ZMod (2 * m + 1)) * (j : ZMod (2 * m + 1))) =
        2 * (cos (2 * Real.pi * j.val * l / (2 * m + 1)) : ℂ) := by
    simpa [neg_mul] using hsum
  simp only [neg_mul] at *
  rw [hsum']
  ring


private lemma dft_eq_cosineValue (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k)
    (j : ZMod (2 * m + 1)) :
    (ZMod.dft (fun k => (f k.val : ℂ)) j).re = cosineValue m f j.val := by
  rw [dft_eq_cosineComplex m f hf j]
  simp

private lemma cosineValue_reflect (m : ℕ) (f : ℕ → ℝ) (j : ℕ)
    (hj : j ≤ 2 * m + 1) :
    cosineValue m f (2 * m + 1 - j) = cosineValue m f j := by
  unfold cosineValue
  congr 2
  apply sum_congr rfl
  intro l _
  congr 1
  rw [Nat.cast_sub hj]
  push_cast
  have hn : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  rw [show 2 * Real.pi * (2 * (m : ℝ) + 1 - j) * l / (2 * (m : ℝ) + 1) =
    (l : ℝ) * (2 * Real.pi) - 2 * Real.pi * j * l / (2 * (m : ℝ) + 1) by
      field_simp]
  exact Real.cos_nat_mul_two_pi_sub _ l

theorem realCirculant_charpoly (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k) :
    (realCirculant m f).charpoly =
      (X - C (cosineValue m f 0)) *
        ∏ j ∈ Icc 1 m, (X - C (cosineValue m f j)) ^ 2 := by
  classical
  let b : ZMod (2 * m + 1) → ℝ := fun k => f k.val
  have hb : ∀ k, b (-k) = b k := by
    intro k
    change f (-k).val = f k.val
    by_cases hk : k = 0
    · rw [ZMod.neg_val, if_pos hk]
      simp [hk]
    · have hkval : k.val ≠ 0 := by
        intro h
        exact hk (ZMod.val_eq_zero k |>.mp h)
      rw [ZMod.neg_val, if_neg hk]
      have hklt : k.val < 2 * m + 1 := k.val_lt
      exact hf k.val (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hkval, by omega⟩)
  have hc := real_circulant_charpoly (2 * m + 1) b hb
  rw [show (realCirculant m f).charpoly = (Matrix.circulant b).charpoly by
    rfl, hc]
  rw [← (ZMod.finEquiv (2 * m + 1)).toEquiv.prod_comp]
  simp only [b]
  simp_rw [dft_eq_cosineValue m f hf]
  have hfin_val (x : Fin (2 * m + 1)) :
      ((ZMod.finEquiv (2 * m + 1)).toEquiv x).val = x.val := by
    simp only [ZMod.finEquiv]
    change x.val = x.val
    rfl
  have hcast_val (x : Fin (2 * m + 1)) :
      ((x.val : ZMod (2 * m + 1)).val) = x.val := by
    exact ZMod.val_cast_of_lt x.isLt
  simp_rw [hfin_val]
  rw [Fin.prod_univ_eq_prod_range
    (fun j : ℕ => (X - C (cosineValue m f j) : ℝ[X]))]
  change (∏ j ∈ range (2 * m + 1), (X - C (cosineValue m f j))) =
    (X - C (cosineValue m f 0)) *
      ∏ j ∈ Icc 1 m, (X - C (cosineValue m f j)) ^ 2
  rw [odd_prod]
  apply congrArg (fun p : ℝ[X] => (X - C (cosineValue m f 0)) * p)
  apply prod_congr rfl
  intro j hj
  rw [cosineValue_reflect m f j (by have := (mem_Icc.mp hj).2; omega), pow_two]

end D5.S3.Quantum.Matrix.CirculantCharpoly
