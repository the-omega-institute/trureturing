/- GID: D5/S3/Quantum/Matrix/CirculantCharpoly
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CirculantCharpoly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic, mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Fourier eigenvectors and paired characteristic factors for odd real symmetric circulants. -/

import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! Fourier modes and characteristic factors, including real odd-order pairing. -/

noncomputable section
open Finset Matrix Polynomial Complex
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.CirculantCharpoly

private abbrev toZ (n : ℕ) [NeZero n] := ZMod.finEquiv n

/-- The positive primitive complex root used for the Fourier modes. -/
def root (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / n)

/-- The eigenvalue with a positive Fourier exponent. -/
def fourierValue {n : ℕ} (v : Fin n → ℂ) (j : Fin n) : ℂ :=
  ∑ k : Fin n, v k * root n ^ (j.val * k.val)

private lemma toZ_eq_cast {n : ℕ} [NeZero n] (j : Fin n) :
    toZ n j = (j.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (Fin.cast_val_eq_self j).symm

private lemma character_eq_pow {n : ℕ} [NeZero n] (j k : Fin n) :
    ZMod.stdAddChar (toZ n j * toZ n k) = root n ^ (j.val * k.val) := by
  rw [toZ_eq_cast, toZ_eq_cast, ← Nat.cast_mul]
  have h (a : ℕ) : ZMod.stdAddChar (a : ZMod n) = ZMod.stdAddChar (1 : ZMod n) ^ a := by
    simpa using AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := n)) a 1
  rw [h]
  congr 1
  simpa [root] using ZMod.stdAddChar_coe (N := n) (1 : ℤ)

/-- Fourier vectors, with the negative exponent for Mathlib's circulant convention. -/
def fourierVector {n : ℕ} [NeZero n] (j : Fin n) (k : Fin n) : ℂ :=
  ZMod.stdAddChar (-(toZ n j * toZ n k))

/-- The Fourier vectors form a basis, transported from the invertible discrete transform. -/
def fourierBasis (n : ℕ) [NeZero n] : Module.Basis (Fin n) ℂ (Fin n → ℂ) :=
  ((Pi.basisFun ℂ (ZMod n)).map (ZMod.dft (N := n))).reindex (toZ n).toEquiv.symm |>.map
    (LinearEquiv.funCongrLeft ℂ ℂ (toZ n).toEquiv)

private lemma fourierBasis_apply {n : ℕ} [NeZero n] (j k : Fin n) :
    fourierBasis n j k = fourierVector j k := by
  classical
  simp [fourierBasis, Module.Basis.reindex_apply,
    Pi.basisFun_apply, ZMod.dft_apply, fourierVector, Pi.single_apply]

/-- The Fourier vectors are eigenvectors with the positive-exponent eigenvalue. -/
theorem circulant_mulVec_fourier {n : ℕ} [NeZero n] (v : Fin n → ℂ) (j : Fin n) :
    Matrix.circulant v *ᵥ fourierVector j = fourierValue v j • fourierVector j := by
  classical
  let e := (toZ n).toEquiv
  let b : ZMod n → ℂ := fun k => v (e.symm (-k))
  have hv : ZMod.dft b (e j) = fourierValue v j := by
    rw [ZMod.dft_apply, fourierValue]
    refine Fintype.sum_equiv ((Equiv.neg (ZMod n)).trans e.symm) _ _ ?_
    intro k
    simp only [Equiv.trans_apply, Equiv.neg_apply, smul_eq_mul, b]
    rw [← character_eq_pow]
    change ZMod.stdAddChar (-(k * e j)) * v (e.symm (-k)) =
      v (e.symm (-k)) * ZMod.stdAddChar (e j * e (e.symm (-k)))
    rw [e.apply_symm_apply]
    simp only [mul_comm, mul_neg, neg_mul]
  have hs := D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.circulant_spectral n b
  ext a
  let S : ℂ := Real.sqrt n
  have hS : S ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos n)))
  have heq := congrArg (fun M : Matrix (ZMod n) (ZMod n) ℂ => M (e j) (e a)) hs
  rw [Matrix.mul_apply, Matrix.diagonal_mul] at heq
  change (∑ k : ZMod n, (ZMod.stdAddChar (-(e j * k)) / S) * b (k - e a)) =
    ZMod.dft b (e j) * (ZMod.stdAddChar (-(e j * e a)) / S) at heq
  rw [hv] at heq
  have hsum : (∑ k : ZMod n, (ZMod.stdAddChar (-(e j * k)) / S) * b (k - e a)) =
      (Matrix.circulant v *ᵥ fourierVector j) a / S := by
    simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, Finset.sum_div]
    refine Fintype.sum_equiv e.symm _ _ ?_
    intro k
    have hk : e.symm (-(k - e a)) = a - e.symm k := by
      rw [neg_sub]
      exact (toZ n).symm.map_sub (e a) k |>.trans (by rw [(toZ n).symm_apply_apply])
    simp only [b, hk, fourierVector]
    change _ = v (a - e.symm k) * ZMod.stdAddChar (-(e j * e (e.symm k))) / S
    rw [e.apply_symm_apply]
    ring
  rw [hsum] at heq
  apply (div_left_inj' hS).mp
  simpa only [Pi.smul_apply, smul_eq_mul, fourierVector, div_eq_mul_inv, mul_assoc] using heq

/-- The complete complex characteristic polynomial of a circulant. -/
theorem circulant_charpoly {n : ℕ} [NeZero n] (v : Fin n → ℂ) :
    (Matrix.circulant v).charpoly = ∏ j : Fin n, (X - C (fourierValue v j)) := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := fun a j => fourierVector j a
  have hcols : P.col = fourierBasis n := by
    ext j a
    exact (fourierBasis_apply j a).symm
  have hu : IsUnit P := Matrix.linearIndependent_col_iff_isUnit.mp (by
    rw [hcols]
    exact (fourierBasis n).linearIndependent)
  have hd : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hu).ne_zero
  have hs : Matrix.circulant v * P = P * Matrix.diagonal (fourierValue v) := by
    ext a j
    have h := congr_fun (circulant_mulVec_fourier v j) a
    simpa only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.mulVec,
      dotProduct, Pi.smul_apply, smul_eq_mul, P, mul_comm] using h
  rw [Matrix.charpoly_eq_of_mul_eq_mul hd hs, Matrix.charpoly_diagonal]

/-- A real circulant specified by its values at natural residue representatives. -/
def realCirculant (m : ℕ) (f : ℕ → ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.circulant (fun k => f k.val)

/-- The real cosine expression for the mode indexed by a natural number. -/
def cosineValue (m : ℕ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  f 0 + 2 * ∑ l ∈ Icc 1 m, f l * Real.cos (2 * Real.pi * j * l / (2 * m + 1))

@[to_additive odd_sum]
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
      ZMod.stdAddChar ((j : ZMod n) * (n - l : ℕ)) =
        (2 * Real.cos (2 * Real.pi * j * l / n) : ℝ) := by
  have hn : ((n - l : ℕ) : ZMod n) = -(l : ZMod n) := by
    rw [Nat.cast_sub hl]
    simp
  rw [hn, mul_neg, AddChar.map_neg_eq_conj]
  have he : ZMod.stdAddChar ((j : ZMod n) * (l : ZMod n)) =
      Complex.exp ((2 * Real.pi * j * l / n : ℝ) * I) := by
    rw [← Nat.cast_mul]
    have h := ZMod.stdAddChar_coe (N := n) ((j * l : ℕ) : ℤ)
    push_cast at h
    rw [h]
    congr 1
    push_cast
    ring
  rw [he, ← Complex.exp_conj]
  push_cast
  rw [Complex.conj_mul, Complex.conj_ofReal, Complex.conj_I]
  have := Complex.two_cos (((2 * Real.pi * j * l / n : ℝ) : ℂ))
  simpa only [mul_neg, neg_mul, Complex.ofReal_cos] using this.symm

private lemma fourierValue_eq_cosineValue (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k)
    (j : Fin (2 * m + 1)) :
    fourierValue (fun k : Fin (2 * m + 1) => (f k.val : ℂ)) j =
      (cosineValue m f j.val : ℂ) := by
  classical
  simp only [fourierValue, ← character_eq_pow, toZ_eq_cast]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (f k : ℂ) *
    ZMod.stdAddChar ((j.val : ZMod (2 * m + 1)) * (k : ZMod (2 * m + 1))))]
  rw [odd_sum]
  simp only [Nat.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  rw [cosineValue]
  push_cast
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  have hl' := mem_Icc.mp hl
  rw [hf l (mem_Icc.mpr ⟨hl'.1, by omega⟩), ← mul_add,
    character_pair _ _ _ (by omega)]
  push_cast
  ring

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

/-- Odd-order real symmetric circulants have one constant mode and paired cosine factors. -/
theorem realCirculant_charpoly (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Icc 1 (2 * m), f (2 * m + 1 - k) = f k) :
    (realCirculant m f).charpoly =
      (X - C (cosineValue m f 0)) *
        ∏ j ∈ Icc 1 m, (X - C (cosineValue m f j)) ^ 2 := by
  classical
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  simp only [realCirculant, Matrix.map_circulant, circulant_charpoly,
    Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  change (∏ j : Fin (2 * m + 1),
    (X - C (fourierValue (fun k : Fin (2 * m + 1) => (f k.val : ℂ)) j))) = _
  simp_rw [fourierValue_eq_cosineValue m f hf]
  rw [Fin.prod_univ_eq_prod_range]
  change (∏ j ∈ range (2 * m + 1), (X - C (cosineValue m f j : ℂ))) = _
  rw [odd_prod]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [cosineValue_reflect m f j (by have := (mem_Icc.mp hj).2; omega), pow_two]

end D5.S3.Quantum.Matrix.CirculantCharpoly
