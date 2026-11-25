/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.pure_replacement_for_equal_moduli; instance=D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.one_zero_feasible
   digest: A real complementary plane gives a pure replacement with the same diagonal. -/

import D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Basic.Complex.BigOperators

/-! # Diagonal-preserving pure replacement in a real complementary plane

The plane result has a joint-numerical-range antecedent in Li and Poon,
*Convexity of the Joint Numerical Range* (2000), Theorems 1.2 and 3.1.
The proof here factors the real part of the two-dimensional compression.
-/

set_option autoImplicit false

open scoped BigOperators ComplexOrder Matrix MatrixOrder

noncomputable section

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityRealCompression

open Matrix
open D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
  (real_gram_entry complete_real_pair complex_gram_re complex_gram_im)

private def realColumns (z : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 2) ℝ :=
  Matrix.of fun i j => Real.sqrt 2 * (![(z i).re, (z i).im] : Fin 2 → ℝ) j

private theorem realColumns_gram (z : Fin 4 → ℂ)
    (hunit : star z ⬝ᵥ z = 1) (horth : star (star z) ⬝ᵥ z = 0) :
    (realColumns z)ᵀ * realColumns z = 1 := by
  let Z : Matrix (Fin 4) (Fin 2) ℂ := Matrix.of fun i j => (![star z, z] : Fin 2 → Fin 4 → ℂ) j i
  have hg11 : (Zᴴ * Z) 1 1 = 1 := hunit
  have hg01 : (Zᴴ * Z) 0 1 = 0 := horth
  let x : Fin 4 → ℝ := fun i => (z i).re
  let y : Fin 4 → ℝ := fun i => (z i).im
  have h11 := complex_gram_re Z 1 1
  have h01 := complex_gram_re Z 0 1
  have hi01 := complex_gram_im Z 0 1
  have hxy : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm _ _
  have hx0 : (fun i => (Z i 0).re) = x := by
    funext i
    change (star (z i)).re = (z i).re
    simp [Complex.star_def]
  have hy0 : (fun i => (Z i 0).im) = -y := by
    funext i
    change (star (z i)).im = -(z i).im
    simp [Complex.star_def]
  have hx1 : (fun i => (Z i 1).re) = x := rfl
  have hy1 : (fun i => (Z i 1).im) = y := rfl
  simp only [hg11, Complex.one_re, hx1, hy1] at h11
  simp only [hg01, Complex.zero_re, hx0, hx1, hy0, hy1, neg_dotProduct] at h01
  simp only [hg01, Complex.zero_im, hx0, hx1, hy0, hy1, neg_dotProduct, hxy] at hi01
  have hxx : x ⬝ᵥ x = 1 / 2 := by linarith only [h11, h01]
  have hyy : y ⬝ᵥ y = 1 / 2 := by linarith only [h11, h01]
  have hzero : x ⬝ᵥ y = 0 := by linarith only [hi01]
  let k := Real.sqrt 2
  have hk : k ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let a : Fin 2 → (Fin 4 → ℝ) := ![k • x, k • y]
  have hcol (j : Fin 2) : (fun i => realColumns z i j) = a j := by
    fin_cases j <;> rfl
  ext j l
  change (fun i => realColumns z i j) ⬝ᵥ (fun i => realColumns z i l) = _
  rw [hcol j, hcol l]
  fin_cases j <;> fin_cases l <;>
    norm_num [a, Matrix.one_apply, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hxx, hyy, hxy, hzero, ← pow_two, hk] <;> nlinarith only [hk]

private def complexify {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofRealHom

private theorem complexify_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    complexify (A * B) = complexify A * complexify B :=
  Matrix.map_mul (f := Complex.ofRealHom)

private theorem complexify_add {m n : Type*} (A B : Matrix m n ℝ) :
    complexify (A + B) = complexify A + complexify B :=
  Matrix.map_add _ (map_add Complex.ofRealHom) A B

private theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℝ) = 0 :=
  Matrix.map_zero _ (map_zero Complex.ofRealHom)

private theorem complexify_one {n : Type*} [DecidableEq n] :
    complexify (1 : Matrix n n ℝ) = 1 :=
  Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)

private theorem complexify_transpose {m n : Type*} (A : Matrix m n ℝ) :
    complexify Aᵀ = (complexify A)ᴴ := by
  ext i j
  simp [complexify, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Complex.star_def]

/-- A complex matrix annihilates the real frame exactly when it annihilates
the two conjugate vectors. -/
private theorem annihilate_realColumns_iff {m : Type*}
    (T : Matrix m (Fin 4) ℂ) (z : Fin 4 → ℂ) :
    T * complexify (realColumns z) = 0 ↔ T *ᵥ z = 0 ∧ T *ᵥ star z = 0 := by
  let A := complexify (realColumns z)
  let k : ℂ := (Real.sqrt 2 : ℝ)
  have hk : k ≠ 0 := by
    have hk' : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    change (↑(Real.sqrt 2) : ℂ) ≠ 0
    exact_mod_cast hk'.ne'
  have h_re : (2 : ℂ) • A.col 0 = k • (z + star z) := by
    funext i
    apply Complex.ext <;>
      simp [A, k, complexify, realColumns, Matrix.col, Complex.star_def, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im, Pi.smul_apply, smul_eq_mul] <;> ring
  have h_im : (2 : ℂ) • A.col 1 = (-k * Complex.I) • (z - star z) := by
    funext i
    apply Complex.ext <;>
      simp [A, k, complexify, realColumns, Matrix.col, Complex.star_def,
        Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Pi.smul_apply, smul_eq_mul] <;> ring
  have h_pos : k • z = A.col 0 + Complex.I • A.col 1 := by
    funext i
    apply Complex.ext <;>
      simp [A, k, complexify, realColumns, Matrix.col, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Pi.smul_apply, smul_eq_mul] <;> ring
  have h_neg : k • star z = A.col 0 - Complex.I • A.col 1 := by
    funext i
    apply Complex.ext <;>
      simp [A, k, complexify, realColumns, Matrix.col, Complex.star_def,
        Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Pi.smul_apply, smul_eq_mul] <;> ring
  change T * A = 0 ↔ _
  constructor
  · intro hT
    have hcol (j : Fin 2) : T *ᵥ A.col j = 0 := by
      rw [← Matrix.col_mul_eq_mulVec_col, hT] <;> rfl
    constructor
    · have h := congrArg (fun v => T *ᵥ v) h_pos
      rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h
      have hz : k • (T *ᵥ z) = 0 := by simpa only [hcol, smul_zero, add_zero] using h
      exact (smul_eq_zero.mp hz).resolve_left hk
    · have h := congrArg (fun v => T *ᵥ v) h_neg
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul] at h
      have hz : k • (T *ᵥ star z) = 0 := by simpa only [hcol, smul_zero, sub_zero] using h
      exact (smul_eq_zero.mp hz).resolve_left hk
  · rintro ⟨hz, hcz⟩
    have hzero (j : Fin 2) : T *ᵥ A.col j = 0 := by
      have h (v : Fin 4 → ℂ) (hv : (2 : ℂ) • A.col j = v)
          (hzv : T *ᵥ v = 0) : T *ᵥ A.col j = 0 := by
        have he := congrArg (fun w => T *ᵥ w) hv
        rw [Matrix.mulVec_smul, hzv] at he
        exact (smul_eq_zero.mp he).resolve_left (by norm_num)
      fin_cases j
      · exact h _ h_re (by rw [Matrix.mulVec_smul, Matrix.mulVec_add, hz, hcz]; simp)
      · exact h _ h_im (by rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hz, hcz]; simp)
    ext i j
    change (T *ᵥ A.col j) i = 0
    rw [hzero]
    rfl

private theorem real_orthogonal_complement
    (A : Matrix (Fin 4) (Fin 2) ℝ) (hA : Aᵀ * A = 1) :
    ∃ F : Matrix (Fin 4) (Fin 2) ℝ, Fᵀ * F = 1 ∧
      Fᵀ * A = 0 ∧ A * Aᵀ + F * Fᵀ = 1 := by
  obtain ⟨R, hR, hR0, hR1⟩ := complete_real_pair A hA
  let tail : Fin 2 → Fin 4 := ![2, 3]
  let F := R.submatrix id tail
  refine ⟨F, ?_, ?_, ?_⟩
  · ext j k
    change (fun i => R i (tail j)) ⬝ᵥ (fun i => R i (tail k)) = _
    rw [real_gram_entry R hR, Matrix.one_apply]
    fin_cases j <;> fin_cases k <;> norm_num [tail, Matrix.one_apply]
  · ext j k
    change (fun i => R i (tail j)) ⬝ᵥ (fun i => A i k) = 0
    have hcol0 : (fun i => A i 0) = fun i => R i 0 := funext fun i => (hR0 i).symm
    have hcol1 : (fun i => A i 1) = fun i => R i 1 := funext fun i => (hR1 i).symm
    fin_cases k
    · change (fun i => R i (tail j)) ⬝ᵥ (fun i => A i 0) = 0
      rw [hcol0, real_gram_entry R hR]
      fin_cases j <;> norm_num [tail]
    · change (fun i => R i (tail j)) ⬝ᵥ (fun i => A i 1) = 0
      rw [hcol1, real_gram_entry R hR]
      fin_cases j <;> norm_num [tail]
  · ext i j
    have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
    have hij := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hRR
    change (∑ k : Fin 4, R i k * R j k) = _ at hij
    change (∑ k : Fin 2, A i k * A j k) +
      (∑ k : Fin 2, R i (tail k) * R j (tail k)) = _
    have ht0 : tail 0 = 2 := rfl
    have ht1 : tail 1 = 3 := rfl
    simpa only [Fin.sum_univ_two, Fin.sum_univ_four, hR0, hR1, ht0, ht1, add_assoc] using hij

-- The real-vector quadratic form argument also appears in
-- QuantumChannels.IptPptSquaredEquivalence.real_part_psd.
private theorem re_part_posSemidef {n : Type*} [Fintype n]
    (T : Matrix n n ℂ) (hT : T.PosSemidef) : (T.map Complex.re).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have he := congrArg Complex.re (congrFun (congrFun hT.isHermitian.eq i) j)
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def] using he
  · intro x
    calc
      star x ⬝ᵥ ((T.map Complex.re) *ᵥ x) =
          (star (fun i => (x i : ℂ)) ⬝ᵥ (T *ᵥ (fun i => (x i : ℂ)))).re := by
        simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Complex.star_def,
          Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      _ ≥ 0 := hT.re_dotProduct_nonneg (fun i => (x i : ℂ))

private theorem re_sandwich {m n : Type*} [Fintype n]
    (F : Matrix m n ℝ) (T : Matrix n n ℂ) :
    ((complexify F) * T * (complexify F)ᴴ).map Complex.re =
      F * T.map Complex.re * Fᵀ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Matrix.map_apply, complexify, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.ofReal_re, Complex.ofReal_im]

/-- Compress to the real two-plane complementary to an orthonormal conjugate
pair. Factor the real part there, then lift the two real columns as one vector. -/
theorem pure_replacement_for_conjugate_pair
    (z : Fin 4 → ℂ) (hunit : star z ⬝ᵥ z = 1)
    (horth : star (star z) ⬝ᵥ z = 0)
    (ρ : Matrix (Fin 4) (Fin 4) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hz : ρ *ᵥ z = 0) (hcz : ρ *ᵥ star z = 0) :
    ∃ w : Fin 4 → ℂ, star z ⬝ᵥ w = 0 ∧ star (star z) ⬝ᵥ w = 0 ∧
      (∀ i, Complex.normSq (w i) = (ρ i i).re) ∧ (star w ⬝ᵥ w) = 1 := by
  let A := realColumns z
  obtain ⟨F, hF, hFA, hres⟩ := real_orthogonal_complement A (realColumns_gram z hunit horth)
  let X := complexify A
  let Y := complexify F
  have hunitY : Yᴴ * Y = 1 := by
    simpa only [Y, complexify_mul, complexify_transpose, complexify_one] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => complexify M) hF
  have horthYX : Yᴴ * X = 0 := by
    simpa only [X, Y, complexify_mul, complexify_transpose, complexify_zero] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => complexify M) hFA
  have hresC : X * Xᴴ + Y * Yᴴ = 1 := by
    simpa only [X, Y, complexify_add, complexify_mul, complexify_transpose, complexify_one] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => complexify M) hres
  have hρX : ρ * X = 0 := (annihilate_realColumns_iff ρ z).2 ⟨hz, hcz⟩
  have hXρ : Xᴴ * ρ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hρ.isHermitian.eq, Matrix.conjTranspose_zero] using
      congrArg (fun M : Matrix (Fin 4) (Fin 2) ℂ => Mᴴ) hρX
  let P := Y * Yᴴ
  have hρP : ρ * P = ρ := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => ρ * M) hresC
    simpa [P, mul_add, ← Matrix.mul_assoc ρ X Xᴴ, hρX] using h
  have hPρ : P * ρ = ρ := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M * ρ) hresC
    simpa [P, add_mul, Matrix.mul_assoc X Xᴴ ρ, hXρ] using h
  let T := Yᴴ * ρ * Y
  have hT : T.PosSemidef := hρ.conjTranspose_mul_mul_same Y
  have hYT : Y * T * Yᴴ = ρ := by
    calc
      Y * T * Yᴴ = (P * ρ) * P := by simp only [P, T, Matrix.mul_assoc]
      _ = ρ := by rw [hPρ, hρP]
  have htT : T.trace = 1 := by
    calc
      T.trace = (Y * T * Yᴴ).trace := by
        rw [Matrix.trace_mul_comm (Y * T) Yᴴ, ← Matrix.mul_assoc, hunitY, Matrix.one_mul]
      _ = 1 := by rw [hYT, htr]
  let S := T.map Complex.re
  have hS : S.PosSemidef := re_part_posSemidef T hT
  have htS : S.trace = 1 := by
    simpa only [S, Matrix.trace, Matrix.diag_apply, Matrix.map_apply,
      Complex.re_sum, Complex.one_re] using congrArg Complex.re htT
  let C := CFC.sqrt S
  have hC : C.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hCC : C * Cᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hC.eq]
    exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  let D := F * C
  have hD : D * Dᵀ = ρ.map Complex.re := by
    calc
      D * Dᵀ = F * S * Fᵀ := by
        change (F * C) * (F * C)ᵀ = _
        rw [Matrix.transpose_mul, ← Matrix.mul_assoc (F * C) Cᵀ Fᵀ,
          Matrix.mul_assoc F C Cᵀ, hCC]
      _ = _ := by
        rw [← re_sandwich F T]
        exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.map Complex.re) hYT
  let ξ : Fin 2 → ℂ := fun j => ⟨C j 0, C j 1⟩
  let w := Y *ᵥ ξ
  have hwRe (i : Fin 4) : (w i).re = D i 0 := by
    simp [w, Y, complexify, ξ, D, Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.map_apply,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hwIm (i : Fin 4) : (w i).im = D i 1 := by
    simp [w, Y, complexify, ξ, D, Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.map_apply,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have hdiag (i : Fin 4) : Complex.normSq (w i) = (ρ i i).re := by
    have hi := congrFun (congrFun hD i) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Fin.sum_univ_two, Complex.normSq_apply, hwRe, hwIm] using hi
  have hξ : star ξ ⬝ᵥ ξ = 1 := by
    have hc : (C * Cᵀ).trace = S.trace := congrArg Matrix.trace hCC
    rw [htS] at hc
    have hc' : ∑ i : Fin 2, Complex.normSq (ξ i) = 1 := by
      simpa [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Complex.normSq_apply, Fin.sum_univ_two, ξ] using hc
    calc
      star ξ ⬝ᵥ ξ = ((∑ i, Complex.normSq (ξ i) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        change (∑ i, star (ξ i) * ξ i) = _
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.star_def, mul_comm, Complex.mul_conj]
      _ = 1 := by rw [hc', Complex.ofReal_one]
  have hwunit : star w ⬝ᵥ w = 1 := by
    change star (Y *ᵥ ξ) ⬝ᵥ (Y *ᵥ ξ) = 1
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hunitY, Matrix.one_mulVec, hξ]
  have ⟨hYz, hYcz⟩ := (annihilate_realColumns_iff Yᴴ z).1 horthYX
  have hpair (v : Fin 4 → ℂ) (hv : Yᴴ *ᵥ v = 0) : star v ⬝ᵥ w = 0 := by
    have hstar : star v ᵥ* Y = 0 := by
      simpa only [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_zero] using
        congrArg (fun u : Fin 2 → ℂ => star u) hv
    rw [show w = Y *ᵥ ξ from rfl, Matrix.dotProduct_mulVec, hstar, zero_dotProduct]
  exact ⟨w, hpair z hYz, hpair (star z) hYcz, hdiag, hwunit⟩

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityRealCompression
