/- GID: D5/S3/QuadraticForms/SymplecticScalarShear
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SymplecticScalarShear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: prerequisite
   digest: Every finite real J0-symplectic block matrix has a bounded scalar shear and exact symmetric factorization. -/

import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms

open Matrix

variable {n : ℕ}

def J0 (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

def lowerShear (K : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 1 0 K 1

def upperShear (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 1 H 0 1

noncomputable def dilation (E : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks E 0 0 E.transpose⁻¹

def J0Inv (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

lemma J0_mul_J0Inv : J0 n * J0Inv n = 1 := by
  simp [J0, J0Inv, Matrix.fromBlocks_multiply]

lemma block_symplectic_identities
    {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : P * J0 n * P.transpose = J0 n) :
    let a := P.toBlocks₁₁
    let b := P.toBlocks₁₂
    let c := P.toBlocks₂₁
    let d := P.toBlocks₂₂
    a * b.transpose = b * a.transpose ∧
      a * d.transpose - b * c.transpose = 1 ∧
      c * d.transpose = d * c.transpose := by
  have hJ : J0 n = -Matrix.J (Fin n) ℝ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [J0, Matrix.J]
  have hmem : P ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    SymplecticGroup.mem_iff.mpr (by
      simpa only [hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] using hP)
  have hblocks := SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks P.toBlocks₁₁.transpose P.toBlocks₂₁.transpose
        P.toBlocks₁₂.transpose P.toBlocks₂₂.transpose ∈
          Matrix.symplecticGroup (Fin n) ℝ from by
      rw [← Matrix.fromBlocks_transpose, Matrix.fromBlocks_toBlocks]
      exact SymplecticGroup.transpose_mem hmem)
  exact ⟨hblocks.1, hblocks.2.2, hblocks.2.1⟩

private lemma gram_pos {a b c d : Matrix (Fin n) (Fin n) ℝ}
    (had : a * d.transpose - b * c.transpose = 1) :
    (a * a.transpose + b * b.transpose).PosDef := by
  let A : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.of fun i j => Sum.elim (a i) (b i) j
  let B : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => Sum.elim (fun k => d.transpose k j) (fun k => -c.transpose k j) i
  have hAB : A * B = 1 := by
    ext i j
    simpa [A, B, Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg,
      Finset.sum_add_distrib, ← Finset.sum_neg_distrib] using congrFun (congrFun had i) j
  have hAinj : Function.Injective (fun v => Matrix.vecMul v A) := by
    intro x y hxy
    have hxy' := congrArg (fun z => Matrix.vecMul z B) hxy
    simpa only [Matrix.vecMul_vecMul, hAB, Matrix.vecMul_one] using hxy'
  have hgram : A * A.conjTranspose = a * a.transpose + b * b.transpose := by
    ext i j
    simp [A, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply]
  rw [← hgram]
  exact Matrix.PosDef.mul_conjTranspose_self A hAinj

private lemma complex_gram {a b : Matrix (Fin n) (Fin n) ℝ}
    (hab : a * b.transpose = b * a.transpose) :
    let M : Matrix (Fin n) (Fin n) ℂ := a.map Complex.ofRealHom + Complex.I • b.map Complex.ofRealHom
    M * M.conjTranspose = (a * a.transpose + b * b.transpose).map Complex.ofReal := by
  let A := a.map Complex.ofRealHom
  let B := b.map Complex.ofRealHom
  have hA : A.conjTranspose = A.transpose := by ext i j; simp [A]
  have hB : B.conjTranspose = B.transpose := by ext i j; simp [B]
  have hAB : A * B.transpose = B * A.transpose := by
    calc
      A * B.transpose = (a * b.transpose).map Complex.ofReal := by
        ext i j
        simp [A, B, Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_mul]
      _ = (b * a.transpose).map Complex.ofReal := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.map Complex.ofRealHom) hab
      _ = B * A.transpose := by
        ext i j
        simp [A, B, Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_mul]
  change (A + Complex.I • B) * (A + Complex.I • B).conjTranspose = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA, hB]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Complex.star_def, Complex.conj_I, neg_smul, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_neg,
    one_smul, mul_one, Matrix.add_mul, hAB]
  have hAA : A * A.transpose = (a * a.transpose).map Complex.ofReal := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_mul]
  have hBB : B * B.transpose = (b * b.transpose).map Complex.ofReal := by
    ext i j
    simp [B, Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_mul]
  rw [hAA, hBB]
  ext i j
  simp [Matrix.add_apply, Complex.ofReal_add]
  ring_nf
  rw [show (Complex.I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring
private lemma eval_det_complex {a b : Matrix (Fin n) (Fin n) ℝ} (z : ℂ) :
    let q : Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
      (Polynomial.X : Polynomial ℝ) • b.map Polynomial.C + a.map Polynomial.C
    Polynomial.eval₂ Complex.ofRealHom z q.det =
      Matrix.det (z • b.map Complex.ofReal + a.map Complex.ofReal) := by
  dsimp
  simp only [Matrix.det_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd, Polynomial.eval₂_smul, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Units.smul_def, smul_eq_mul, map_mul, map_add]
  classical
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsg | hsg
  · rw [hsg]
    simp only [Units.smul_def, Units.val_one, one_smul]
    rw [Polynomial.eval₂_finsetProd]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    ring
  · rw [hsg]
    simp [Units.smul_def, smul_eq_mul]
    rw [Polynomial.eval₂_finsetProd]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    ring
private lemma complex_det_ne_zero {a b c d : Matrix (Fin n) (Fin n) ℝ}
    (hab : a * b.transpose = b * a.transpose)
    (had : a * d.transpose - b * c.transpose = 1) :
    (a.map Complex.ofReal + Complex.I • b.map Complex.ofReal).det ≠ 0 := by
  let S : Matrix (Fin n) (Fin n) ℝ := a * a.transpose + b * b.transpose
  let M : Matrix (Fin n) (Fin n) ℂ := a.map Complex.ofReal + Complex.I • b.map Complex.ofReal
  have hSpos : S.PosDef := by
    dsimp [S]
    exact gram_pos had
  have hSunit : IsUnit S := hSpos.isUnit
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hdetC : IsUnit (S.map Complex.ofReal).det := by
    have hmapdet := RingHom.map_det Complex.ofRealHom S
    have hmapdet' : Complex.ofRealHom S.det = (S.map Complex.ofReal).det := by
      simpa [Complex.ofRealHom] using hmapdet
    rw [← hmapdet']
    exact RingHom.isUnit_map Complex.ofRealHom hdet
  have hSmap : IsUnit (S.map Complex.ofReal) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdetC
  have hgram : M * M.conjTranspose = S.map Complex.ofReal := by
    dsimp [M, S]
    simpa [Complex.ofRealHom, add_comm] using complex_gram hab
  have hMunit : IsUnit M := by
    apply isUnit_of_mul_isUnit_left
    rw [hgram]
    exact hSmap
  exact (Matrix.isUnit_iff_isUnit_det M).mp hMunit |>.ne_zero
private lemma exists_scalar_det_ne_zero {a b c d : Matrix (Fin n) (Fin n) ℝ}
    (hab : a * b.transpose = b * a.transpose)
    (had : a * d.transpose - b * c.transpose = 1) :
    ∃ t : ℕ, t ≤ n ∧ (a + (t : ℝ) • b).det ≠ 0 := by
  let q : Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
    (Polynomial.X : Polynomial ℝ) • b.map Polynomial.C + a.map Polynomial.C
  let p : Polynomial ℝ := q.det
  have hp0 : p ≠ 0 := by
    intro hp
    have hzero : Polynomial.eval₂ Complex.ofRealHom Complex.I p = 0 := by
      rw [hp]
      simp
    have heval : Polynomial.eval₂ Complex.ofRealHom Complex.I p =
        (Complex.I • b.map Complex.ofReal + a.map Complex.ofReal).det := by
      dsimp [p, q]
      exact eval_det_complex Complex.I
    rw [heval] at hzero
    exact (by
      have hne := complex_det_ne_zero hab had
      exact hne (by simpa [add_comm] using hzero))
  have h_exists : ∃ k ∈ Finset.range (n + 1), p.eval (k : ℝ) ≠ 0 := by
    by_contra h
    have hsubset : (Finset.image (fun k : ℕ => (k : ℝ)) (Finset.range (n + 1))).val ⊆ p.roots := by
      intro x hx
      have hx' : x ∈ Finset.image (fun k : ℕ => (k : ℝ)) (Finset.range (n + 1)) := by
        exact hx
      rcases Finset.mem_image.mp hx' with ⟨k, hk, rfl⟩
      apply (Polynomial.mem_roots hp0).mpr
      by_contra hkzero
      exact h ⟨k, hk, hkzero⟩
    have hcard := Polynomial.card_le_degree_of_subset_roots hsubset
    have hdeg : p.natDegree ≤ n := by
      dsimp [p, q]
      simpa using (Polynomial.natDegree_det_X_add_C_le b a)
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at hcard
    omega
  obtain ⟨t, ht, hteval⟩ := h_exists
  have htlt : t < n + 1 := Finset.mem_range.mp ht
  refine ⟨t, by omega, ?_⟩
  have hEval2 : Polynomial.eval₂ Complex.ofRealHom (t : ℂ) p ≠ 0 := by
    change Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom (t : ℝ)) p ≠ 0
    rw [Polynomial.eval₂_at_apply]
    intro hz
    apply hteval
    exact Complex.ofReal_injective hz
  have hdetC :
      (Complex.ofRealHom (a + (t : ℝ) • b).det) =
        ((t : ℂ) • b.map Complex.ofReal + a.map Complex.ofReal).det := by
    have hmapdet := RingHom.map_det Complex.ofRealHom (a + (t : ℝ) • b)
    rw [hmapdet]
    congr 1
    ext i j
    simp [Complex.ofRealHom, Matrix.map_apply, add_comm]
  have hdetC' : Complex.ofRealHom (a + (t : ℝ) • b).det ≠ 0 := by
    rw [hdetC]
    rw [← eval_det_complex (a := a) (b := b) (z := (t : ℂ))]
    exact hEval2
  intro hreal
  apply hdetC'
  simp [hreal]
private lemma transpose_symplectic
    {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : P * J0 n * P.transpose = J0 n) :
    P.transpose * J0 n * P = J0 n := by
  have hJ : J0 n = -Matrix.J (Fin n) ℝ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [J0, Matrix.J]
  have hmem : P ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    SymplecticGroup.mem_iff.mpr (by
      simpa only [hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] using hP)
  rw [hJ, Matrix.mul_neg, Matrix.neg_mul]
  exact congrArg Neg.neg (SymplecticGroup.mem_iff'.mp hmem)

private lemma transpose_block_symplectic
    {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : P.transpose * J0 n * P = J0 n) :
    let a := P.toBlocks₁₁
    let b := P.toBlocks₁₂
    let c := P.toBlocks₂₁
    let d := P.toBlocks₂₂
    a.transpose * c = c.transpose * a ∧
      a.transpose * d - c.transpose * b = 1 ∧
      b.transpose * d = d.transpose * b := by
  have hJ : J0 n = -Matrix.J (Fin n) ℝ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [J0, Matrix.J]
  have hmem : P ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    SymplecticGroup.mem_iff'.mpr (by
      simpa only [hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] using hP)
  have hblocks := SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ ∈
        Matrix.symplecticGroup (Fin n) ℝ from by
      rw [Matrix.fromBlocks_toBlocks]
      exact hmem)
  exact ⟨hblocks.1, hblocks.2.2, hblocks.2.1⟩

private lemma transformed_identities
    {a b c d : Matrix (Fin n) (Fin n) ℝ} (t : ℕ)
    (hab : a * b.transpose = b * a.transpose)
    (hac : a.transpose * c = c.transpose * a)
    (had : a.transpose * d - c.transpose * b = 1)
    (hbd : b.transpose * d = d.transpose * b) :
    let E := a + (t : ℝ) • b
    let C := c + (t : ℝ) • d
    E * b.transpose = b * E.transpose ∧
      E.transpose * C = C.transpose * E ∧
      E.transpose * d - C.transpose * b = 1 := by
  dsimp
  have hadT : d.transpose * a - b.transpose * c = 1 := by
    simpa [Matrix.transpose_sub, Matrix.transpose_one] using congrArg Matrix.transpose had
  have hcross : a.transpose * d + b.transpose * c = c.transpose * b + d.transpose * a := by
    ext i j
    have h1 := congrFun (congrFun had i) j
    have h2 := congrFun (congrFun hadT i) j
    simp [Matrix.sub_apply, Matrix.add_apply] at h1 h2 ⊢
    linear_combination h1 - h2
  constructor
  · simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, hab, add_assoc, add_comm, add_left_comm]
  constructor
  · change (a.transpose + (t : ℝ) • b.transpose) * (c + (t : ℝ) • d) =
      (c.transpose + (t : ℝ) • d.transpose) * (a + (t : ℝ) • b)
    calc
      (a.transpose + (t : ℝ) • b.transpose) * (c + (t : ℝ) • d) =
          (t : ℝ) • (a.transpose * d + b.transpose * c) +
            (t : ℝ) • (t : ℝ) • (b.transpose * d) + a.transpose * c := by
        simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          smul_add, smul_smul, add_assoc, add_comm, add_left_comm]
      _ = (t : ℝ) • (c.transpose * b + d.transpose * a) +
            (t : ℝ) • (t : ℝ) • (d.transpose * b) + c.transpose * a := by
        rw [hcross, hbd, hac]
      _ = (c.transpose + (t : ℝ) • d.transpose) * (a + (t : ℝ) • b) := by
        simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          smul_add, smul_smul, add_assoc, add_comm, add_left_comm]
  · simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, had, hbd, add_assoc, add_comm, add_left_comm]

private lemma inverse_symmetries
    {E b C d : Matrix (Fin n) (Fin n) ℝ}
    (hdetE : IsUnit E.det)
    (hEb : E * b.transpose = b * E.transpose)
    (hEC : E.transpose * C = C.transpose * E)
    (hEd : E.transpose * d - C.transpose * b = 1) :
    let H := E⁻¹ * b
    let R := C * E⁻¹
    H.transpose = H ∧ R.transpose = R ∧ d = R * b + E.transpose⁻¹ := by
  dsimp
  have hdetEt : IsUnit E.transpose.det := Matrix.isUnit_det_transpose E hdetE
  have hH : (E⁻¹ * b).transpose = E⁻¹ * b := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc
      b.transpose * E.transpose⁻¹ = 1 * (b.transpose * E.transpose⁻¹) := by rw [Matrix.one_mul]
      _ = (E⁻¹ * E) * (b.transpose * E.transpose⁻¹) := by rw [Matrix.nonsing_inv_mul E hdetE]
      _ = E⁻¹ * (E * b.transpose * E.transpose⁻¹) := by simp only [Matrix.mul_assoc]
      _ = E⁻¹ * (b * E.transpose * E.transpose⁻¹) := by rw [hEb]
      _ = E⁻¹ * b := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv E.transpose hdetEt, Matrix.mul_one]
  have hR' : E.transpose⁻¹ * C.transpose = C * E⁻¹ := by
    calc
      E.transpose⁻¹ * C.transpose = E.transpose⁻¹ * C.transpose * (E * E⁻¹) := by
        rw [Matrix.mul_nonsing_inv E hdetE, Matrix.mul_one]
      _ = E.transpose⁻¹ * (C.transpose * E) * E⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E.transpose⁻¹ * (E.transpose * C) * E⁻¹ := by rw [hEC]
      _ = C * E⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul E.transpose hdetEt, Matrix.one_mul]
  have hR : (C * E⁻¹).transpose = C * E⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    exact hR'
  have hEd' : E.transpose * d = C.transpose * b + 1 := by
    ext i j
    have h := congrFun (congrFun hEd i) j
    simp [Matrix.sub_apply, Matrix.add_apply] at h ⊢
    linear_combination h
  have hd : d = C * E⁻¹ * b + E.transpose⁻¹ := by
    calc
      d = 1 * d := by rw [Matrix.one_mul]
      _ = (E.transpose⁻¹ * E.transpose) * d := by rw [Matrix.nonsing_inv_mul E.transpose hdetEt]
      _ = E.transpose⁻¹ * (E.transpose * d) := by simp only [Matrix.mul_assoc]
      _ = E.transpose⁻¹ * (C.transpose * b + 1) := by rw [hEd']
      _ = E.transpose⁻¹ * C.transpose * b + E.transpose⁻¹ := by
        rw [Matrix.mul_add, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = C * E⁻¹ * b + E.transpose⁻¹ := by rw [hR']
  exact ⟨hH, hR, hd⟩

private lemma block_factor
    {E b C d H R : Matrix (Fin n) (Fin n) ℝ}
    (hdetE : IsUnit E.det)
    (hH : H = E⁻¹ * b)
    (hR : R = C * E⁻¹)
    (hd : d = R * b + E.transpose⁻¹) :
    Matrix.fromBlocks E b C d =
      lowerShear R * dilation E * upperShear H := by
  have hEH : E * H = b := by
    rw [hH, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv E hdetE, Matrix.one_mul]
  have hRE : R * E = C := by
    rw [hR, Matrix.mul_assoc, Matrix.nonsing_inv_mul E hdetE, Matrix.mul_one]
  have hRt : R * E * H + E.transpose⁻¹ = d := by
    rw [Matrix.mul_assoc, hEH, hd]
  have hRt' : C * H + E.transpose⁻¹ = d := by
    calc
      C * H + E.transpose⁻¹ = R * E * H + E.transpose⁻¹ := by rw [hRE]
      _ = d := hRt
  simp [lowerShear, dilation, upperShear, Matrix.fromBlocks_multiply,
    hEH, hRE, hRt']

private lemma j0_lower_conjugate {H : Matrix (Fin n) (Fin n) ℝ} :
    J0 n * lowerShear (-H) * J0Inv n = upperShear H := by
  have hcomm : J0 n * lowerShear (-H) = upperShear H * J0 n := by
    simp [J0, lowerShear, upperShear, Matrix.fromBlocks_multiply]
  calc
    J0 n * lowerShear (-H) * J0Inv n =
        (upperShear H * J0 n) * J0Inv n := by rw [hcomm]
    _ = upperShear H := by
      rw [Matrix.mul_assoc, J0_mul_J0Inv, Matrix.mul_one]

private lemma lower_cancel (t : ℕ) :
    lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) *
      lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  simp [lowerShear, Matrix.fromBlocks_multiply, Matrix.mul_apply, smul_smul]
 theorem exists_scalar_shear_factorization
    {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hP : P * J0 n * P.transpose = J0 n) :
    let a := P.toBlocks₁₁
    let b := P.toBlocks₁₂
    let c := P.toBlocks₂₁
    let d := P.toBlocks₂₂
    ∃ t : ℕ, t ≤ n ∧
      ∃ E H R : Matrix (Fin n) (Fin n) ℝ,
        E = a + (t : ℝ) • b ∧
        IsUnit E.det ∧
        H = E⁻¹ * b ∧
        R = (c + (t : ℝ) • d) * E⁻¹ ∧
        H.transpose = H ∧ R.transpose = R ∧
        P = lowerShear R * dilation E * J0 n * lowerShear (-H) * J0Inv n *
          lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  dsimp
  let a := P.toBlocks₁₁
  let b := P.toBlocks₁₂
  let c := P.toBlocks₂₁
  let d := P.toBlocks₂₂
  have hids := block_symplectic_identities hP
  have hab := hids.1
  have had := hids.2.1
  have hcd := hids.2.2
  have hPt := transpose_symplectic hP
  have htids := transpose_block_symplectic hPt
  obtain ⟨t, ht, hdet⟩ := exists_scalar_det_ne_zero hab had
  let E : Matrix (Fin n) (Fin n) ℝ := a + (t : ℝ) • b
  let C : Matrix (Fin n) (Fin n) ℝ := c + (t : ℝ) • d
  let H : Matrix (Fin n) (Fin n) ℝ := E⁻¹ * b
  let R : Matrix (Fin n) (Fin n) ℝ := C * E⁻¹
  have hdetE : IsUnit E.det := isUnit_iff_ne_zero.mpr (by simpa [E] using hdet)
  have htrans := transformed_identities (a := a) (b := b) (c := c) (d := d) t
      hab htids.1 htids.2.1 htids.2.2
  have htrans' : E * b.transpose = b * E.transpose ∧
      E.transpose * C = C.transpose * E ∧
      E.transpose * d - C.transpose * b = 1 := by
    simpa [E, C] using htrans
  have hinv := inverse_symmetries (E := E) (b := b) (C := C) (d := d)
      hdetE htrans'.1 htrans'.2.1 htrans'.2.2
  have hinv' : H.transpose = H ∧ R.transpose = R ∧
      d = R * b + E.transpose⁻¹ := by
    simpa [H, R] using hinv
  have hPblocks : P = Matrix.fromBlocks a b c d := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hPnt : P * lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      lowerShear R * dilation E * upperShear H := by
    calc
      P * lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
          Matrix.fromBlocks a b c d * lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by rw [hPblocks]
      _ = Matrix.fromBlocks E b C d := by
        simp [lowerShear, Matrix.fromBlocks_multiply, E, C,
          Matrix.mul_smul, Matrix.smul_mul, smul_smul, add_comm]
      _ = lowerShear R * dilation E * upperShear H := block_factor hdetE rfl rfl hinv'.2.2
  have hcancel := lower_cancel (n := n) t
  have hJ := j0_lower_conjugate (n := n) (H := H)
  refine ⟨t, ht, E, H, R, ?_, hdetE, ?_, ?_, hinv'.1, hinv'.2.1, ?_⟩
  · simp [E, a, b]
  · simp [H, b]
  · simp [R, C, c, d]
  have hrewrite :
      lowerShear R * dilation E * upperShear H *
          lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
        lowerShear R * dilation E * (J0 n * lowerShear (-H) * J0Inv n) *
          lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [← hJ]
  calc
    P = P * 1 := by rw [Matrix.mul_one]
    _ = P * (lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) *
        lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by rw [hcancel]
    _ = (P * lowerShear ((t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) *
        lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by simp only [Matrix.mul_assoc]
    _ = (lowerShear R * dilation E * upperShear H) *
        lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by rw [hPnt]
    _ = lowerShear R * dilation E * J0 n * lowerShear (-H) * J0Inv n *
        lowerShear (-(t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
      rw [hrewrite]
      simp only [Matrix.mul_assoc]
end D5.S3.QuadraticForms
