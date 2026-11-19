import D5.S3.Quantum.Measurement.AuricRankOneFourScratch
import D5.S3.Quantum.Measurement.AuricRootTrace
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # The rank-three and rank-two competitor in five-level AURIC -/

noncomputable section

namespace D5.S3.Quantum.Measurement.AuricRankThreeTwo

open Matrix Set RHLinalg
open scoped ComplexOrder MatrixOrder BigOperators InnerProductSpace
open AuricBranchDual (rootTrace flaggedChoiScore two_flag_cp_branch_score_le)
open AuricRankOneFour (mixedTest mixedTest_psd mixed_flag_gram flagTest weights)
open AuricFiveLevelTilt
open FiniteDimensional

set_option maxHeartbeats 800000

private theorem rootTrace_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (A V : Matrix n n ℂ) (hA : A.PosSemidef) (hV : Vᴴ * V = 1) :
    rootTrace (Vᴴ * A * V) = rootTrace A := by
  have hu : V ∈ Matrix.unitaryGroup n ℂ := Matrix.mem_unitaryGroup_iff'.2 hV
  unfold rootTrace
  rw [show Vᴴ = star V from rfl, AuricRootTrace.sqrt_star_conjugate A V hA.nonneg hu,
    Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff.mp hu, Matrix.one_mul]

/-- Diagonal pinching for a trace root, proved by taking the norm of each
column of the positive square root. -/
theorem rootTrace_le_sum_sqrt_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    rootTrace A ≤ ∑ i, Real.sqrt (A i i).re := by
  let B := CFC.sqrt A
  have hB : B.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hGram : Bᴴ * B = A := by rw [hB.1.eq]; exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hdiag (i : n) : (A i i).re = ∑ j, ‖B j i‖ ^ 2 := by
    rw [← hGram, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow]
    rfl
  unfold rootTrace
  change (∑ i, B i i).re ≤ _
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    (B i i).re ≤ ‖B i i‖ := Complex.re_le_norm _
    _ ≤ Real.sqrt (A i i).re := by
      rw [hdiag]
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖B j i‖) (Finset.mem_univ i))

private theorem gram_entry {m n : Type*} [Fintype m]
    (A : Matrix m n ℂ) (i j : n) :
    (Aᴴ * A) i j = ∑ k, star (A k i) * A k j := by
  simp [Matrix.mul_apply, conjTranspose_apply]

private theorem basisMatrix_isometry {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (of fun i j => b j i : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      (of fun i j => b j i : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  rw [gram_entry, Matrix.one_apply, ← orthonormal_iff_ite.mp b.orthonormal i j,
    EuclideanSpace.inner_eq_star_dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem exists_basis_first {n : ℕ}
    (x : EuclideanSpace ℂ (Fin (n + 1))) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℂ (EuclideanSpace ℂ (Fin (n + 1))), b 0 = x := by
  let v : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)) := fun _ => x
  have hv : Orthonormal ℂ (({0} : Set (Fin (n + 1))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, v, Set.domRestrict, inner_self_eq_norm_sq_to_K, hx]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (by simp)⟩

/-- A unitary change of coordinates aligns the first column with the
spectator row. The zero row permits any first unit vector. -/
theorem exists_spectator_adapted {m : Type*} (k : m) {n : ℕ}
    (A : Matrix m (Fin (n + 1)) ℂ) :
    ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ),
      Vᴴ * V = 1 ∧ 0 ≤ a ∧ (A * V) k 0 = (a : ℂ) ∧
        ∀ j : Fin n, (A * V) k j.succ = 0 := by
  let y : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (fun j => star (A k j))
  by_cases hy : y = 0
  · have hrow (j : Fin (n + 1)) : A k j = 0 := by
      have h := congrArg (fun z : EuclideanSpace ℂ (Fin (n + 1)) => z j) hy
      simpa [y] using h
    exact ⟨1, 0, by simp, le_rfl, by simp [hrow], by simp [hrow]⟩
  · let x : EuclideanSpace ℂ (Fin (n + 1)) := (↑‖y‖⁻¹ : ℂ) • y
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hx : ‖x‖ = 1 := by
      simp [x, norm_smul, inv_mul_cancel₀ hy0.ne']
    obtain ⟨b, hb⟩ := exists_basis_first x hx
    let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := of fun i j => b j i
    have hyb : y = (↑‖y‖ : ℂ) • b 0 := by
      rw [hb]
      change y = (↑‖y‖ : ℂ) • ((↑‖y‖⁻¹ : ℂ) • y)
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hy0.ne', Complex.ofReal_one, one_smul]
    have hentry (j : Fin (n + 1)) : (A * V) k j = ⟪y, b j⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [Matrix.mul_apply, V, y, dotProduct, mul_comm]
    refine ⟨V, ‖y‖, basisMatrix_isometry b, hy0.le, ?_, ?_⟩
    · rw [hentry]
      conv_lhs => rw [hyb]
      rw [inner_smul_left, orthonormal_iff_ite.mp b.orthonormal]
      simp
    · intro j
      rw [hentry, hyb, inner_smul_left, orthonormal_iff_ite.mp b.orthonormal]
      simp [Ne.symm (Fin.succ_ne_zero j)]

private def pMass (x : Fin 5 → ℂ) : ℝ := Complex.normSq (x 0) + Complex.normSq (x 1)
private def qMass (x : Fin 5 → ℂ) : ℝ := Complex.normSq (x 2) + Complex.normSq (x 3)
private def overlap (x y : Fin 5 → ℂ) : ℂ := ∑ i, star (x i) * y i
private def colVec {n : Type*} (A : Matrix (Fin 5) n ℂ) (j : n) : Fin 5 → ℂ :=
  fun i => A i j

private theorem overlap_self (x : Fin 5 → ℂ) :
    (overlap x x).re = pMass x + qMass x + Complex.normSq (x 4) := by
  simp only [overlap, Fin.sum_univ_five, RCLike.star_def, Complex.conj_mul',
    Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    pMass, qMass]
  ring

private theorem overlap_gram {m n : Type*} (A : Matrix (Fin 5) m ℂ)
    (B : Matrix (Fin 5) n ℂ) (i : m) (j : n) :
    overlap (colVec A i) (colVec B j) = (Aᴴ * B) i j := by
  simp [overlap, colVec, mul_apply, conjTranspose_apply]

private theorem unit_col_mass {n : Type*} [DecidableEq n] (A : Matrix (Fin 5) n ℂ)
    (hA : Aᴴ * A = 1) (i : n) :
    pMass (colVec A i) + qMass (colVec A i) + Complex.normSq (A 4 i) = 1 := by
  change pMass (colVec A i) + qMass (colVec A i) + Complex.normSq (colVec A i 4) = 1
  rw [← overlap_self, overlap_gram, hA, one_apply_eq, Complex.one_re]

private theorem diag_mixed {n : Type*} (A : Matrix (Fin 5) n ℂ) (j : n) (r t : ℝ) :
    ((Aᴴ * mixedTest r t * A) j j).re =
      t * pMass (colVec A j) + (1 - t) * qMass (colVec A j) +
        r ^ 2 * Complex.normSq (A 4 j) := by
  unfold mixedTest
  rw [Matrix.mul_assoc, Matrix.mul_apply, Complex.re_sum]
  have h (i : Fin 5) :
      ((Aᴴ) j i * (diagonal (fun k => (weights r t k : ℂ)) * A) i j).re =
        weights r t i * Complex.normSq (A i j) := by
    rw [Matrix.diagonal_mul, conjTranspose_apply, ← mul_left_comm, RCLike.star_def,
      Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simp_rw [h]
  rw [Fin.sum_univ_five]
  change t * _ + t * _ + (1 - t) * _ + (1 - t) * _ + r ^ 2 * _ = _
  unfold pMass qMass colVec
  ring

private theorem twoCoordinate_lagrange (a b c d : ℂ) :
    Complex.normSq (star a * c + star b * d) + Complex.normSq (a * d - b * c) =
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) := by
  simp only [RCLike.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- On the hyperplane perpendicular to a background unit vector, any unit
vector whose preferred-sector component is parallel to that of the
distinguished vector has preferred-sector weight at most the complementary
weight of the distinguished vector. This gives the smaller Rayleigh bound
needed on a two-dimensional rest space, including both sector endpoints. -/
theorem preferred_weight_le_of_det_zero (v x : Fin 5 → ℂ)
    (hv : pMass v + qMass v = 1) (hx : pMass x + qMass x = 1)
    (horth : overlap v x = 0) (hx4 : x 4 = 0)
    (hdet : v 0 * x 1 - v 1 * x 0 = 0) :
    pMass x ≤ 1 - pMass v := by
  have hP := twoCoordinate_lagrange (v 0) (v 1) (x 0) (x 1)
  have hQ := twoCoordinate_lagrange (v 2) (v 3) (x 2) (x 3)
  rw [hdet, Complex.normSq_zero, add_zero] at hP
  have hsum : star (v 0) * x 0 + star (v 1) * x 1 =
      -(star (v 2) * x 2 + star (v 3) * x 3) := by
    simp only [overlap, Fin.sum_univ_five, hx4, mul_zero, add_zero] at horth
    linear_combination horth
  rw [hsum, Complex.normSq_neg] at hP
  change _ = pMass v * pMass x at hP
  change _ = qMass v * qMass x at hQ
  nlinarith only [hP, hQ, Complex.normSq_nonneg (v 2 * x 3 - v 3 * x 2), hv, hx,
    show qMass v * qMass x = (1 - pMass v) * (1 - pMass x) by
      rw [show qMass v = 1 - pMass v by linarith only [hv],
          show qMass x = 1 - pMass x by linarith only [hx]]]

private theorem unitary_right {n : Type*} [Fintype n] [DecidableEq n]
    {V : Matrix n n ℂ} (hV : Vᴴ * V = 1) : V * Vᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr hV)

private theorem rotated_isometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n ℂ} {V : Matrix n n ℂ} (hA : Aᴴ * A = 1) (hV : Vᴴ * V = 1) :
    (A * V)ᴴ * (A * V) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hV]

private theorem rotated_proj {m n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {V : Matrix n n ℂ} (hV : Vᴴ * V = 1) :
    (A * V) * (A * V)ᴴ = A * Aᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc A, ← Matrix.mul_assoc V, unitary_right hV, Matrix.one_mul]

private theorem rootTrace_rotated {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin 5) n ℂ) {V : Matrix n n ℂ} (hV : Vᴴ * V = 1)
    {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rootTrace ((A * V)ᴴ * mixedTest r t * (A * V)) =
      rootTrace (Aᴴ * mixedTest r t * A) := by
  have he : (A * V)ᴴ * mixedTest r t * (A * V) = Vᴴ * (Aᴴ * mixedTest r t * A) * V := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  exact rootTrace_unitary (Aᴴ * mixedTest r t * A) V ((mixedTest_psd ht).conjTranspose_mul_mul_same A) hV

private theorem frame_cross {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] (e : m ⊕ n ≃ k)
    (U : Matrix k m ℂ) (W : Matrix k n ℂ) (h : U * Uᴴ + W * Wᴴ = 1) :
    Uᴴ * W = 0 := by
  let M := fromCols U W
  have hM : M * Mᴴ = 1 := by
    rw [show M = fromCols U W from rfl, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromRows, h]
  have hM' : Mᴴ * M = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e.symm).1 hM
  have hh : fromBlocks (Uᴴ * U) (Uᴴ * W) (Wᴴ * U) (Wᴴ * W) = 1 := by
    simpa only [M, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols] using hM'
  ext i j
  simpa only [fromBlocks_apply₁₂, Matrix.one_apply, reduceCtorEq, ite_false, Matrix.zero_apply]
    using congrFun (congrFun hh (Sum.inl i)) (Sum.inr j)

private theorem row_mass {m n : Type*} [Fintype m] [Fintype n]
    (U : Matrix (Fin 5) m ℂ) (W : Matrix (Fin 5) n ℂ)
    (h : U * Uᴴ + W * Wᴴ = 1) (i : Fin 5) :
    (∑ j, Complex.normSq (U i j)) + (∑ j, Complex.normSq (W i j)) = 1 := by
  have hh := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => (M i i).re) h
  simpa only [Matrix.add_apply, Complex.add_re, Matrix.mul_apply, conjTranspose_apply,
    RCLike.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, one_apply_eq,
    Complex.one_re] using hh

private theorem overlap_sub_left (a b : ℝ) (u w x : Fin 5 → ℂ) :
    overlap (fun i => (a : ℂ) * u i - (b : ℂ) * w i) x =
      (a : ℂ) * overlap u x - (b : ℂ) * overlap w x := by
  simp only [overlap, star_sub, star_mul, RCLike.star_def, Complex.conj_ofReal,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem overlap_sub_right (a b : ℝ) (x u w : Fin 5 → ℂ) :
    overlap x (fun i => (a : ℂ) * u i - (b : ℂ) * w i) =
      (a : ℂ) * overlap x u - (b : ℂ) * overlap x w := by
  simp only [overlap, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- The complementary special vectors share a unit background direction.
Every remaining column is perpendicular to that direction. The construction
applies when either special vector has zero spectator overlap. -/
theorem exists_background_direction
    (U : Matrix (Fin 5) (Fin 3) ℂ) (W : Matrix (Fin 5) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    {a b : ℝ} (ha : U 4 0 = (a : ℂ)) (hb : W 4 0 = (b : ℂ))
    (hu : ∀ j : Fin 2, U 4 j.succ = 0) (hw : ∀ j : Fin 1, W 4 j.succ = 0) :
    ∃ v : Fin 5 → ℂ, a ^ 2 + b ^ 2 = 1 ∧ v 4 = 0 ∧ pMass v + qMass v = 1 ∧
      (∀ i : Fin 5, i ≠ 4 → U i 0 = (b : ℂ) * v i ∧ W i 0 = -(a : ℂ) * v i) ∧
      (∀ j : Fin 2, overlap v (colVec U j.succ) = 0) ∧
      (∀ j : Fin 1, overlap v (colVec W j.succ) = 0) := by
  have hnormSq (x : ℝ) : Complex.normSq (x : ℂ) = x ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simpa [Fin.sum_univ_succ, ha, hb, hu, hw, hnormSq] using row_mass U W hcompl 4
  let u := colVec U 0
  let w := colVec W 0
  let v : Fin 5 → ℂ := fun i => (b : ℂ) * u i - (a : ℂ) * w i
  have hv4 : v 4 = 0 := by simp [v, u, w, colVec, ha, hb, mul_comm]
  have hUW := frame_cross (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5) U W hcompl
  have hWU : Wᴴ * U = 0 := by
    simpa using congrArg Matrix.conjTranspose hUW
  have hcast : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hvunit : pMass v + qMass v = 1 := by
    have h := overlap_self v
    rw [hv4, Complex.normSq_zero, add_zero] at h
    rw [← h]
    have he : overlap v v = 1 := by
      change overlap (fun i => (b : ℂ) * u i - (a : ℂ) * w i)
        (fun i => (b : ℂ) * u i - (a : ℂ) * w i) = 1
      rw [overlap_sub_left, overlap_sub_right, overlap_sub_right]
      simp only [u, w, overlap_gram, hUW, hWU, hU, hW, one_apply_eq, Matrix.zero_apply]
      linear_combination hcast
    rw [he, Complex.one_re]
  refine ⟨v, hab, hv4, hvunit, ?_, ?_, ?_⟩
  · intro i hi
    have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M i 4) hcompl
    have hzero : u i * (a : ℂ) + w i * (b : ℂ) = 0 := by
      simpa [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ,
        Matrix.one_apply, hi, u, w, colVec, ha, hb, hu, hw] using he
    constructor
    · change u i = (b : ℂ) * ((b : ℂ) * u i - (a : ℂ) * w i)
      linear_combination -(u i) * hcast + (a : ℂ) * hzero
    · change w i = -(a : ℂ) * ((b : ℂ) * u i - (a : ℂ) * w i)
      linear_combination -(w i) * hcast + (b : ℂ) * hzero
  · intro j
    change overlap (fun i => (b : ℂ) * u i - (a : ℂ) * w i) _ = 0
    simp [overlap_sub_left, u, w, overlap_gram, hU, hWU, Ne.symm (Fin.succ_ne_zero j)]
  · intro j
    change overlap (fun i => (b : ℂ) * u i - (a : ℂ) * w i) _ = 0
    simp [overlap_sub_left, u, w, overlap_gram, hW, hUW, Ne.symm (Fin.succ_ne_zero j)]

private def tailRotate {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  of (Fin.cases (Fin.cases 1 (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => V i j)))

private theorem tailRotate_isometry {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : Vᴴ * V = 1) : (tailRotate V)ᴴ * tailRotate V = 1 := by
  ext i j
  rw [gram_entry, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [tailRotate]
  · simp [tailRotate, Ne.symm (Fin.succ_ne_zero _)]
  · simp [tailRotate, Fin.succ_ne_zero]
  · simpa [tailRotate, Matrix.one_apply, gram_entry] using congrFun (congrFun hV i) j

private theorem tailRotate_first {m : Type*} {n : ℕ}
    (U : Matrix m (Fin (n + 1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) (i : m) :
    (U * tailRotate V) i 0 = U i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailRotate]

private theorem tailRotate_succ {m : Type*} {n : ℕ}
    (U : Matrix m (Fin (n + 1)) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) (i : m) (j : Fin n) :
    (U * tailRotate V) i j.succ = ∑ k : Fin n, U i k.succ * V k j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailRotate]

/-- Within the two background columns, one can rotate to put a vector with
vanishing preferred-sector determinant in the last column. -/
theorem exists_preferred_tail_rotation (U : Matrix (Fin 5) (Fin 3) ℂ)
    (v : Fin 5 → ℂ) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℂ, Vᴴ * V = 1 ∧
      (∀ i, (U * V) i 0 = U i 0) ∧
      (∀ i, (∀ j : Fin 2, U i j.succ = 0) → ∀ j : Fin 2, (U * V) i j.succ = 0) ∧
      v 0 * (U * V) 1 2 - v 1 * (U * V) 0 2 = 0 := by
  let A : Matrix Unit (Fin 2) ℂ := of fun _ j => v 0 * U 1 j.succ - v 1 * U 0 j.succ
  obtain ⟨V, a, hV, _, _, hv⟩ := exists_spectator_adapted () A
  refine ⟨tailRotate V, tailRotate_isometry hV, tailRotate_first U V, ?_, ?_⟩
  · intro i hi j
    simp [tailRotate_succ, hi]
  · change v 0 * (U * tailRotate V) 1 (Fin.succ (1 : Fin 2)) -
      v 1 * (U * tailRotate V) 0 (Fin.succ (1 : Fin 2)) = 0
    rw [tailRotate_succ, tailRotate_succ]
    simpa [Matrix.mul_apply, A, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      using hv (0 : Fin 1)

private theorem pMass_nonneg (v : Fin 5 → ℂ) : 0 ≤ pMass v :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

private theorem qMass_nonneg (v : Fin 5 → ℂ) : 0 ≤ qMass v :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

private theorem normSq_real_mul (a : ℝ) (z : ℂ) :
    Complex.normSq ((a : ℂ) * z) = a ^ 2 * Complex.normSq z := by
  rw [map_mul]
  simp [Complex.normSq_apply, pow_two]

private def bg (t x : ℝ) := t * x + (1 - t) * (1 - x)

private theorem bg_mem {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    bg t x ∈ Icc (0 : ℝ) 1 := by
  unfold bg
  exact ⟨add_nonneg (mul_nonneg ht.1 hx.1) (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx.2)), by
    linarith [mul_le_mul_of_nonneg_left hx.2 ht.1,
      mul_le_mul_of_nonneg_left (show 1 - x ≤ 1 by linarith [hx.1]) (sub_nonneg.mpr ht.2)]⟩

private theorem rest_diag {n : Type*} [DecidableEq n] (A : Matrix (Fin 5) n ℂ)
    (hA : Aᴴ * A = 1) (j : n) (hj : A 4 j = 0) (r t : ℝ) :
    ((Aᴴ * mixedTest r t * A) j j).re = bg t (pMass (colVec A j)) ∧
      pMass (colVec A j) ∈ Icc (0 : ℝ) 1 := by
  have h := unit_col_mass A hA j
  rw [hj, Complex.normSq_zero, add_zero] at h
  have hq := qMass_nonneg (colVec A j)
  refine ⟨?_, pMass_nonneg _, by linarith⟩
  rw [diag_mixed, hj, Complex.normSq_zero, mul_zero, add_zero, bg,
    show qMass (colVec A j) = 1 - pMass (colVec A j) by linarith]

private theorem special_diag {n : Type*} [OfNat n 0] (A : Matrix (Fin 5) n ℂ)
    (v : Fin 5 → ℂ) (hv : pMass v + qMass v = 1) {a b : ℝ}
    (ha : A 4 0 = (a : ℂ)) (h : ∀ i : Fin 5, i ≠ 4 → A i 0 = (b : ℂ) * v i)
    (r t : ℝ) :
    ((Aᴴ * mixedTest r t * A) 0 0).re = r ^ 2 * a ^ 2 + b ^ 2 * bg t (pMass v) := by
  rw [diag_mixed, ha, show Complex.normSq (a : ℂ) = a ^ 2 by simp [Complex.normSq_apply, pow_two]]
  unfold pMass qMass colVec
  simp only [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), normSq_real_mul]
  unfold pMass qMass at hv
  unfold bg
  linear_combination b ^ 2 * (1 - t) * hv

private theorem rest_sector_trace_le
    (U : Matrix (Fin 5) (Fin 3) ℂ) (W : Matrix (Fin 5) (Fin 2) ℂ)
    (h : U * Uᴴ + W * Wᴴ = 1) :
    pMass (colVec U 1) + pMass (colVec U 2) + pMass (colVec W 1) ≤ 2 := by
  have h₀ := row_mass U W h 0
  have h₁ := row_mass U W h 1
  simp only [Fin.sum_univ_three, Fin.sum_univ_two] at h₀ h₁
  unfold pMass colVec
  linarith only [h₀, h₁, Complex.normSq_nonneg (U 0 0), Complex.normSq_nonneg (U 1 0),
    Complex.normSq_nonneg (W 0 0), Complex.normSq_nonneg (W 1 0)]

private theorem rootTrace_three_diag (U : Matrix (Fin 5) (Fin 3) ℂ)
    {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rootTrace (Uᴴ * mixedTest r t * U) ≤
      Real.sqrt ((Uᴴ * mixedTest r t * U) 1 1).re +
      Real.sqrt ((Uᴴ * mixedTest r t * U) 2 2).re +
      Real.sqrt ((Uᴴ * mixedTest r t * U) 0 0).re := by
  have h := rootTrace_le_sum_sqrt_diagonal _ ((mixedTest_psd (r := r) ht).conjTranspose_mul_mul_same U)
  rw [Fin.sum_univ_three] at h
  linarith only [h]

private theorem rootTrace_two_diag (W : Matrix (Fin 5) (Fin 2) ℂ)
    {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rootTrace (Wᴴ * mixedTest r t * W) ≤
      Real.sqrt ((Wᴴ * mixedTest r t * W) 1 1).re +
      Real.sqrt ((Wᴴ * mixedTest r t * W) 0 0).re := by
  simpa only [Fin.sum_univ_two, add_comm] using
    rootTrace_le_sum_sqrt_diagonal _ ((mixedTest_psd (r := r) ht).conjTranspose_mul_mul_same W)

private theorem rootTrace_nonnegative {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : 0 ≤ rootTrace A :=
  (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1

private theorem bg_le_affine {t x : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) : bg t x ≤ (1 + x) / 2 := by
  unfold bg
  by_cases h : 1 / 2 ≤ x
  · have hh := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ 2 * x - 1 by linarith)
    nlinarith only [hh, hx.2]
  · have hh := mul_nonneg (sub_nonneg.mpr ht.1) (show 0 ≤ 1 - 2 * x by linarith)
    nlinarith only [hh, hx.1]

private theorem euclidean_pair_bound {a b c d A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : a ^ 2 + b ^ 2 ≤ A) (hB : c ^ 2 + d ^ 2 ≤ B) :
    (a + c) ^ 2 + (b + d) ^ 2 ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ a ^ 2 + b ^ 2).trans hA
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ c ^ 2 + d ^ 2).trans hB
  have hprod := mul_le_mul hA hB (by positivity : 0 ≤ c ^ 2 + d ^ 2) hA0
  have hcross : a * c + b * d ≤ Real.sqrt A * Real.sqrt B := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hprod, sq_nonneg (a * d - b * c),
      show (Real.sqrt A * Real.sqrt B) ^ 2 = A * B by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]]
  nlinarith only [hA, hB, hcross, Real.sq_sqrt hA0, Real.sq_sqrt hB0]

private theorem same_preference_diagonal {x y z c d R t s : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hsum : x + y + z ≤ 2) (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c + d ≤ R)
    (ht : t ∈ Icc (1 / 2 : ℝ) 1) (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    (Real.sqrt (bg t x) + Real.sqrt (bg t y) + Real.sqrt c) ^ 2 +
      (Real.sqrt (bg s z) + Real.sqrt d) ^ 2 ≤
      (Real.sqrt (9 / 2) + Real.sqrt R) ^ 2 := by
  have hₓ := Real.sq_sqrt (bg_mem ⟨by linarith [ht.1], ht.2⟩ hx).1
  have hᵧ := Real.sq_sqrt (bg_mem ⟨by linarith [ht.1], ht.2⟩ hy).1
  have h_z := Real.sq_sqrt (bg_mem ⟨by linarith [hs.1], hs.2⟩ hz).1
  apply euclidean_pair_bound (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · nlinarith only [hₓ, hᵧ, h_z, bg_le_affine ht hx, bg_le_affine ht hy,
      bg_le_affine hs hz, hsum, hz.1, sq_nonneg (Real.sqrt (bg t x) - Real.sqrt (bg t y))]
  · simpa only [Real.sq_sqrt hc, Real.sq_sqrt hd] using hcd

private theorem tiltScore_le_max (r : WitnessInterval) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    tiltScore r q ≤ tiltScore r (tiltMass r) := by
  by_cases heq : q = tiltMass r
  · rw [heq]
  · have hr : 1 < (r : ℝ) := by linarith [r.property.1]
    have hm := tiltMass_spec r
    exact (tiltScore_lt_of_ne_maximizer r (tiltMass r) q hr
      ⟨hm.1.1, hm.1.2.trans (by norm_num)⟩ hm.2 hq heq).le

private theorem bg_pref_le {t x y : ℝ} (ht : 1 / 2 ≤ t) (hxy : x ≤ y) :
    bg t x ≤ bg t y := by
  unfold bg
  nlinarith only [mul_nonneg (show 0 ≤ 2 * t - 1 by linarith) (sub_nonneg.mpr hxy)]

private theorem special_pair_bound {r a b t s z : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    (r ^ 2 * a ^ 2 + b ^ 2 * bg t z) + (r ^ 2 * b ^ 2 + a ^ 2 * bg s z) ≤ r ^ 2 + 1 := by
  nlinarith only [mul_le_mul_of_nonneg_left (bg_mem ht hz).2 (sq_nonneg b),
    mul_le_mul_of_nonneg_left (bg_mem hs hz).2 (sq_nonneg a),
    show r ^ 2 * (a ^ 2 + b ^ 2) = r ^ 2 by rw [hab, mul_one], hab]

private theorem paired_square_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : a ^ 2 + b ^ 2 ≤ c ^ 2 + d ^ 2 :=
  add_le_add (pow_le_pow_left₀ ha hac 2) (pow_le_pow_left₀ hb hbd 2)

private theorem opposed_preference_diagonal (r : WitnessInterval)
    {eta z x y w t s : ℝ}
    (heta : eta ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (hyz : y ≤ 1 - z) (ht : t ∈ Icc (1 / 2 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    (Real.sqrt (bg t x) + Real.sqrt (bg t y) +
      Real.sqrt ((r : ℝ) ^ 2 * eta + (1 - eta) * bg t z)) ^ 2 +
    (Real.sqrt (bg s w) + Real.sqrt ((r : ℝ) ^ 2 * (1 - eta) + eta * bg s z)) ^ 2 ≤
      tiltScore r (tiltMass r) := by
  let R : ℝ := r
  have hR : 1 < R := by dsimp [R]; linarith [r.property.1]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith only [hR, sq_nonneg (R - 1)]
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  by_cases hsmall : eta ≤ 1 / 8
  · have hsp3 : R ^ 2 * eta + (1 - eta) * bg t z ≤ 1 + (R ^ 2 - 1) / 8 := by
      nlinarith only [mul_le_mul_of_nonneg_left (bg_mem ht' hz).2 (sub_nonneg.mpr heta.2),
        mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hR2)]
    have hsp2 : R ^ 2 * (1 - eta) + eta * bg s z ≤ R ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left ((bg_mem hs' hz).2.trans hR2) heta.1]
    have tone {a u : ℝ} (h : a ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
        Real.sqrt (bg a u) ≤ 1 := (Real.sqrt_le_sqrt (bg_mem h hu).2).trans_eq Real.sqrt_one
    have h3 := add_le_add (add_le_add (tone ht' hx) (tone ht' hy)) (Real.sqrt_le_sqrt hsp3)
    have h2 := add_le_add (tone hs' hw) (Real.sqrt_le_sqrt hsp2)
    rw [Real.sqrt_sq (by linarith : 0 ≤ R)] at h2
    exact (paired_square_le (by positivity) (by positivity) h3 h2).trans
      ((by simpa only [one_add_one_eq_two] using (other_rank_bounds_lt r).2.2.le :
        (1 + 1 + Real.sqrt (1 + (R ^ 2 - 1) / 8)) ^ 2 + (1 + R) ^ 2 ≤ tiltScore r 0).trans
          (tiltScore_le_max r (by norm_num)))
  · have h₁ : bg t x ≤ t := (bg_pref_le ht.1 hx.2).trans_eq (by simp [bg])
    have h₂ : bg t y ≤ t - (2 * t - 1) * z := (bg_pref_le ht.1 hyz).trans_eq (by unfold bg; ring)
    have h₃ : bg s w ≤ 1 - s := by
      have hcoef : 0 ≤ 1 - 2 * s := by linarith [hs.2]
      unfold bg
      nlinarith only [mul_nonneg hcoef hw.1]
    have h₄ : bg t z = 1 - t + (2 * t - 1) * z := by unfold bg; ring
    have h₅ : bg s z = (1 - s) - (2 * (1 - s) - 1) * z := by unfold bg; ring
    have hthree := add_le_add (add_le_add (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂))
      (le_of_eq (congrArg Real.sqrt (congrArg (fun x => R ^ 2 * eta + (1 - eta) * x) h₄)))
    have htwo := add_le_add (Real.sqrt_le_sqrt h₃)
      (le_of_eq (congrArg Real.sqrt (congrArg (fun x => R ^ 2 * (1 - eta) + eta * x) h₅)))
    have b3 := hthree.trans (opposed_rank_three_bound R eta z t r.property
      ⟨by linarith, heta.2⟩ hz ht)
    have b2 := htwo.trans (opposed_rank_two_bound R eta z (1 - s) heta.1 hz.1
      ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    have hscore := paired_square_le (by positivity) (by positivity) b3 b2
    have hp : 1 - eta ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr heta.2, by linarith [heta.1]⟩
    have he : R ^ 2 * (1 - eta) + eta = 1 + (R ^ 2 - 1) * (1 - eta) := by ring
    rw [he] at hscore
    have htilt := tiltScore_eq_branch_sum R (1 - eta) hR hp
    rw [sub_sub_cancel] at htilt
    exact hscore.trans (htilt.ge.trans (tiltScore_le_max r hp))

/-- The rank-three preferred sector has the larger coefficient. Both
preferences of the rank-two block are allowed, independently. -/
theorem rank_three_two_first_preference_bound
    (U : Matrix (Fin 5) (Fin 3) ℂ) (W : Matrix (Fin 5) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    (r : WitnessInterval) {t s : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rootTrace (Uᴴ * mixedTest r t * U) ^ 2 + rootTrace (Wᴴ * mixedTest r s * W) ^ 2 ≤
      tiltScore r (tiltMass r) := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨V, a, hV, _, ha, hu⟩ := exists_spectator_adapted 4 U
  obtain ⟨X, b, hX, _, hb, hw⟩ := exists_spectator_adapted 4 W
  let A := U * V
  let B := W * X
  change A 4 0 = (a : ℂ) at ha
  change B 4 0 = (b : ℂ) at hb
  have hA : Aᴴ * A = 1 := rotated_isometry hU hV
  have hB : Bᴴ * B = 1 := rotated_isometry hW hX
  have hAB : A * Aᴴ + B * Bᴴ = 1 := by
    simpa only [A, B, rotated_proj U hV, rotated_proj W hX] using hcompl
  obtain ⟨v, hab, hv4, hv, hspec, _, _⟩ := exists_background_direction A B hA hB hAB ha hb hu hw
  obtain ⟨Y, hY, hf, htail, hdet⟩ := exists_preferred_tail_rotation A v
  let C := A * Y
  have hC : Cᴴ * C = 1 := rotated_isometry hA hY
  have hCB : C * Cᴴ + B * Bᴴ = 1 := by simpa only [C, rotated_proj A hY] using hAB
  have hc4 (j : Fin 2) : C 4 j.succ = 0 := htail 4 hu j
  have hcv (i : Fin 5) (hi : i ≠ 4) : C i 0 = (b : ℂ) * v i :=
    (hf i).trans (hspec i hi).1
  have hCv2 : overlap v (colVec C 2) = 0 := by
    let u := colVec C 0
    let w := colVec B 0
    have hvc : v = fun i => (b : ℂ) * u i - (a : ℂ) * w i := by
      funext i
      by_cases hi : i = 4
      · subst i
        rw [hv4]
        change 0 = (b : ℂ) * C 4 0 - (a : ℂ) * B 4 0
        rw [show C 4 0 = A 4 0 from hf 4, ha, hb, mul_comm (b : ℂ), sub_self]
      · have hcast : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
        simp only [u, w, colVec, hcv i hi, (hspec i hi).2]
        linear_combination -(v i) * hcast
    have hx := frame_cross (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5) C B hCB
    have hx' : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose hx
    rw [hvc, overlap_sub_left]
    simp [u, w, overlap_gram, hC, hx']
  let z := pMass v
  have hz : z ∈ Icc (0 : ℝ) 1 := ⟨pMass_nonneg _, by dsimp [z]; linarith [qMass_nonneg v]⟩
  let y := pMass (colVec C 2)
  obtain ⟨hdx, hx⟩ := rest_diag C hC 1 (hc4 0) r t
  obtain ⟨hdy, hy⟩ := rest_diag C hC 2 (hc4 1) r t
  obtain ⟨hdw, hww⟩ := rest_diag B hB 1 (hw 0) r s
  have hyz : y ≤ 1 - z := by
    have hwgt := unit_col_mass C hC 2
    rw [show C 4 2 = 0 from hc4 1, Complex.normSq_zero, add_zero] at hwgt
    exact preferred_weight_le_of_det_zero v (colVec C 2) hv hwgt hCv2 (hc4 1) hdet
  have hca : C 4 0 = (a : ℂ) := (hf 4).trans ha
  have hcb (i : Fin 5) (hi : i ≠ 4) : B i 0 = ((-a : ℝ) : ℂ) * v i := by
    rw [Complex.ofReal_neg]
    exact (hspec i hi).2
  have hds₃ := special_diag C v hv hca hcv r t
  have hds₂ := special_diag B v hv hb hcb r s
  rw [neg_sq] at hds₂
  have h3 := rootTrace_three_diag C (r := (r : ℝ)) ht'
  have h2 := rootTrace_two_diag B (r := (r : ℝ)) hs
  rw [hdx, hdy, hds₃] at h3
  rw [hdw, hds₂] at h2
  have hsum := paired_square_le (rootTrace_nonnegative _) (rootTrace_nonnegative _) h3 h2
  rw [show rootTrace (Cᴴ * mixedTest r t * C) = rootTrace (Aᴴ * mixedTest r t * A) from
      rootTrace_rotated A hY ht',
    show rootTrace (Aᴴ * mixedTest r t * A) = rootTrace (Uᴴ * mixedTest r t * U) from
      rootTrace_rotated U hV ht',
    show rootTrace (Bᴴ * mixedTest r s * B) = rootTrace (Wᴴ * mixedTest r s * W) from
      rootTrace_rotated W hX hs] at hsum
  apply hsum.trans
  by_cases hsame : 1 / 2 ≤ s
  · have h := same_preference_diagonal hx hy hww (rest_sector_trace_le C B hCB)
      (show 0 ≤ (r : ℝ) ^ 2 * a ^ 2 + b ^ 2 * bg t z by
        exact add_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (bg_mem ht' hz).1))
      (show 0 ≤ (r : ℝ) ^ 2 * b ^ 2 + a ^ 2 * bg s z by
        exact add_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (bg_mem hs hz).1))
      (special_pair_bound (r := r) hab ht' hs hz) ht ⟨hsame, hs.2⟩
    exact h.trans ((other_rank_bounds_lt r).2.1.le.trans (tiltScore_le_max r (by norm_num)))
  · have he : b ^ 2 = 1 - a ^ 2 := by linarith only [hab]
    have heta : a ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by linarith only [hab, sq_nonneg b]⟩
    simpa only [← he] using opposed_preference_diagonal r heta hz hx hy hww hyz ht ⟨hs.1, le_of_not_ge hsame⟩

private def swapSectors : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

private theorem mixedTest_swap (r t : ℝ) :
    (mixedTest r (1 - t)).submatrix swapSectors swapSectors = mixedTest r t := by
  rw [mixedTest, Matrix.submatrix_diagonal_equiv, mixedTest, Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i <;> simp [swapSectors, Equiv.swap_apply_def, weights, sub_sub_cancel]

private theorem swap_compression {n : Type*} [Fintype n] (A : Matrix (Fin 5) n ℂ) (r t : ℝ) :
    (A.submatrix swapSectors id)ᴴ * mixedTest r (1 - t) * A.submatrix swapSectors id =
      Aᴴ * mixedTest r t * A := by
  have h : (mixedTest r t).submatrix swapSectors swapSectors = mixedTest r (1 - t) := by
    simpa only [sub_sub_cancel] using mixedTest_swap r (1 - t)
  rw [← h, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

/-- For every pair of independent two-flag mixtures, the complementary
rank-three and rank-two compression scores are bounded by the tilted
maximum on the witness interval. -/
theorem rank_three_two_trace_root_bound
    (U : Matrix (Fin 5) (Fin 3) ℂ) (W : Matrix (Fin 5) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    (r : WitnessInterval) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rootTrace (Uᴴ * mixedTest r t * U) ^ 2 + rootTrace (Wᴴ * mixedTest r s * W) ^ 2 ≤
      tiltScore r (tiltMass r) := by
  by_cases h : 1 / 2 ≤ t
  · exact rank_three_two_first_preference_bound U W hU hW hcompl r ⟨h, ht.2⟩ hs
  · let A := U.submatrix swapSectors id
    let B := W.submatrix swapSectors id
    have hA : Aᴴ * A = 1 := by
      change (U.submatrix swapSectors id)ᴴ * U.submatrix swapSectors id = 1
      rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, hU]
    have hB : Bᴴ * B = 1 := by
      change (W.submatrix swapSectors id)ᴴ * W.submatrix swapSectors id = 1
      rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, hW]
    have hAB : A * Aᴴ + B * Bᴴ = 1 := by
      change U.submatrix swapSectors id * (U.submatrix swapSectors id)ᴴ +
        W.submatrix swapSectors id * (W.submatrix swapSectors id)ᴴ = 1
      rw [conjTranspose_submatrix, conjTranspose_submatrix,
        show (id : Fin 3 → Fin 3) = (Equiv.refl (Fin 3) : Fin 3 → Fin 3) from rfl,
        show (id : Fin 2 → Fin 2) = (Equiv.refl (Fin 2) : Fin 2 → Fin 2) from rfl,
        submatrix_mul_equiv, submatrix_mul_equiv]
      calc
        _ = (U * Uᴴ + W * Wᴴ).submatrix swapSectors swapSectors := by
          ext i j
          rfl
        _ = 1 := by rw [hcompl, submatrix_one_equiv]
    have ha : 1 - t ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    have hb : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
    simpa only [A, B, swap_compression] using
      rank_three_two_first_preference_bound A B hA hB hAB r ha hb

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

/-- The two independent finite CP branch bounds are consumed by the rank
three plus rank two complementary-frame estimate. -/
theorem rank_three_two_cp_score_le
    (U : Matrix (Fin 5) (Fin 3) ℂ) (W : Matrix (Fin 5) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hcompl : U * Uᴴ + W * Wᴴ = 1)
    (r : WitnessInterval)
    (Φ : Fin 2 → MatrixMap (Fin 3) (Fin 5) ℂ)
    (Ψ : Fin 2 → MatrixMap (Fin 2) (Fin 5) ℂ)
    (hΦ : ∀ j, (Φ j).IsCompletelyPositive) (hΨ : ∀ j, (Ψ j).IsCompletelyPositive)
    (hΦtp : (∑ j, Φ j).IsTracePreserving) (hΨtp : (∑ j, Ψ j).IsTracePreserving) :
    flaggedChoiScore (fun j => flagTest r j * U) Φ +
      flaggedChoiScore (fun j => flagTest r j * W) Ψ ≤ tiltScore r (tiltMass r) := by
  obtain ⟨t, ht, _, h3⟩ := two_flag_cp_branch_score_le (fun j => flagTest r j * U) Φ hΦ hΦtp
  obtain ⟨s, hs, _, h2⟩ := two_flag_cp_branch_score_le (fun j => flagTest r j * W) Ψ hΨ hΨtp
  dsimp only at h3 h2
  rw [mixed_flag_gram] at h3 h2
  exact (add_le_add h3 h2).trans (rank_three_two_trace_root_bound U W hU hW hcompl r ht hs)

#print axioms rootTrace_le_sum_sqrt_diagonal
#print axioms exists_spectator_adapted
#print axioms preferred_weight_le_of_det_zero
#print axioms exists_background_direction
#print axioms exists_preferred_tail_rotation
#print axioms rank_three_two_first_preference_bound
#print axioms rank_three_two_trace_root_bound
#print axioms rank_three_two_cp_score_le

end D5.S3.Quantum.Measurement.AuricRankThreeTwo
