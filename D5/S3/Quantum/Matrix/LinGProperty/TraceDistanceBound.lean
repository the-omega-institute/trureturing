/- GID: D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: A block overlap bounds the squared difference of normalized diagonal blocks. -/

import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.TotalVariation.Bhattacharyya

/-! Complementary diagonal compressions control the spectral difference. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Matrix.LinGProperty

private theorem two_outcome_bound {a b t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t)
    (h : t ≤ Real.sqrt (a*b) + Real.sqrt ((1-a)*(1-b))) :
    (a-b)^2 ≤ 1-t^2 := by
  let p : Bool → ℝ := fun k => if k then a else 1-a
  let q : Bool → ℝ := fun k => if k then b else 1-b
  have hp : (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 := by
    constructor
    · intro k
      cases k <;> simp [p] <;> linarith
    · simp [p, Fintype.sum_bool]
  have hq : (∀ k, 0 ≤ q k) ∧ ∑ k, q k = 1 := by
    constructor
    · intro k
      cases k <;> simp [q] <;> linarith
    · simp [q, Fintype.sum_bool]
  have hf : D5.S3.TotalVariation.Bhattacharyya.bhattacharyya p q =
      Real.sqrt (a*b) + Real.sqrt ((1-a)*(1-b)) := by
    simp [D5.S3.TotalVariation.Bhattacharyya.bhattacharyya, p, q,
      Fintype.sum_bool, add_comm]
  have hv : D5.S3.TotalVariation.Pinsker.totalVariation p q = |a-b| := by
    simp only [D5.S3.TotalVariation.Pinsker.totalVariation, Fintype.sum_bool,
      p, q, Bool.false_eq_true, ↓reduceIte]
    rw [show 1-a-(1-b) = -(a-b) by ring, abs_neg]
    ring
  have hs := D5.S3.TotalVariation.Bhattacharyya.total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  rw [hf, hv, sq_abs] at hs
  have hsq : t^2 ≤ (Real.sqrt (a*b) + Real.sqrt ((1-a)*(1-b)))^2 :=
    (sq_le_sq₀ ht (by positivity)).mpr h
  linarith

private theorem block_trace_cauchy {n : Type*} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ} (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (s : Finset n) :
    ‖∑ i ∈ s, X i i‖ ^ 2 ≤
      (∑ i ∈ s, (A i i).re) * (∑ i ∈ s, (B i i).re) := by
  let e (i : n) : Fin 2 → n ⊕ n := ![Sum.inl i, Sum.inr i]
  let W : Matrix (Fin 2) (Fin 2) ℂ :=
    ∑ i ∈ s, (fromBlocks A X Xᴴ B).submatrix (e i) (e i)
  have hP : W.PosSemidef :=
    Matrix.posSemidef_sum s (fun i _ => hW.submatrix (e i))
  have h := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hP 0 1
  simp only [W, Matrix.sum_apply, Matrix.submatrix_apply,
    Complex.normSq_eq_norm_sq, e, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂, Complex.re_sum] at h
  exact h

private theorem normalized_diagonal_gap {n : Type*} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ} (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1) (i : n) :
    ((A i i).re - (B i i).re)^2 ≤ 1-‖X.trace‖^2 := by
  have ha0 : 0 ≤ (A i i).re :=
    (hW.diag_nonneg (i := Sum.inl i)).1
  have hb0 : 0 ≤ (B i i).re :=
    (hW.diag_nonneg (i := Sum.inr i)).1
  have haSum : ∑ k, (A k k).re = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re hA
  have hbSum : ∑ k, (B k k).re = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re hB
  have haRest : ∑ k ∈ Finset.univ.erase i, (A k k).re = 1-(A i i).re := by
    have := Finset.sum_erase_add (s := Finset.univ) (fun k => (A k k).re)
      (Finset.mem_univ i)
    linarith
  have hbRest : ∑ k ∈ Finset.univ.erase i, (B k k).re = 1-(B i i).re := by
    have := Finset.sum_erase_add (s := Finset.univ) (fun k => (B k k).re)
      (Finset.mem_univ i)
    linarith
  have ha1 : (A i i).re ≤ 1 := by
    have hn : 0 ≤ ∑ k ∈ Finset.univ.erase i, (A k k).re :=
      Finset.sum_nonneg (fun k _ => (hW.diag_nonneg (i := Sum.inl k)).1)
    linarith
  have hb1 : (B i i).re ≤ 1 := by
    have hn : 0 ≤ ∑ k ∈ Finset.univ.erase i, (B k k).re :=
      Finset.sum_nonneg (fun k _ => (hW.diag_nonneg (i := Sum.inr k)).1)
    linarith
  have hsingle : ‖X i i‖ ≤ Real.sqrt ((A i i).re * (B i i).re) := by
    have hc := block_trace_cauchy hW {i}
    simp only [Finset.sum_singleton] at hc
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg ha0 hb0)).mpr hc
  have hrest : ‖∑ k ∈ Finset.univ.erase i, X k k‖ ≤
      Real.sqrt ((1-(A i i).re)*(1-(B i i).re)) := by
    have hc := block_trace_cauchy hW (Finset.univ.erase i)
    rw [haRest,hbRest] at hc
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hc
  apply two_outcome_bound ha0 ha1 hb0 hb1 (norm_nonneg _)
  have hx : X.trace = (∑ k ∈ Finset.univ.erase i, X k k) + X i i := by
    exact (Finset.sum_erase_add Finset.univ (fun k => X k k) (Finset.mem_univ i)).symm
  rw [hx]
  exact (norm_add_le _ _).trans (by linarith)

/-- The overlap trace of two trace-one positive blocks has modulus at most one. -/
theorem normalized_trace_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ} (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1) : ‖X.trace‖ ≤ 1 := by
  have hc := block_trace_cauchy hW Finset.univ
  have ha : ∑ i, (A i i).re = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re hA
  have hb : ∑ i, (B i i).re = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re hB
  rw [ha, hb, one_mul] at hc
  have hsq : ‖X.trace‖ ^ 2 ≤ 1 := by simpa [Matrix.trace] using hc
  nlinarith [norm_nonneg X.trace]

set_option maxHeartbeats 800000 in
/-- A normalized positive block matrix controls the squared diagonal difference. -/
theorem normalized_difference_square_le {n : Type*} [Fintype n] [DecidableEq n]
    {A X B : Matrix n n ℂ} (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1) :
    ((((1-‖X.trace‖^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) -
      (A-B)*(A-B)).PosSemidef := by
  have hAp : A.PosSemidef := by
    have he : (fromBlocks A X Xᴴ B).submatrix Sum.inl Sum.inl = A := by
      ext i j
      rfl
    rw [← he]
    exact hW.submatrix Sum.inl
  have hBp : B.PosSemidef := by
    have he : (fromBlocks A X Xᴴ B).submatrix Sum.inr Sum.inr = B := by
      ext i j
      rfl
    rw [← he]
    exact hW.submatrix Sum.inr
  let hD : (A-B).IsHermitian := hAp.isHermitian.sub hBp.isHermitian
  let U := hD.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U)
  have htrace (M : Matrix n n ℂ) : (C M).trace = M.trace := by
    dsimp [C]
    rw [star_star, Matrix.trace_mul_cycle, ← Unitary.coe_star,
      Unitary.coe_mul_star_self, Matrix.one_mul]
  have hW' : (fromBlocks (C A) (C X) (C X)ᴴ (C B)).PosSemidef := by
    have hc := hW.conjTranspose_mul_mul_same
      (fromBlocks (U : Matrix n n ℂ) 0 0 (U : Matrix n n ℂ))
    simpa [C, Unitary.conjStarAlgAut_star_apply, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.conjTranspose_mul,
      Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using hc
  have hdiag : C (A-B) = diagonal (fun i => (hD.eigenvalues i : ℂ)) := by
    exact hD.conjStarAlgAut_star_eigenvectorUnitary
  have hgap (i : n) : (hD.eigenvalues i)^2 ≤ 1-‖X.trace‖^2 := by
    have hg := normalized_diagonal_gap hW' ((htrace A).trans hA)
      ((htrace B).trans hB) i
    rw [htrace X] at hg
    have he := congrArg (fun M : Matrix n n ℂ => (M i i).re) hdiag
    simp only [map_sub, Matrix.sub_apply, Complex.sub_re,
      Matrix.diagonal_apply_eq, Complex.ofReal_re] at he
    rwa [he] at hg
  have hd : (diagonal (fun i => ((1-‖X.trace‖^2-(hD.eigenvalues i)^2 : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast sub_nonneg.mpr (hgap i)
  have he : C (((((1-‖X.trace‖^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))) -
      (A-B)*(A-B)) = diagonal
        (fun i => ((1-‖X.trace‖^2-(hD.eigenvalues i)^2 : ℝ) : ℂ)) := by
    simp only [map_sub, map_mul, map_smul, map_one, hdiag]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        pow_two, Complex.ofReal_sub]
    · simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [← he] at hd
  simp only [C, Unitary.conjStarAlgAut_star_apply] at hd
  exact (Unitary.isUnit_coe (U := star U)).posSemidef_star_right_conjugate_iff.mp
    (by simpa using hd)

end D5.S3.Quantum.Matrix.LinGProperty
