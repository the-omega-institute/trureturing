/- GID: D5/S3/Quantum/Matrix/CubicTraceBregman
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CubicTraceBregman
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Noncommuting PSD cubic trace coercivity and two-level component stability. -/

module

public import D5.S3.Quantum.Matrix.HsfCubicRadial
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Mul

/-! Cubic trace geometry retains coercivity at singular PSD reference matrices. -/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Matrix.CubicTraceBregman

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem remainder_identity (A T : Matrix n n ℂ) :
    (A ^ 3).trace.re - 3 * (T ^ 2 * A).trace.re + 2 * (T ^ 3).trace.re =
      3 * (T * (A - T) ^ 2).trace.re + ((A - T) ^ 3).trace.re := by
  have h := HsfCubicRadial.trace_cubic T (A - T) 1
  have he : T + (A - T) = A := by abel
  simp only [one_smul, he, one_pow, mul_one] at h
  have ht : (T ^ 2 * A).trace.re =
      (T ^ 3).trace.re + (T * T * (A - T)).trace.re := by
    simp [pow_succ, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  rw [ht]
  simp only [pow_two, ← Matrix.mul_assoc]
  linarith

/-- Cubic trace Bregman coercivity for arbitrary finite complex PSD endpoints. -/
theorem cubic_trace_bregman_ge_weighted_square_add_abs_cube
    (A T : Matrix n n ℂ) (hA : A.PosSemidef) (hT : T.PosSemidef) :
    let H := A - T
    let hH : H.IsHermitian := hA.isHermitian.sub hT.isHermitian
    (T * H ^ 2).trace.re + (∑ i, |hH.eigenvalues i| ^ 3) ≤
      (A ^ 3).trace.re - 3 * (T ^ 2 * A).trace.re + 2 * (T ^ 3).trace.re := by
  let H := A - T
  let hH : H.IsHermitian := hA.isHermitian.sub hT.isHermitian
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star hH.eigenvectorUnitary)
  have eh : e H = diagonal (fun i => (hH.eigenvalues i : ℂ)) :=
    hH.conjStarAlgAut_star_eigenvectorUnitary
  have tr (M : Matrix n n ℂ) : (e M).trace = M.trace := by
    change (Unitary.conjStarAlgAut ℂ _ (star hH.eigenvectorUnitary) M).trace = _
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.trace_mul_cycle,
      ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have ht (i : n) : 0 ≤ (e T i i).re := by
    have hp := hT.conjTranspose_mul_mul_same (hH.eigenvectorUnitary : Matrix n n ℂ)
    simpa only [e, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      (Complex.nonneg_iff.mp (hp.diag_nonneg (i := i))).1
  have ha (i : n) : 0 ≤ (e T i i).re + hH.eigenvalues i := by
    have hp := hA.conjTranspose_mul_mul_same (hH.eigenvectorUnitary : Matrix n n ℂ)
    have hi := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := i))).1
    have he : e A = e T + diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
      rw [← eh, ← map_add]
      congr 1
      dsimp [H]
      abel
    have hi' : 0 ≤ (e A i i).re := by
      simpa only [e, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using hi
    simpa [he] using hi'
  have hw : (T * H ^ 2).trace.re =
      ∑ i, (e T i i).re * hH.eigenvalues i ^ 2 := by
    rw [← tr (T * H ^ 2), map_mul, map_pow, eh]
    simp [Matrix.trace, Matrix.diagonal_pow, Matrix.mul_diagonal,
      ← Complex.ofReal_pow, Complex.mul_re]
  have hc : (H ^ 3).trace.re = ∑ i, hH.eigenvalues i ^ 3 := by
    rw [← tr (H ^ 3), map_pow, eh]
    simp [Matrix.diagonal_pow, Matrix.trace_diagonal, ← Complex.ofReal_pow]
  have hs : (∑ i, |hH.eigenvalues i| ^ 3) ≤
      2 * (T * H ^ 2).trace.re + (H ^ 3).trace.re := by
    rw [hw, hc, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rcases le_total 0 (hH.eigenvalues i) with hi | hi
    · rw [abs_of_nonneg hi]
      nlinarith [mul_nonneg (ht i) (sq_nonneg (hH.eigenvalues i))]
    · rw [abs_of_nonpos hi]
      nlinarith [mul_nonneg (ha i) (sq_nonneg (hH.eigenvalues i))]
  dsimp only
  rw [remainder_identity]
  change (T * H ^ 2).trace.re + _ ≤ 3 * (T * H ^ 2).trace.re + (H ^ 3).trace.re
  linarith

private theorem diagonal_abs_cube_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (j : n) :
    |(H j j).re| ^ 3 ≤ ∑ i, |hH.eigenvalues i| ^ 3 := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let p : n → ℝ := fun i => ‖U j i‖ ^ 2
  have hp (i : n) : 0 ≤ p i := sq_nonneg _
  have hsum : ∑ i, p i = 1 := by
    have h := hH.eigenvectorBasis.sum_sq_norm_inner_right (EuclideanSpace.single j (1 : ℂ))
    simpa [p, U, EuclideanSpace.inner_single_right, PiLp.norm_single] using h
  have hj : (H j j).re = ∑ i, p i * hH.eigenvalues i := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ((U j i * (hH.eigenvalues i : ℂ)) * star (U j i)).re = _
    rw [mul_right_comm, RCLike.star_def, Complex.mul_conj]
    simp [p, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, Complex.mul_re]
  have htri : |(H j j).re| ≤ ∑ i, p i * |hH.eigenvalues i| := by
    rw [hj]
    calc
      _ ≤ ∑ i, |p i * hH.eigenvalues i| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp [abs_mul, abs_of_nonneg (hp _)]
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (3 : ℕ)) := convexOn_pow 3
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := p)
    (fun i _ => hp i) hsum (fun i _ => abs_nonneg (hH.eigenvalues i))
  simp only [smul_eq_mul] at hjensen
  calc
    |(H j j).re| ^ 3 ≤ (∑ i, p i * |hH.eigenvalues i|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) htri 3
    _ ≤ ∑ i, p i * |hH.eigenvalues i| ^ 3 := hjensen
    _ ≤ ∑ i, |hH.eigenvalues i| ^ 3 := by
      apply Finset.sum_le_sum
      intro i _
      have hpi : p i ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun k _ => hp k) (Finset.mem_univ i)
      exact mul_le_of_le_one_left (by positivity) hpi

/-- Two spectral levels: stable quadratic components and the distinguished cubic component. -/
theorem two_level_cubic_bregman_controls_components
    (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (E : Matrix Unit n ℂ) (D : Matrix n n ℂ) :
    let T : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
      Matrix.fromBlocks ((a : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0
        ((b : ℂ) • (1 : Matrix n n ℂ))
    let X : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
      Matrix.fromBlocks (((a + q : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) E Eᴴ
        (((b : ℂ) • (1 : Matrix n n ℂ)) + D)
    let W : ℝ := a * q ^ 2 + b * (Dᴴ * D).trace.re +
      (a + b) * (E * Eᴴ).trace.re
    X.PosSemidef →
      max (W + |q| ^ 3) (2 * W) ≤
        (X ^ 3).trace.re - 3 * (T ^ 2 * X).trace.re + 2 * (T ^ 3).trace.re := by
  intro T X W hX
  have hT : T.PosSemidef := by
    have he : T = diagonal (Sum.elim (fun _ : Unit => (a : ℂ)) (fun _ : n => (b : ℂ))) := by
      ext i j
      cases i <;> cases j <;> simp [T, Matrix.one_apply, Matrix.diagonal]
    rw [he, Matrix.posSemidef_diagonal_iff]
    intro i
    cases i <;> simp [Complex.nonneg_iff, ha, hb]
  have hD : D.IsHermitian := by
    have h := hX.isHermitian.submatrix Sum.inr
    have hbI : ((b : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
      simpa using (Matrix.isHermitian_one (n := n) (α := ℂ)).smul
        (show IsSelfAdjoint (b : ℂ) by simp [isSelfAdjoint_iff])
    have h' : (((b : ℂ) • (1 : Matrix n n ℂ)) + D).IsHermitian := h
    simpa using h'.sub hbI
  let H := X - T
  have hH : H.IsHermitian := hX.isHermitian.sub hT.isHermitian
  have he : H = fromBlocks ((q : ℂ) • (1 : Matrix Unit Unit ℂ)) E Eᴴ D := by
    ext i j
    cases i <;> cases j <;> simp [H, X, T, add_smul, sub_eq_add_neg] <;> ring
  have hw : (T * H ^ 2).trace.re = W := by
    rw [he, pow_two]
    simp only [T, Matrix.fromBlocks_multiply, Matrix.zero_mul,
      zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.add_apply, Matrix.smul_apply,
      Complex.mul_re]
    dsimp only [W]
    rw [hD.eq]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Fintype.sum_unique]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have het := congrArg Complex.re (Matrix.trace_mul_comm Eᴴ E)
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Fintype.sum_unique] at het
    rw [het]
    ring
  have hq : (H (Sum.inl ()) (Sum.inl ())).re = q := by simp [he]
  have hentry := diagonal_abs_cube_le H hH (Sum.inl ())
  rw [hq] at hentry
  have hcore := cubic_trace_bregman_ge_weighted_square_add_abs_cube X T hX hT
  change (T * H ^ 2).trace.re + (∑ i, |hH.eigenvalues i| ^ 3) ≤ _ at hcore
  rw [hw] at hcore
  apply max_le
  · linarith
  · have hp := HsfCubicRadial.trace_weight_square_nonneg X H hX hH
    have heq : (X * H ^ 2).trace.re = (T * H ^ 2).trace.re + (H ^ 3).trace.re := by
      have hx : X = T + H := by dsimp [H]; abel
      conv_lhs => rw [hx]
      simp [Matrix.add_mul, Matrix.trace_add, pow_succ']
    rw [heq, hw] at hp
    rw [remainder_identity]
    change 2 * W ≤ 3 * (T * H ^ 2).trace.re + (H ^ 3).trace.re
    rw [hw]
    linarith

#print axioms cubic_trace_bregman_ge_weighted_square_add_abs_cube
#print axioms two_level_cubic_bregman_controls_components

end D5.S3.Quantum.Matrix.CubicTraceBregman
