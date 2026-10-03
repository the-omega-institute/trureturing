/- GID: D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity
   generality: G
   mirror-B: D5/B/S3/Estimation/SplitCovarianceIntersectionEvenConvexity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All positive even derivatives of split CIF log determinant and trace are nonnegative. -/

/-
proof_shape: result: content
escape_witness: the public conclusion itself, via arbitrary-order affine-inverse and log-determinant
  differential constructions together with the compression trace inequality (second form of §3.2).
admission_basis: open-problem-resolution (#11592; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator MatrixOrder
namespace D5.S3.Estimation.SplitCovarianceIntersectionEvenConvexity

/-- The literal split CIF formula, with scalar division encoded by reciprocal scaling. -/
def splitP {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) : (Matrix (Fin n) (Fin n) ℝ) :=
  ((w⁻¹ • A + B)⁻¹ + ((1 - w)⁻¹ • C + D)⁻¹)⁻¹

/-- Both inequalities of Li, equations (7a) and (7b), at every interior weight. -/
def claim : Prop := ∀ (n : ℕ) (A B C D : (Matrix (Fin n) (Fin n) ℝ)),
  A.PosSemidef → B.PosSemidef → C.PosSemidef → D.PosSemidef →
  (A + B).PosDef → (C + D).PosDef → ∀ k : ℕ, 1 ≤ k →
  ∀ w ∈ Set.Ioo (0 : ℝ) 1,
    0 ≤ iteratedDeriv (2 * k) (fun w => Real.log (splitP A B C D w).det) w ∧
    0 ≤ iteratedDeriv (2 * k) (fun w => (splitP A B C D w).trace) w

private abbrev Hidden (n : ℕ) := Fin n ⊕ Fin n

private abbrev Full (n : ℕ) := Fin n ⊕ Hidden n

private def hiddenPencil {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) :
    Matrix (Hidden n) (Hidden n) ℝ :=
  fromBlocks (w • A⁻¹ + B⁻¹) 0 0 ((1 - w) • C⁻¹ + D⁻¹)

private def coupling {n : ℕ} (A C : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) : Matrix (Fin n) (Hidden n) ℝ :=
  fromCols (-(w • A⁻¹)) (-((1 - w) • C⁻¹))

private def pencil {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) : Matrix (Full n) (Full n) ℝ :=
  fromBlocks (w • A⁻¹ + (1 - w) • C⁻¹) (coupling A C w)
    (coupling A C w)ᵀ (hiddenPencil A B C D w)

private def inverseWord {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] : ℕ → R → R → R
  | 0, _, X => X
  | m + 1, N, X => inverseWord m N X * N * X

private def cornerTraceCLM (n : ℕ) : Matrix (Full n) (Full n) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun M => (M.submatrix Sum.inl Sum.inl : (Matrix (Fin n) (Fin n) ℝ)).trace
     map_add' := by intro M N; simp [Matrix.trace, Matrix.submatrix, Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [Matrix.trace, Matrix.submatrix, Finset.mul_sum] } :
      Matrix (Full n) (Full n) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

private def matrixTraceCLM {ι : Type} [Fintype ι] [DecidableEq ι] : Matrix ι ι ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap

private def hiddenInclusion (n : ℕ) : Matrix (Full n) (Hidden n) ℝ := fromRows 0 1

private def regularize {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℝ)) (e : ℝ) : (Matrix (Fin n) (Fin n) ℝ) := A + e • 1

private def jointSplitP {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (p : ℝ × ℝ) : (Matrix (Fin n) (Fin n) ℝ) :=
  splitP (regularize A p.1) (regularize B p.1) (regularize C p.1) (regularize D p.1) p.2

private def matrixEntryCLM {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Matrix ι ι ℝ →L[ℝ] ℝ :=
  ({ toFun := fun M => M i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Matrix ι ι ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- Arbitrary positive even-order convexity for semidefinite split CIF inputs. -/
theorem result : claim := by
  have hasDerivAt_inverseWord {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] {f : ℝ → R} {N : R} {w : ℝ}
      (hf : HasDerivAt f (-(f w * N * f w)) w) (m : ℕ) :
      HasDerivAt (fun x => inverseWord m N (f x))
        (-((m + 1 : ℕ) : ℝ) • inverseWord (m + 1) N (f w)) w := by

    induction m with
    | zero => simpa [inverseWord] using hf
    | succ m ih =>
      have h := (ih.mul_const N).mul hf
      convert h using 1
      · rfl
      · simp only [inverseWord, Nat.cast_add, Nat.cast_one, smul_mul_assoc, mul_smul_comm,
          mul_neg, neg_mul, mul_assoc]
        module

  have iterated_inverse_affine_on {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] (M₀ M₁ : R) (s : Set ℝ) (hs : IsOpen s)
      (hU : ∀ w ∈ s, IsUnit (M₀ + w • M₁)) (m : ℕ) :
      ∀ w ∈ s, iteratedDeriv m (fun x => Ring.inverse (M₀ + x • M₁)) w =
        ((-1 : ℝ) ^ m * (m.factorial : ℝ)) •
          inverseWord m M₁ (Ring.inverse (M₀ + w • M₁)) := by
    have hasDerivAt_inverse {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] {f : ℝ → R} {N : R} {w : ℝ}
        (hf : HasDerivAt f N w) (hu : IsUnit (f w)) :
        HasDerivAt (fun x => Ring.inverse (f x))
          (-(Ring.inverse (f w) * N * Ring.inverse (f w))) w := by
      rcases hu with ⟨u, hu⟩
      have hi : HasFDerivAt Ring.inverse
          (-ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse (f w)) (Ring.inverse (f w))) (f w) := by
        simpa only [← Ring.inverse_unit, hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
      simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply] using! hi.comp_hasDerivAt w hf
    induction m with
    | zero => intro w hw; simp [inverseWord]
    | succ m ih =>
      intro w hw
      have hf : HasDerivAt (fun x : ℝ => M₀ + x • M₁) M₁ w := by
        simpa using ((hasDerivAt_id w).smul_const M₁).const_add M₀
      have hinv := hasDerivAt_inverse hf (hU w hw)
      have hd := (hasDerivAt_inverseWord hinv m).const_smul
        ((-1 : ℝ) ^ m * (m.factorial : ℝ))
      have heq : iteratedDeriv m (fun x => Ring.inverse (M₀ + x • M₁)) =ᶠ[𝓝 w]
          (fun x => ((-1 : ℝ) ^ m * (m.factorial : ℝ)) •
            inverseWord m M₁ (Ring.inverse (M₀ + x • M₁))) := by
        filter_upwards [hs.mem_nhds hw] with x hx using ih x hx
      rw [iteratedDeriv_succ, heq.deriv_eq]
      change deriv (((-1 : ℝ) ^ m * (m.factorial : ℝ)) •
        (fun x => inverseWord m M₁ (Ring.inverse (M₀ + x • M₁)))) w = _
      rw [hd.deriv]
      simp only [smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      congr 1
      ring

  have trace_even_compression {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
      (V : Matrix ι κ ℝ) (hV : Vᵀ * V = 1) (k : ℕ) :
      ((Vᵀ * H * V) ^ (2 * k)).trace ≤ (H ^ (2 * k)).trace := by
    have isometry_row_sum_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (V : Matrix ι κ ℝ) (hV : Vᵀ * V = 1) (i : ι) :
        (∑ j, V i j ^ 2) ≤ 1 := by
      have he : (1 - V * Vᵀ)ᴴ * (1 - V * Vᵀ) = 1 - V * Vᵀ := by
        simp only [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one,
          transpose_mul, transpose_transpose]
        calc
          (1 - V * Vᵀ) * (1 - V * Vᵀ) =
              1 - V * Vᵀ - V * Vᵀ + V * (Vᵀ * V) * Vᵀ := by
            noncomm_ring
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [hV, Matrix.mul_one]; abel
      have hp := posSemidef_conjTranspose_mul_self (1 - V * Vᵀ)
      rw [he] at hp
      have hd := hp.diag_nonneg (i := i)
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, transpose_apply] at hd
      simpa [pow_two] using (sub_nonneg.mp hd)
    have substochastic_even_power {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (lambda : ι → ℝ) (q : ι → κ → ℝ)
        (hq : ∀ i j, 0 ≤ q i j) (hc : ∀ j, ∑ i, q i j = 1)
        (hr : ∀ i, ∑ j, q i j ≤ 1) (k : ℕ) :
        (∑ j, (∑ i, q i j * lambda i) ^ (2 * k)) ≤ ∑ i, lambda i ^ (2 * k) := by
      have hp : Even (2 * k) := even_two_mul k
      calc
        _ ≤ ∑ j, ∑ i, q i j * lambda i ^ (2 * k) := by
          apply Finset.sum_le_sum
          intro j hj
          simpa only [smul_eq_mul] using hp.convexOn_pow.map_sum_le
            (t := Finset.univ) (w := fun i => q i j) (p := lambda)
            (fun i _ => hq i j) (hc j) (fun _ _ => Set.mem_univ _)
        _ = ∑ i, (∑ j, q i j) * lambda i ^ (2 * k) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          simpa using mul_le_mul_of_nonneg_right (hr i) (hp.pow_nonneg (lambda i))
    have trace_power_spectral {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ) (hH : H.IsHermitian) (m : ℕ) :
        (H ^ m).trace = ∑ i, hH.eigenvalues i ^ m := by
      conv_lhs => rw [hH.spectral_theorem, ← map_pow]
      simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
        Matrix.diagonal_pow, Function.comp_def]
    have hT : (Vᵀ * H * V).IsHermitian := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_conjTranspose_mul_mul V hH
    let U : Matrix ι ι ℝ := hH.eigenvectorUnitary
    let Q : Matrix κ κ ℝ := hT.eigenvectorUnitary
    let W := Uᵀ * V * Q
    have hU1 : Uᵀ * U = 1 := by
      simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have hU2 : U * Uᵀ = 1 := by
      simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using Unitary.coe_mul_star_self hH.eigenvectorUnitary
    have hQ1 : Qᵀ * Q = 1 := by
      simpa [Q, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using Unitary.coe_star_mul_self hT.eigenvectorUnitary
    have hW : Wᵀ * W = 1 := by
      dsimp [W]
      simp only [transpose_mul, transpose_transpose]
      calc
        (Qᵀ * (Vᵀ * U)) * (Uᵀ * V * Q) = Qᵀ * (Vᵀ * (U * Uᵀ) * V) * Q := by
          simp only [Matrix.mul_assoc]
        _ = 1 := by simp only [hU2, Matrix.mul_one, Matrix.one_mul, hV, hQ1]
    have hHd : H = U * diagonal hH.eigenvalues * Uᵀ := by
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hH.spectral_theorem
    have hTd : Qᵀ * (Vᵀ * H * V) * Q = diagonal hT.eigenvalues := by
      simpa [Q, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using
          hT.conjStarAlgAut_star_eigenvectorUnitary
    have hdiag : Wᵀ * diagonal hH.eigenvalues * W = diagonal hT.eigenvalues := by
      rw [← hTd]
      conv_rhs => rw [hHd]
      dsimp [W]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have hval (j : κ) : hT.eigenvalues j = ∑ i, W i j ^ 2 * hH.eigenvalues i := by
      have hd := congrArg (fun M : Matrix κ κ ℝ => M j j) hdiag
      simpa [Matrix.mul_apply, Matrix.diagonal_apply, pow_two, mul_comm, mul_left_comm, mul_assoc] using hd.symm
    have hc (j : κ) : ∑ i, W i j ^ 2 = 1 := by
      have hd := congrArg (fun M : Matrix κ κ ℝ => M j j) hW
      simpa [Matrix.mul_apply, pow_two] using hd
    rw [trace_power_spectral _ hT, trace_power_spectral _ hH]
    simp only [hval]
    exact substochastic_even_power hH.eigenvalues (fun i j => W i j ^ 2)
      (fun i j => sq_nonneg _) hc (isometry_row_sum_le W hW) k

  have iterated_logdet_affine_on {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ)
      (s : Set ℝ) (hs : IsOpen s) (hU : ∀ w ∈ s, IsUnit (M₀ + w • M₁)) (m : ℕ) :
      ∀ w ∈ s, iteratedDeriv (m + 1) (fun x => Real.log (M₀ + x • M₁).det) w =
        (-1 : ℝ) ^ m * (m.factorial : ℝ) *
          (inverseWord m M₁ (M₀ + w • M₁)⁻¹ * M₁).trace := by
    have hasDerivAt_inverse {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] {f : ℝ → R} {N : R} {w : ℝ}
        (hf : HasDerivAt f N w) (hu : IsUnit (f w)) :
        HasDerivAt (fun x => Ring.inverse (f x))
          (-(Ring.inverse (f w) * N * Ring.inverse (f w))) w := by
      rcases hu with ⟨u, hu⟩
      have hi : HasFDerivAt Ring.inverse
          (-ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse (f w)) (Ring.inverse (f w))) (f w) := by
        simpa only [← Ring.inverse_unit, hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
      simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply] using! hi.comp_hasDerivAt w hf
    have det_one_add_polynomial_eval {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℝ) (t : ℝ) :
        (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • N.map (Polynomial.C : ℝ →+* Polynomial ℝ))).eval t = (1 + t • N).det := by
      have hm : (1 + (Polynomial.X : Polynomial ℝ) • N.map (Polynomial.C : ℝ →+* Polynomial ℝ)).map (Polynomial.evalRingHom t) =
          1 + t • N := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C]
        by_cases hij : i = j
        · subst j
          simp only [Matrix.one_apply_eq, Polynomial.eval_one]
        · simp only [Matrix.one_apply_ne hij, Polynomial.eval_zero]
      have h := (Polynomial.evalRingHom t).map_det (1 + (Polynomial.X : Polynomial ℝ) • N.map (Polynomial.C : ℝ →+* Polynomial ℝ))
      change Polynomial.eval t _ = ((1 + (Polynomial.X : Polynomial ℝ) •
        N.map (Polynomial.C : ℝ →+* Polynomial ℝ)).map (Polynomial.evalRingHom t)).det at h
      rw [hm] at h
      exact h
    have hasDerivAt_det_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (w : ℝ)
        (hu : IsUnit (M₀ + w • M₁)) :
        HasDerivAt (fun x => (M₀ + x • M₁).det)
          ((M₀ + w • M₁).det * ((M₀ + w • M₁)⁻¹ * M₁).trace) w := by
      let M := M₀ + w • M₁
      let N := M⁻¹ * M₁
      let p : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • N.map (Polynomial.C : ℝ →+* Polynomial ℝ)).det
      have hd : HasDerivAt (fun t => p.eval t) N.trace 0 := by
        simpa only [p, Matrix.derivative_det_one_add_X_smul] using p.hasDerivAt 0
      have ht : HasDerivAt (fun x : ℝ => x - w) 1 w := by simpa using (hasDerivAt_id w).sub_const w
      have hdw := (hd.comp_of_eq w ht (by simp)).const_mul M.det
      have hdet (x : ℝ) : (M₀ + x • M₁).det = M.det * p.eval (x - w) := by
        rw [show p.eval (x - w) = (1 + (x - w) • N).det from det_one_add_polynomial_eval N (x - w),
          ← Matrix.det_mul]
        congr 1
        dsimp [N]
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hu), Matrix.one_mul]
        dsimp [M]
        module
      simpa only [mul_one] using! hdw.congr_of_eventuallyEq (Filter.Eventually.of_forall hdet)
    have hasDerivAt_logdet_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (w : ℝ)
        (hu : IsUnit (M₀ + w • M₁)) :
        HasDerivAt (fun x => Real.log (M₀ + x • M₁).det)
          ((M₀ + w • M₁)⁻¹ * M₁).trace w := by
      have hdet := hasDerivAt_det_affine M₀ M₁ w hu
      have hn : (M₀ + w • M₁).det ≠ 0 :=
        (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu))
      convert hdet.log hn using 1
      field_simp
    induction m with
    | zero =>
      intro w hw
      simpa [inverseWord] using (hasDerivAt_logdet_affine M₀ M₁ w (hU w hw)).deriv
    | succ m ih =>
      intro w hw
      have hf : HasDerivAt (fun x : ℝ => M₀ + x • M₁) M₁ w := by
        simpa using ((hasDerivAt_id w).smul_const M₁).const_add M₀
      have hinv : HasDerivAt (fun x => (M₀ + x • M₁)⁻¹)
          (-((M₀ + w • M₁)⁻¹ * M₁ * (M₀ + w • M₁)⁻¹)) w := by
        simpa only [← Matrix.nonsing_inv_eq_ringInverse] using! hasDerivAt_inverse hf (hU w hw)
      have hword := (hasDerivAt_inverseWord hinv m).mul_const M₁
      have ht : HasDerivAt (fun x => (inverseWord m M₁ (M₀ + x • M₁)⁻¹ * M₁).trace)
          (-((m + 1 : ℕ) : ℝ) * (inverseWord (m + 1) M₁ (M₀ + w • M₁)⁻¹ * M₁).trace) w := by
        simpa [matrixTraceCLM, Matrix.smul_mul, Matrix.trace_smul] using!
          (matrixTraceCLM (ι := ι)).hasFDerivAt.comp_hasDerivAt w hword
      have hd := ht.const_mul ((-1 : ℝ) ^ m * (m.factorial : ℝ))
      have heq : iteratedDeriv (m + 1) (fun x => Real.log (M₀ + x • M₁).det) =ᶠ[𝓝 w]
          (fun x => (-1 : ℝ) ^ m * (m.factorial : ℝ) *
            (inverseWord m M₁ (M₀ + x • M₁)⁻¹ * M₁).trace) := by
        filter_upwards [hs.mem_nhds hw] with x hx using ih x hx
      rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

  have parallel_inverse {ι : Type} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℝ)
      (hU : IsUnit U) (hV : IsUnit V) (hUV : IsUnit (U + V)) :
      U - U * (U + V)⁻¹ * U = (U⁻¹ + V⁻¹)⁻¹ := by
    have hUd := (isUnit_iff_isUnit_det U).mp hU
    have hVd := (isUnit_iff_isUnit_det V).mp hV
    have hUVd := (isUnit_iff_isUnit_det (U + V)).mp hUV
    rw [inv_add_inv ⟨fun _ => hV, fun _ => hU⟩, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      nonsing_inv_nonsing_inv _ hVd, nonsing_inv_nonsing_inv _ hUd]
    calc
      U - U * (U + V)⁻¹ * U =
          (U + V) * (U + V)⁻¹ * U - U * (U + V)⁻¹ * U := by
        rw [mul_nonsing_inv _ hUVd, Matrix.one_mul]
      _ = _ := by noncomm_ring
  have inverse_smul_real {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : IsUnit A)
      (t : ℝ) (ht : t ≠ 0) : (t • A)⁻¹ = t⁻¹ • A⁻¹ := by
    letI : Invertible t := invertibleOfNonzero ht
    simpa using inv_smul A t ((isUnit_iff_isUnit_det A).mp hA)
  have weighted_inverse {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ)
      (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
      t • A⁻¹ - (t • A⁻¹) * (t • A⁻¹ + B⁻¹)⁻¹ * (t • A⁻¹) =
        (t⁻¹ • A + B)⁻¹ := by
    have hU := hA.inv.smul ht
    have hV := hB.inv
    rw [parallel_inverse _ _ hU.isUnit hV.isUnit (hU.add hV).isUnit,
      inverse_smul_real _ hA.inv.isUnit t ht.ne',
      nonsing_inv_nonsing_inv A ((isUnit_iff_isUnit_det A).mp hA.isUnit),
      nonsing_inv_nonsing_inv B ((isUnit_iff_isUnit_det B).mp hB.isUnit)]
  have input_posDef {n : ℕ} (A B : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosSemidef) (_hB : B.PosSemidef) (hAB : (A + B).PosDef)
      {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : (t⁻¹ • A + B).PosDef := by
    have hi : 0 ≤ t⁻¹ - 1 := by
      have : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
      linarith
    have h := hAB.add_posSemidef (hA.smul hi)
    convert h using 1
    module
  have splitP_posDef {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosSemidef) (hB : B.PosSemidef)
      (hC : C.PosSemidef) (hD : D.PosSemidef)
      (hAB : (A + B).PosDef) (hCD : (C + D).PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) : (splitP A B C D w).PosDef := by
    have h1 := input_posDef A B hA hB hAB hw.1 hw.2.le
    have h2 := input_posDef C D hC hD hCD (sub_pos.mpr hw.2) (by linarith [hw.1])
    exact (h1.inv.add h2.inv).inv
  have hiddenPencil_posDef {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) : (hiddenPencil A B C D w).PosDef := by
    have h1 := (hA.inv.smul hw.1).add hB.inv
    have h2 := (hC.inv.smul (sub_pos.mpr hw.2)).add hD.inv
    have hp : (hiddenPencil A B C D w).PosSemidef := by
      letI := h1.isUnit.invertible
      simpa [hiddenPencil] using (Matrix.PosDef.fromBlocks₁₁ (0 : (Matrix (Fin n) (Fin n) ℝ)) _ h1).mpr (by simpa using h2.posSemidef)
    apply hp.posDef_iff_isUnit.mpr
    apply Matrix.isUnit_fromBlocks_zero₂₁.mpr
    exact ⟨h1.isUnit, h2.isUnit⟩
  have hiddenPencil_inverse {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      (hiddenPencil A B C D w)⁻¹ =
        fromBlocks (w • A⁻¹ + B⁻¹)⁻¹ 0 0 ((1 - w) • C⁻¹ + D⁻¹)⁻¹ := by
    have h1 := (hA.inv.smul hw.1).add hB.inv
    have h2 := (hC.inv.smul (sub_pos.mpr hw.2)).add hD.inv
    simpa [hiddenPencil] using Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff
      (w • A⁻¹ + B⁻¹) 0 ((1 - w) • C⁻¹ + D⁻¹) ⟨fun _ => h2.isUnit, fun _ => h1.isUnit⟩
  have pencil_schur {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      w • A⁻¹ + (1 - w) • C⁻¹ -
        coupling A C w * (hiddenPencil A B C D w)⁻¹ * (coupling A C w)ᵀ =
        (w⁻¹ • A + B)⁻¹ + ((1 - w)⁻¹ • C + D)⁻¹ := by
    rw [hiddenPencil_inverse A B C D hA hB hC hD hw]
    simp only [coupling, transpose_fromCols, transpose_neg,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      fromCols_mul_fromRows, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hAt : (w • A⁻¹)ᵀ = w • A⁻¹ := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using (hA.inv.smul hw.1).isHermitian.eq
    have hCt : ((1 - w) • C⁻¹)ᵀ = (1 - w) • C⁻¹ := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        (hC.inv.smul (sub_pos.mpr hw.2)).isHermitian.eq
    rw [hAt, hCt]
    have h1 := weighted_inverse A B hA hB hw.1
    have h2 := weighted_inverse C D hC hD (sub_pos.mpr hw.2)
    rw [← h1, ← h2]
    abel
  have pencil_posDef {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) : (pencil A B C D w).PosDef := by
    have hK := hiddenPencil_posDef A B C D hA hB hC hD hw
    letI := hK.isUnit.invertible
    have hS := (hA.smul (inv_pos.mpr hw.1)).add hB
    have hT := (hC.smul (inv_pos.mpr (sub_pos.mpr hw.2))).add hD
    have hSchur : (w • A⁻¹ + (1 - w) • C⁻¹ -
        coupling A C w * (hiddenPencil A B C D w)⁻¹ * (coupling A C w)ᵀ).PosDef := by
      rw [pencil_schur A B C D hA hB hC hD hw]
      exact hS.inv.add hT.inv
    have hp : (pencil A B C D w).PosSemidef := by
      simpa only [pencil, conjTranspose_eq_transpose_of_trivial] using
        (Matrix.PosDef.fromBlocks₂₂ (w • A⁻¹ + (1 - w) • C⁻¹) (coupling A C w) hK).mpr
          (by simpa only [conjTranspose_eq_transpose_of_trivial] using hSchur.posSemidef)
    apply hp.posDef_iff_isUnit.mpr
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mpr
    simpa only [Matrix.invOf_eq_nonsing_inv] using hSchur.isUnit
  have pencil_inverse_corner {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      (pencil A B C D w)⁻¹.submatrix Sum.inl Sum.inl = splitP A B C D w := by
    have hK := hiddenPencil_posDef A B C D hA hB hC hD hw
    have hM := pencil_posDef A B C D hA hB hC hD hw
    letI := hK.isUnit.invertible
    letI := hM.isUnit.invertible
    have hS : IsUnit (w • A⁻¹ + (1 - w) • C⁻¹ -
        coupling A C w * ⅟(hiddenPencil A B C D w) * (coupling A C w)ᵀ) := by
      rw [Matrix.invOf_eq_nonsing_inv, pencil_schur A B C D hA hB hC hD hw]
      exact ((hA.smul (inv_pos.mpr hw.1)).add hB).inv.add
        (((hC.smul (inv_pos.mpr (sub_pos.mpr hw.2))).add hD).inv) |>.isUnit
    letI := hS.invertible
    letI := Matrix.fromBlocks₂₂Invertible (w • A⁻¹ + (1 - w) • C⁻¹)
      (coupling A C w) (coupling A C w)ᵀ (hiddenPencil A B C D w)
    have h := Matrix.invOf_fromBlocks₂₂_eq (w • A⁻¹ + (1 - w) • C⁻¹)
      (coupling A C w) (coupling A C w)ᵀ (hiddenPencil A B C D w)
    simp only [Matrix.invOf_eq_nonsing_inv] at h
    rw [pencil_schur A B C D hA hB hC hD hw] at h
    ext i j
    exact congrArg (fun N => N (Sum.inl i) (Sum.inl j)) h
  have pencil_det_ratio {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      (splitP A B C D w).det = (hiddenPencil A B C D w).det / (pencil A B C D w).det := by
    have hK := hiddenPencil_posDef A B C D hA hB hC hD hw
    letI := hK.isUnit.invertible
    have h := Matrix.det_fromBlocks₂₂ (w • A⁻¹ + (1 - w) • C⁻¹)
      (coupling A C w) (coupling A C w)ᵀ (hiddenPencil A B C D w)
    simp only [Matrix.invOf_eq_nonsing_inv] at h
    rw [pencil_schur A B C D hA hB hC hD hw] at h
    have hS := ((hA.smul (inv_pos.mpr hw.1)).add hB).inv.add
      (((hC.smul (inv_pos.mpr (sub_pos.mpr hw.2))).add hD).inv)
    change _ = _ / (fromBlocks _ _ _ _).det
    rw [h, splitP, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    field_simp [hK.det_pos.ne', hS.det_pos.ne']
  have pencil_affine {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) :
      pencil A B C D w = pencil A B C D 0 + w • (pencil A B C D 1 - pencil A B C D 0) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [pencil, coupling, hiddenPencil, fromCols, fromBlocks, Matrix.transpose_apply,
        Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have inverseWord_eq {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] (m : ℕ) (N X : R) :
      inverseWord m N X = X * (N * X) ^ m := by
    induction m with
    | zero => simp [inverseWord]
    | succ m ih => simp [inverseWord, ih, pow_succ, mul_assoc]
  have even_word_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
      (X N : Matrix ι ι ℝ) (hX : X.PosSemidef) (hN : N.IsHermitian) (k : ℕ) :
      (X * (N * X) ^ (2 * k)).PosSemidef := by
    have hp := hX.conjTranspose_mul_mul_same ((N * X) ^ k)
    simp only [conjTranspose_pow, conjTranspose_mul, hX.isHermitian.eq, hN.eq] at hp
    convert hp using 1
    simp only [Nat.two_mul, pow_add, mul_pow_mul, mul_assoc]
  have iterated_matrix_inverse_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (m : ℕ) (w : ℝ)
      (hu : IsUnit (M₀ + w • M₁)) :
      iteratedDeriv m (fun x => (M₀ + x • M₁)⁻¹) w =
        ((-1 : ℝ) ^ m * (m.factorial : ℝ)) •
          ((M₀ + w • M₁)⁻¹ * (M₁ * (M₀ + w • M₁)⁻¹) ^ m) := by
    let s : Set ℝ := {x | IsUnit (M₀ + x • M₁)}
    have hs : IsOpen s := Units.isOpen.preimage
      (continuous_const.add (continuous_id.smul continuous_const))
    have h := iterated_inverse_affine_on M₀ M₁ s hs (fun _ hx => hx) m w hu
    simpa only [← Matrix.nonsing_inv_eq_ringInverse, inverseWord_eq] using! h
  have affine_inverse_even_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ)
      (hN : M₁.IsHermitian) (k : ℕ) (w : ℝ) (hM : (M₀ + w • M₁).PosDef) :
      (iteratedDeriv (2 * k) (fun x => (M₀ + x • M₁)⁻¹) w).PosSemidef := by
    rw [iterated_matrix_inverse_affine M₀ M₁ (2 * k) w hM.isUnit]
    apply (even_word_posSemidef _ M₁ hM.inv.posSemidef hN k).smul
    simp [pow_mul]
  have iteratedDeriv_clm {E F : Type}
      [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      (L : E →L[ℝ] F) (f : ℝ → E) (m : ℕ) (w : ℝ) (hf : ContDiffAt ℝ m f w) :
      iteratedDeriv m (fun x => L (f x)) w = L (iteratedDeriv m f w) := by
    unfold iteratedDeriv
    change iteratedFDeriv ℝ m (L ∘ f) w _ = _
    rw [L.iteratedFDeriv_comp_left hf le_rfl]
    rfl
  have pencil_isHermitian {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (hD : D.IsHermitian)
      (w : ℝ) : (pencil A B C D w).IsHermitian := by
    have ha := hA.inv.smul (show IsSelfAdjoint w by rfl)
    have hc := hC.inv.smul (show IsSelfAdjoint (1 - w) by rfl)
    apply (ha.add hc).fromBlocks (conjTranspose_eq_transpose_of_trivial _)
    exact (ha.add hB.inv).fromBlocks (by simp) (hc.add hD.inv)
  have splitP_trace_even_posDef {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      (k : ℕ) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ iteratedDeriv (2 * k) (fun x => (splitP A B C D x).trace) w := by
    let M₀ := pencil A B C D 0
    let M₁ := pencil A B C D 1 - pencil A B C D 0
    have heq : (fun x => (pencil A B C D x)⁻¹) = (fun x => (M₀ + x • M₁)⁻¹) := by
      funext x
      rw [pencil_affine]
    have hp := pencil_posDef A B C D hA hB hC hD hw
    have hMp : (M₀ + w • M₁).PosDef := by
      change (pencil A B C D 0 + w • (pencil A B C D 1 - pencil A B C D 0)).PosDef
      rw [← pencil_affine]
      exact hp
    have hN : M₁.IsHermitian :=
      (pencil_isHermitian A B C D hA.isHermitian hB.isHermitian hC.isHermitian hD.isHermitian 1).sub
        (pencil_isHermitian A B C D hA.isHermitian hB.isHermitian hC.isHermitian hD.isHermitian 0)
    have hpos := affine_inverse_even_posSemidef M₀ M₁ hN k w hMp
    have hevent : (fun x => (splitP A B C D x).trace) =ᶠ[𝓝 w]
        (fun x => cornerTraceCLM n ((pencil A B C D x)⁻¹)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hw] with x hx
      change (splitP A B C D x).trace = ((pencil A B C D x)⁻¹.submatrix Sum.inl Sum.inl).trace
      rw [pencil_inverse_corner A B C D hA hB hC hD hx]
    rw [(hevent.iteratedDeriv (2 * k)).eq_of_nhds]
    have hsm : ContDiffAt ℝ (2 * k) (fun x => (pencil A B C D x)⁻¹) w := by
      rw [heq]
      have haff : ContDiff ℝ (2 * k) (fun x : ℝ => M₀ + x • M₁) :=
        contDiff_const.add (contDiff_id.smul contDiff_const)
      rcases hMp.isUnit with ⟨u, hu⟩
      have hi := contDiffAt_ringInverse ℝ (n := (2 * k : ℕ)) u
      rw [hu] at hi
      simpa only [← Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using!
        hi.comp w haff.contDiffAt
    rw [iteratedDeriv_clm _ _ _ _ hsm, heq]
    exact (hpos.submatrix Sum.inl).trace_nonneg
  have trace_mul_pow_comm {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (m : ℕ) :
      ((A * B) ^ m).trace = ((B * A) ^ m).trace := by
    cases m with
    | zero => simp
    | succ m =>
      calc
        ((A * B) ^ (m + 1)).trace = ((A * B) ^ m * A * B).trace := by
          simp only [pow_succ, Matrix.mul_assoc]
        _ = (B * ((A * B) ^ m * A)).trace := Matrix.trace_mul_comm _ _
        _ = ((B * A) ^ m * B * A).trace := by
          rw [← Matrix.mul_assoc, ← mul_pow_mul B A m]
        _ = _ := by simp only [pow_succ, Matrix.mul_assoc]
  have root_trace_power {ι : Type} [Fintype ι] [DecidableEq ι] (M N S : Matrix ι ι ℝ) (hroot : Sᵀ * S = M) (m : ℕ) :
      ((M⁻¹ * N) ^ m).trace = ((Sᵀ⁻¹ * N * S⁻¹) ^ m).trace := by
    rw [← hroot, Matrix.mul_inv_rev, Matrix.mul_assoc]
    exact trace_mul_pow_comm S⁻¹ (Sᵀ⁻¹ * N) m
  have weighted_trace_compression_of_roots {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (M N S : Matrix ι ι ℝ)
      (E : Matrix ι κ ℝ) (T : Matrix κ κ ℝ) (hN : N.IsHermitian)
      (hS : IsUnit S) (hT : IsUnit T) (hMroot : Sᵀ * S = M)
      (hKroot : Tᵀ * T = Eᵀ * M * E) (k : ℕ) :
      (((Eᵀ * M * E)⁻¹ * (Eᵀ * N * E)) ^ (2 * k)).trace ≤
        ((M⁻¹ * N) ^ (2 * k)).trace := by
    let H := Sᵀ⁻¹ * N * S⁻¹
    let V := S * E * T⁻¹
    have hSd := (Matrix.isUnit_iff_isUnit_det S).mp hS
    have hTd := (Matrix.isUnit_iff_isUnit_det T).mp hT
    have hSi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSd
    have hSj : Sᵀ * Sᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv Sᵀ (by simpa using hSd)
    have hTi : Tᵀ⁻¹ * Tᵀ = 1 := Matrix.nonsing_inv_mul Tᵀ (by simpa using hTd)
    have hTj : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTd
    have hH : H.IsHermitian := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_nonsing_inv] using
        Matrix.isHermitian_conjTranspose_mul_mul S⁻¹ hN
    have hV : Vᵀ * V = 1 := by
      dsimp [V]
      simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      calc
        (Tᵀ⁻¹ * (Eᵀ * Sᵀ)) * (S * E * T⁻¹) =
            Tᵀ⁻¹ * (Eᵀ * (Sᵀ * S) * E) * T⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Tᵀ⁻¹ * (Tᵀ * T) * T⁻¹ := by rw [hMroot, ← hKroot]
        _ = 1 := by
          rw [← Matrix.mul_assoc Tᵀ⁻¹ Tᵀ T, hTi, Matrix.one_mul, hTj]
    have hcomp : Vᵀ * H * V = Tᵀ⁻¹ * (Eᵀ * N * E) * T⁻¹ := by
      dsimp [V, H]
      simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      calc
        (Tᵀ⁻¹ * (Eᵀ * Sᵀ)) * (Sᵀ⁻¹ * N * S⁻¹) * (S * E * T⁻¹) =
            Tᵀ⁻¹ * Eᵀ * (Sᵀ * Sᵀ⁻¹) * N * (S⁻¹ * S) * E * T⁻¹ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [hSj, hSi, Matrix.mul_one, Matrix.mul_assoc]
    have h := trace_even_compression H hH V hV k
    rw [hcomp] at h
    rw [root_trace_power _ _ S hMroot, root_trace_power _ _ T hKroot]
    exact h
  have posDef_root_factor {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.PosDef) :
      ∃ S : Matrix ι ι ℝ, IsUnit S ∧ Sᵀ * S = M := by
    obtain ⟨S, hS, hroot⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hM.isStrictlyPositive
    exact ⟨S, hS, by simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hroot.symm⟩
  have weighted_trace_compression {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (M N : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
      (hM : M.PosDef) (hN : N.IsHermitian) (hK : (Eᵀ * M * E).PosDef) (k : ℕ) :
      (((Eᵀ * M * E)⁻¹ * (Eᵀ * N * E)) ^ (2 * k)).trace ≤
        ((M⁻¹ * N) ^ (2 * k)).trace := by
    obtain ⟨S, hS, hSM⟩ := posDef_root_factor M hM
    obtain ⟨T, hT, hTK⟩ := posDef_root_factor (Eᵀ * M * E) hK
    exact weighted_trace_compression_of_roots M N S E T hN hS hT hSM hTK k
  have iterated_matrix_logdet_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (m : ℕ) (w : ℝ)
      (hu : IsUnit (M₀ + w • M₁)) :
      iteratedDeriv (m + 1) (fun x => Real.log (M₀ + x • M₁).det) w =
        (-1 : ℝ) ^ m * (m.factorial : ℝ) * (((M₀ + w • M₁)⁻¹ * M₁) ^ (m + 1)).trace := by
    let s : Set ℝ := {x | IsUnit (M₀ + x • M₁)}
    have hs : IsOpen s := Units.isOpen.preimage
      (continuous_const.add (continuous_id.smul continuous_const))
    have h := iterated_logdet_affine_on M₀ M₁ s hs (fun _ hx => hx) m w hu
    rw [inverseWord_eq, ← mul_pow_mul, Matrix.mul_assoc, ← pow_succ] at h
    exact h
  have even_logdet_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (k : ℕ) (hk : 1 ≤ k) (w : ℝ)
      (hu : IsUnit (M₀ + w • M₁)) :
      iteratedDeriv (2 * k) (fun x => Real.log (M₀ + x • M₁).det) w =
        -((2 * k - 1).factorial : ℝ) * (((M₀ + w • M₁)⁻¹ * M₁) ^ (2 * k)).trace := by
    have hplus : 2 * k - 1 + 1 = 2 * k := by omega
    have h := iterated_matrix_logdet_affine M₀ M₁ (2 * k - 1) w hu
    rw [hplus] at h
    have hp : (-1 : ℝ) ^ (2 * k - 1) = -1 := by
      have hp : (-1 : ℝ) ^ (2 * k) = 1 := by simp [pow_mul]
      rw [← hplus, pow_succ] at hp
      linarith
    simpa only [hp, neg_one_mul] using h
  have contDiff_det_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (m : ℕ) :
      ContDiff ℝ m (fun x : ℝ => (M₀ + x • M₁).det) := by
    simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have contDiffAt_logdet_affine {ι : Type} [Fintype ι] [DecidableEq ι] (M₀ M₁ : Matrix ι ι ℝ) (m : ℕ) (w : ℝ)
      (hu : IsUnit (M₀ + w • M₁)) :
      ContDiffAt ℝ m (fun x => Real.log (M₀ + x • M₁).det) w := by
    exact (contDiff_det_affine M₀ M₁ m).contDiffAt.log
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu))
  have hiddenInclusion_compress {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) :
      (hiddenInclusion n)ᵀ * pencil A B C D w * hiddenInclusion n = hiddenPencil A B C D w := by
    simp [hiddenInclusion, pencil, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  have hiddenPencil_affine {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ)) (w : ℝ) :
      hiddenPencil A B C D w = hiddenPencil A B C D 0 +
        w • (hiddenPencil A B C D 1 - hiddenPencil A B C D 0) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hiddenPencil, fromBlocks, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have pencil_trace_compression {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      (k : ℕ) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      (((hiddenPencil A B C D w)⁻¹ * (hiddenPencil A B C D 1 - hiddenPencil A B C D 0)) ^ (2 * k)).trace ≤
        (((pencil A B C D w)⁻¹ * (pencil A B C D 1 - pencil A B C D 0)) ^ (2 * k)).trace := by
    have hN :=
      (pencil_isHermitian A B C D hA.isHermitian hB.isHermitian hC.isHermitian hD.isHermitian 1).sub
        (pencil_isHermitian A B C D hA.isHermitian hB.isHermitian hC.isHermitian hD.isHermitian 0)
    have hK : ((hiddenInclusion n)ᵀ * pencil A B C D w * hiddenInclusion n).PosDef := by
      rw [hiddenInclusion_compress]
      exact hiddenPencil_posDef A B C D hA hB hC hD hw
    have h := weighted_trace_compression (pencil A B C D w)
      (pencil A B C D 1 - pencil A B C D 0) (hiddenInclusion n)
      (pencil_posDef A B C D hA hB hC hD hw) hN hK k
    simpa only [Matrix.mul_sub, Matrix.sub_mul, hiddenInclusion_compress] using h
  have splitP_log_even_posDef {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
      (k : ℕ) (hk : 1 ≤ k) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      0 ≤ iteratedDeriv (2 * k) (fun x => Real.log (splitP A B C D x).det) w := by
    let M₀ := pencil A B C D 0
    let M₁ := pencil A B C D 1 - pencil A B C D 0
    let K₀ := hiddenPencil A B C D 0
    let K₁ := hiddenPencil A B C D 1 - hiddenPencil A B C D 0
    have hM : IsUnit (M₀ + w • M₁) := by
      change IsUnit (pencil A B C D 0 + w • (pencil A B C D 1 - pencil A B C D 0))
      rw [← pencil_affine]
      exact (pencil_posDef A B C D hA hB hC hD hw).isUnit
    have hK : IsUnit (K₀ + w • K₁) := by
      change IsUnit (hiddenPencil A B C D 0 + w • (hiddenPencil A B C D 1 - hiddenPencil A B C D 0))
      rw [← hiddenPencil_affine]
      exact (hiddenPencil_posDef A B C D hA hB hC hD hw).isUnit
    have hfM : (fun x => Real.log (pencil A B C D x).det) =
        (fun x => Real.log (M₀ + x • M₁).det) := by
      funext x; rw [pencil_affine]
    have hfK : (fun x => Real.log (hiddenPencil A B C D x).det) =
        (fun x => Real.log (K₀ + x • K₁).det) := by
      funext x; rw [hiddenPencil_affine]
    have hsmM : ContDiffAt ℝ (2 * k) (fun x => Real.log (pencil A B C D x).det) w := by
      rw [hfM]; exact contDiffAt_logdet_affine M₀ M₁ (2 * k) w hM
    have hsmK : ContDiffAt ℝ (2 * k) (fun x => Real.log (hiddenPencil A B C D x).det) w := by
      rw [hfK]; exact contDiffAt_logdet_affine K₀ K₁ (2 * k) w hK
    have hderM := even_logdet_affine M₀ M₁ k hk w hM
    have hderK := even_logdet_affine K₀ K₁ k hk w hK
    rw [← hfM] at hderM
    rw [← hfK] at hderK
    dsimp [M₀, M₁] at hderM
    dsimp [K₀, K₁] at hderK
    rw [← pencil_affine] at hderM
    rw [← hiddenPencil_affine] at hderK
    have hevent : (fun x => Real.log (splitP A B C D x).det) =ᶠ[𝓝 w]
        (fun x => Real.log (hiddenPencil A B C D x).det - Real.log (pencil A B C D x).det) := by
      filter_upwards [isOpen_Ioo.mem_nhds hw] with x hx
      rw [pencil_det_ratio A B C D hA hB hC hD hx]
      exact Real.log_div (hiddenPencil_posDef A B C D hA hB hC hD hx).det_pos.ne'
        (pencil_posDef A B C D hA hB hC hD hx).det_pos.ne'
    rw [(hevent.iteratedDeriv (2 * k)).eq_of_nhds, iteratedDeriv_fun_sub hsmK hsmM,
      hderK, hderM]
    have hc := pencil_trace_compression A B C D hA hB hC hD k hw
    have hf : (0 : ℝ) ≤ ((2 * k - 1).factorial : ℝ) := Nat.cast_nonneg _
    nlinarith
  have continuousAt_iteratedDeriv_parameter (m : ℕ) (f : ℝ × ℝ → ℝ) (e w : ℝ)
      (hf : ContDiffAt ℝ m f (e, w)) :
      ContinuousAt (fun t => iteratedDeriv m (fun x => f (t, x)) w) e := by
    rcases hf.contDiffOn' le_rfl (by simp) with ⟨s, hs, hp, hsf0⟩
    have hsf : ContDiffOn ℝ m f s := hsf0.mono (by simp)
    let L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
    have heq (q : ℝ × ℝ) (hq : q ∈ s) :
        iteratedDeriv m (fun x => f (q.1, x)) q.2 =
          iteratedFDeriv ℝ m f q (fun _ => (0, 1)) := by
      let t := (fun v : ℝ × ℝ => q + v) ⁻¹' s
      have ht : IsOpen t := hs.preimage (continuous_const.add continuous_id)
      have hg : ContDiffOn ℝ m (fun v => f (q + v)) t :=
        hsf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h => h)
      have hz : L 0 ∈ t := by change q + (0 : ℝ × ℝ) ∈ s; simpa using hq
      have hu : IsOpen (L ⁻¹' t) := ht.preimage L.continuous
      have h := L.iteratedFDerivWithin_comp_right hg ht.uniqueDiffOn hu.uniqueDiffOn hz le_rfl
      rw [iteratedFDerivWithin_of_isOpen m hu (show (0 : ℝ) ∈ L ⁻¹' t from hz),
        iteratedFDerivWithin_of_isOpen m ht hz] at h
      have hh := congrArg (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ) ℝ =>
        g (fun _ => 1)) h
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_comp_add_left] at hh
      have hshift := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun x => f (q.1, x)) m q.2 (0 : ℝ)
      have he : (fun x : ℝ => f (q + L x)) = (fun x => f (q.1, q.2 + x)) := by
        funext x; congr 1; ext <;> simp [L]
      rw [show L 0 = 0 from rfl, add_zero] at hh
      simp only [Function.comp_def] at hh
      rw [he, hshift] at hh
      simpa [iteratedDeriv_eq_iteratedFDeriv, L] using hh
    have hc : ContinuousAt (fun q : ℝ × ℝ =>
        iteratedFDeriv ℝ m f q (fun _ => (0, 1))) (e, w) :=
      (hf.continuousAt_iteratedFDeriv le_rfl).eval continuousAt_const
    have hcc := hc.comp (f := fun t : ℝ => (t, w)) (continuousAt_id.prodMk continuousAt_const)
    apply hcc.congr_of_eventuallyEq
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (hs.mem_nhds hp)] with t ht
    exact heq (t, w) ht
  have matrix_inverse_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {ι : Type} [Fintype ι] [DecidableEq ι] {f : E → Matrix ι ι ℝ} {p : E} {m : ℕ}
      (hf : ContDiffAt ℝ m f p) (hu : IsUnit (f p)) :
      ContDiffAt ℝ m (fun x => (f x)⁻¹) p := by
    rcases hu with ⟨u, hu⟩
    have hi := contDiffAt_ringInverse ℝ (n := (m : ℕ)) u
    rw [hu] at hi
    simpa only [← Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using! hi.comp p hf
  have matrix_det_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {ι : Type} [Fintype ι] [DecidableEq ι] {f : E → Matrix ι ι ℝ} {p : E} {m : ℕ}
      (hf : ContDiffAt ℝ m f p) : ContDiffAt ℝ m (fun x => (f x).det) p := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro s hs
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro i hi
    simpa [matrixEntryCLM] using! (matrixEntryCLM (s i) i).contDiff.contDiffAt.comp p hf
  have jointSplitP_contDiffAt {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
      (hAB : (A + B).PosDef) (hCD : (C + D).PosDef)
      (m : ℕ) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      ContDiffAt ℝ m (jointSplitP A B C D) (0, w) := by
    have h1 := input_posDef A B hA hB hAB hw.1 hw.2.le
    have h2 := input_posDef C D hC hD hCD (sub_pos.mpr hw.2) (by linarith [hw.1])
    have hreg (X : (Matrix (Fin n) (Fin n) ℝ)) : ContDiff ℝ m (fun p : ℝ × ℝ => regularize X p.1) :=
      contDiff_const.add (contDiff_fst.smul contDiff_const)
    have hsc1 : ContDiffAt ℝ m (fun p : ℝ × ℝ => p.2⁻¹) (0, w) :=
      contDiffAt_snd.inv hw.1.ne'
    have hsc2 : ContDiffAt ℝ m (fun p : ℝ × ℝ => (1 - p.2)⁻¹) (0, w) :=
      (contDiffAt_const.sub contDiffAt_snd).inv (sub_pos.mpr hw.2).ne'
    have hi1 := matrix_inverse_contDiffAt ((hsc1.smul (hreg A).contDiffAt).add (hreg B).contDiffAt)
      (by simpa [regularize] using h1.isUnit)
    have hi2 := matrix_inverse_contDiffAt ((hsc2.smul (hreg C).contDiffAt).add (hreg D).contDiffAt)
      (by simpa [regularize] using h2.isUnit)
    exact matrix_inverse_contDiffAt (hi1.add hi2) (by simpa [regularize] using (h1.inv.add h2.inv).isUnit)
  have regularized_log_derivative_continuous {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
      (hAB : (A + B).PosDef) (hCD : (C + D).PosDef)
      (m : ℕ) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      ContinuousAt (fun e => iteratedDeriv m
        (fun x => Real.log (splitP (regularize A e) (regularize B e) (regularize C e) (regularize D e) x).det) w) 0 := by
    have hf := jointSplitP_contDiffAt A B C D hA hB hC hD hAB hCD m hw
    have hl : ContDiffAt ℝ m (fun p => Real.log (jointSplitP A B C D p).det) (0, w) :=
      (matrix_det_contDiffAt hf).log (by
        simpa [jointSplitP, regularize] using (splitP_posDef A B C D hA hB hC hD hAB hCD hw).det_pos.ne')
    exact continuousAt_iteratedDeriv_parameter m (fun p => Real.log (jointSplitP A B C D p).det) 0 w hl
  have regularized_trace_derivative_continuous {n : ℕ} (A B C D : (Matrix (Fin n) (Fin n) ℝ))
      (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
      (hAB : (A + B).PosDef) (hCD : (C + D).PosDef)
      (m : ℕ) {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
      ContinuousAt (fun e => iteratedDeriv m
        (fun x => (splitP (regularize A e) (regularize B e) (regularize C e) (regularize D e) x).trace) w) 0 := by
    have hf := jointSplitP_contDiffAt A B C D hA hB hC hD hAB hCD m hw
    have ht : ContDiffAt ℝ m (fun p => (jointSplitP A B C D p).trace) (0, w) := by
      simpa [matrixTraceCLM] using! (matrixTraceCLM (ι := Fin n)).contDiff.contDiffAt.comp (0, w) hf
    exact continuousAt_iteratedDeriv_parameter m (fun p => (jointSplitP A B C D p).trace) 0 w ht
  have regularize_posDef {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℝ)) (hA : A.PosSemidef)
      {e : ℝ} (he : 0 < e) : (regularize A e).PosDef :=
    (Matrix.PosDef.one.smul he).posSemidef_add hA
  intro n A B C D hA hB hC hD hAB hCD k hk w hw
  have hlog := regularized_log_derivative_continuous A B C D hA hB hC hD hAB hCD (2 * k) hw
  have htr := regularized_trace_derivative_continuous A B C D hA hB hC hD hAB hCD (2 * k) hw
  constructor
  · have htend : Tendsto (fun e => iteratedDeriv (2 * k)
        (fun x => Real.log (splitP (regularize A e) (regularize B e) (regularize C e) (regularize D e) x).det) w)
        (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv (2 * k) (fun x => Real.log (splitP A B C D x).det) w)) := by
      simpa [regularize] using hlog.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with e he
    exact splitP_log_even_posDef _ _ _ _ (regularize_posDef A hA he) (regularize_posDef B hB he)
      (regularize_posDef C hC he) (regularize_posDef D hD he) k hk hw
  · have htend : Tendsto (fun e => iteratedDeriv (2 * k)
        (fun x => (splitP (regularize A e) (regularize B e) (regularize C e) (regularize D e) x).trace) w)
        (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv (2 * k) (fun x => (splitP A B C D x).trace) w)) := by
      simpa [regularize] using htr.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with e he
    exact splitP_trace_even_posDef _ _ _ _ (regularize_posDef A hA he) (regularize_posDef B hB he)
      (regularize_posDef C hC he) (regularize_posDef D hD he) k hw

end D5.S3.Estimation.SplitCovarianceIntersectionEvenConvexity
