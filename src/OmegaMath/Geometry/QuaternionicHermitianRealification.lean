import OmegaBuild.Commands
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Opposite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

Quaternionic matrix multiplication acts on the real inner product space of
quaternionic columns. Hermitian matrices give symmetric operators, and the
operators commute with right scalar multiplication.
-/

open scoped BigOperators InnerProductSpace Matrix Quaternion

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

variable {ι : Type*} [Fintype ι]

/-- A quaternionic column with its real Euclidean inner product. -/
abbrev Columns (ι : Type*) := PiLp 2 (fun _ : ι => ℍ[ℝ])

/-- Left matrix multiplication on realified quaternionic columns. -/
def realAction (M : Matrix ι ι ℍ[ℝ]) : Columns ι →ₗ[ℝ] Columns ι where
  toFun x := WithLp.toLp 2 fun i => ∑ j, M i j * x j
  map_add' x y := by
    apply PiLp.ext
    intro i
    change (∑ j, M i j * (x j + y j)) = _
    simp only [mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' c x := by
    apply PiLp.ext
    intro i
    change (∑ j, M i j * (c • x j)) = c • ∑ j, M i j * x j
    simp only [mul_smul_comm, Finset.smul_sum]

@[simp] theorem realAction_apply (M : Matrix ι ι ℍ[ℝ]) (x : Columns ι) (i : ι) :
    realAction M x i = ∑ j, M i j * x j := rfl

/-- Right multiplication of each coordinate of a column. -/
def rightMul (q : ℍ[ℝ]) (x : Columns ι) : Columns ι :=
  WithLp.toLp 2 fun i => x i * q

omit [Fintype ι] in
@[simp] theorem rightMul_apply (q : ℍ[ℝ]) (x : Columns ι) (i : ι) :
    rightMul q x i = x i * q := rfl

theorem realAction_rightMul (M : Matrix ι ι ℍ[ℝ]) (q : ℍ[ℝ]) (x : Columns ι) :
    realAction M (rightMul q x) = rightMul q (realAction M x) := by
  apply PiLp.ext
  intro i
  simp only [realAction_apply, rightMul_apply, Finset.sum_mul, mul_assoc]

theorem re_mul_cycle (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

/-- Quaternionic Hermitian multiplication is symmetric in the real inner product. -/
theorem isSymmetric_realAction {M : Matrix ι ι ℍ[ℝ]} (h : M.IsHermitian) :
    (realAction M).IsSymmetric := by
  intro x y
  have hstar (i j) : star (M i j) = M j i := by
    have hh := congrFun (congrFun h j) i
    exact hh
  simp only [PiLp.inner_apply, realAction_apply, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Quaternion.inner_def, star_mul, hstar]
  rw [mul_assoc, re_mul_cycle (M i j), mul_assoc]

/-- A quaternionic eigenspace is closed under all right scalar multiplications. -/
theorem real_eigenvector_rightMul {M : Matrix ι ι ℍ[ℝ]} {x : Columns ι}
    {μ : ℝ} (hx : realAction M x = μ • x) (q : ℍ[ℝ]) :
    realAction M (rightMul q x) = μ • rightMul q x := by
  rw [realAction_rightMul, hx]
  apply PiLp.ext
  intro i
  change (μ • x i) * q = μ • (x i * q)
  exact smul_mul_assoc μ (x i) q


section Multiplicity

open MulOpposite

private def rightEigenspace (M : Matrix ι ι ℍ[ℝ]) (μ : ℝ) :
    Submodule (ℍ[ℝ]ᵐᵒᵖ) (Columns ι) where
  carrier := {x | realAction M x = μ • x}
  add_mem' := by
    intro x y hx hy
    change realAction M x = μ • x at hx
    change realAction M y = μ • y at hy
    change realAction M (x + y) = μ • (x + y)
    rw [map_add, hx, hy, smul_add]
  zero_mem' := by simp
  smul_mem' q x hx := by
    change realAction M x = μ • x at hx
    change realAction M (rightMul q.unop x) = μ • rightMul q.unop x
    exact real_eigenvector_rightMul hx _

private theorem restricted_rightEigenspace (M : Matrix ι ι ℍ[ℝ]) (μ : ℝ) :
    (rightEigenspace M μ).restrictScalars ℝ = Module.End.eigenspace (realAction M) μ := by
  ext x
  exact Module.End.mem_eigenspace_iff.symm

/-- Every real eigenspace of a quaternionic matrix has dimension divisible by
four, since it is a module for right quaternionic scalar multiplication. -/
theorem four_dvd_finrank_eigenspace (M : Matrix ι ι ℍ[ℝ]) (μ : ℝ) :
    4 ∣ Module.finrank ℝ (Module.End.eigenspace (realAction M) μ) := by
  rw [← restricted_rightEigenspace]
  change 4 ∣ Module.finrank ℝ (rightEigenspace M μ)
  have hd : Module.finrank ℝ (ℍ[ℝ]ᵐᵒᵖ) = 4 :=
    (MulOpposite.opLinearEquiv ℝ (M := ℍ[ℝ])).symm.finrank_eq.trans Quaternion.finrank_eq_four
  rw [← hd]
  exact ⟨Module.finrank (ℍ[ℝ]ᵐᵒᵖ) (rightEigenspace M μ),
    (Module.finrank_mul_finrank ℝ (ℍ[ℝ]ᵐᵒᵖ) (rightEigenspace M μ)).symm⟩

end Multiplicity


open Finset

private theorem finrank_columns (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (Columns ι) = Fintype.card ι * 4 := by
  rw [(WithLp.linearEquiv 2 ℝ (ι → ℍ[ℝ])).finrank_eq, Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four]

private theorem four_dvd_card_strict {n : ℕ} (f : Fin (n * 4) → ℝ)
    (h : ∀ y, 4 ∣ #{i : Fin (n * 4) | f i = y}) (y : ℝ) :
    4 ∣ #{i : Fin (n * 4) | y < f i} := by
  classical
  let values := (univ.image f).filter (fun z => y < z)
  have hf : univ.filter (fun i => f i ∈ values) = univ.filter (fun i => y < f i) := by
    ext i
    simp [values]
  rw [← hf, ← sum_card_fiberwise_eq_card_filter univ values f]
  exact Finset.dvd_sum fun z _ => h z

private theorem constant_on_blocks {n : ℕ} (f : Fin (n * 4) → ℝ) (hf : Antitone f)
    (hcount : ∀ y, 4 ∣ #{i : Fin (n * 4) | f i = y}) (i : Fin n) (j : Fin 4) :
    f (finProdFinEquiv (i, j)) = f (finProdFinEquiv (i, 0)) := by
  classical
  let a := finProdFinEquiv (i, (0 : Fin 4))
  let b := finProdFinEquiv (i, j)
  have hab : a ≤ b := by change 0 + 4 * i.val ≤ j.val + 4 * i.val; omega
  apply le_antisymm (hf hab)
  by_contra! hlt
  let s := univ.filter fun k => f b < f k
  have ha : Iic a ⊆ s := by
    intro k hk
    exact mem_filter.mpr ⟨mem_univ _, hlt.trans_le (hf (mem_Iic.mp hk))⟩
  have hb : s ⊆ Iio b := by
    intro k hk
    rw [mem_Iio]
    by_contra! hkb
    exact (not_lt_of_ge (hf hkb)) (mem_filter.mp hk).2
  have hca := card_le_card ha
  have hcb := card_le_card hb
  rw [Fin.card_Iic] at hca
  rw [Fin.card_Iio] at hcb
  obtain ⟨q, hq⟩ := four_dvd_card_strict f hcount (f b)
  change s.card = 4 * q at hq
  change 0 + 4 * i.val + 1 ≤ s.card at hca
  change s.card ≤ j.val + 4 * i.val at hcb
  omega

/-- The ordered real spectrum consists of four copies of each ordered
quaternionic eigenvalue, including multiplicities inside a common eigenspace. -/
theorem exists_ordered_spectrum {M : Matrix ι ι ℍ[ℝ]} (hM : M.IsHermitian) :
    let m := Fintype.card ι
    ∃ μ : Fin m → ℝ, Antitone μ ∧
      ∃ b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι),
      ∀ i j, realAction M (b (i, j)) = μ i • b (i, j) := by
  classical
  let h := isSymmetric_realAction hM
  let hn := finrank_columns ι
  let f := h.eigenvalues hn
  have hf := h.eigenvalues_antitone hn
  have hcount (x : ℝ) : 4 ∣ #{i | f i = x} := by
    change 4 ∣ #{i | h.eigenvalues hn i = x}
    have hcard := h.card_filter_eigenvalues_eq (𝕜 := ℝ) hn x
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hcard
    rw [hcard]
    exact four_dvd_finrank_eigenspace M x
  let μ (i : Fin (Fintype.card ι)) := f (finProdFinEquiv (i, 0))
  refine ⟨μ, ?_, (h.eigenvectorBasis hn).reindex finProdFinEquiv.symm, ?_⟩
  · intro a b hab
    apply hf
    change 0 + 4 * a.val ≤ 0 + 4 * b.val
    omega
  · intro i j
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm, h.apply_eigenvectorBasis]
    change f (finProdFinEquiv (i, j)) • _ = μ i • _
    rw [constant_on_blocks f hf hcount]


section Trace

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- Realification preserves multiplication of quaternionic matrices. -/
theorem realAction_mul (A B : Matrix ι ι ℍ[ℝ]) :
    realAction (A * B) = realAction A * realAction B := by
  ext x : 1
  apply PiLp.ext
  intro i
  simp only [realAction_apply, Module.End.mul_apply, Matrix.mul_apply, sum_mul, mul_sum,
    mul_assoc]
  rw [sum_comm]

theorem realAction_one : realAction (1 : Matrix ι ι ℍ[ℝ]) = 1 := by
  ext x : 1
  apply PiLp.ext
  intro i
  simp only [realAction_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true, Module.End.one_apply]

/-- Realification preserves matrix powers. -/
theorem realAction_pow (M : Matrix ι ι ℍ[ℝ]) (k : ℕ) :
    realAction (M ^ k) = realAction M ^ k := by
  induction k with
  | zero => simp [realAction_one]
  | succ k ih => rw [pow_succ, pow_succ, realAction_mul, ih]

private def columnCoords : Columns ι ≃ₗ[ℝ] ((ι × Fin 4) → ℝ) where
  toFun x ij := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) (x ij.1) ij.2
  invFun y := WithLp.toLp 2 fun i =>
    (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm (fun j => y (i, j))
  left_inv x := by
    apply PiLp.ext
    intro i
    exact (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm_apply_apply (x i)
  right_inv y := by
    funext ij
    exact congrFun ((QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).apply_symm_apply
      (fun j => y (ij.1, j))) ij.2
  map_add' x y := by
    funext ij
    exact congrFun ((QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).map_add
      (x ij.1) (y ij.1)) ij.2
  map_smul' c x := by
    funext ij
    exact congrFun ((QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).map_smul
      c (x ij.1)) ij.2

private def columnBasis : Module.Basis (ι × Fin 4) ℝ (Columns ι) :=
  Module.Basis.ofEquivFun columnCoords

private theorem columnBasis_apply (i : ι) (j : Fin 4) :
    (columnBasis (i, j) : Columns ι) i =
      (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm
        (fun k => if j = k then 1 else 0) := by
  have hd (k : Fin 4) :
      columnCoords (columnBasis (i, j)) (i, k) = if j = k then 1 else 0 := by
    change (columnBasis.equivFun (columnBasis (i, j)) (i, k)) = _
    rw [Module.Basis.equivFun_self]
    simp
  apply (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).injective
  rw [LinearEquiv.apply_symm_apply]
  funext k
  exact hd k

private theorem columnBasis_apply_ne {i i' : ι} (h : i' ≠ i) (j : Fin 4) :
    (columnBasis (i, j) : Columns ι) i' = 0 := by
  apply (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).injective
  rw [map_zero]
  funext k
  change columnBasis.equivFun (columnBasis (i, j)) (i', k) = 0
  rw [Module.Basis.equivFun_self, ite_eq_right]
  exact fun he => h (congrArg Prod.fst he).symm

/-- The real trace of left multiplication is four times the sum of the
real parts of the quaternionic diagonal entries. -/
theorem trace_realAction (M : Matrix ι ι ℍ[ℝ]) :
    LinearMap.trace ℝ (Columns ι) (realAction M) = 4 * ∑ i, (M i i).re := by
  rw [LinearMap.trace_eq_matrix_trace ℝ columnBasis]
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  trans ∑ i, ∑ _j : Fin 4, (M i i).re
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    change columnCoords (realAction M (columnBasis (i, j))) (i, j) = _
    change QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)
      (realAction M (columnBasis (i, j)) i) j = _
    rw [realAction_apply, sum_eq_single i]
    · rw [columnBasis_apply]
      change QuaternionAlgebra.equivTuple (-1 : ℝ) 0 (-1)
        (M i i * (QuaternionAlgebra.equivTuple (-1 : ℝ) 0 (-1)).symm
          (fun k => if j = k then 1 else 0)) j = _
      fin_cases j <;>
        norm_num [QuaternionAlgebra.equivTuple, Quaternion.re_mul]
    · intro k _ hk
      rw [columnBasis_apply_ne hk, mul_zero]
    · simp
  · simp [← Finset.mul_sum]

/-- Every spectral moment is the sum of the real diagonal entries of the
corresponding quaternionic matrix power. -/
theorem spectrum_moments (M : Matrix ι ι ℍ[ℝ]) {μ : Fin (Fintype.card ι) → ℝ}
    (b : OrthonormalBasis (Fin (Fintype.card ι) × Fin 4) ℝ (Columns ι))
    (hb : ∀ i j, realAction M (b (i, j)) = μ i • b (i, j)) (k : ℕ) :
    ∑ i, μ i ^ k = ∑ i, ((M ^ k) i i).re := by
  have hpow (i) (j) : (realAction M ^ k) (b (i, j)) = μ i ^ k • b (i, j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, ih, map_smul, hb, smul_smul, mul_comm]
  have h := trace_realAction (M ^ k)
  rw [realAction_pow, LinearMap.trace_eq_matrix_trace ℝ b.toBasis] at h
  unfold Matrix.trace at h
  rw [Fintype.sum_prod_type] at h
  have hterm (i) (j) :
      (LinearMap.toMatrix b.toBasis b.toBasis (realAction M ^ k)).diag (i, j) = μ i ^ k := by
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    change b.toBasis.repr ((realAction M ^ k) (b (i, j))) (i, j) = _
    rw [hpow]
    simp
  simp only [hterm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    ← mul_sum] at h
  linarith only [h]

end Trace

end Omega.Geometry.HolonomySpectrum
