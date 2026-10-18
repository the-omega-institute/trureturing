/- GID: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/UnitarilyInvariantNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular-value reduction and diagonal monotonicity for unitarily invariant norms. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Schatten.CompoundMatrices
import D5.S3.Geometry.AlphaGeometry.MajorizationTransfer

/-! Unitarily invariant matrix norms and their real diagonal gauges. -/

noncomputable section

namespace D5.S3.Quantum.Schatten

open Matrix

/-- A unitarily invariant norm on complex `n × n` matrices. -/
structure UINorm (n : ℕ) where
  N : Matrix (Fin n) (Fin n) ℂ → ℝ
  nonneg : ∀ X, 0 ≤ N X
  eq_zero_iff : ∀ X, N X = 0 ↔ X = 0
  add_le : ∀ X Y, N (X + Y) ≤ N X + N Y
  smul_eq : ∀ (c : ℂ) X, N (c • X) = ‖c‖ * N X
  unitary_invariant : ∀ U V X, U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    V ∈ Matrix.unitaryGroup (Fin n) ℂ → N (U * X * V) = N X

namespace UINorm

variable {n : ℕ} (ν : UINorm n)

set_option maxHeartbeats 1000000 in
/-- A unitarily invariant norm depends only on the singular values. -/
theorem N_eq_singularValues (X : Matrix (Fin n) (Fin n) ℂ) :
    ν.N X = ν.N (diagonal (fun i => (singularValues X i : ℂ))) := by
  obtain ⟨U, V, h⟩ :=
    Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues X
  have hV : (V.val)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    exact (star V).property
  have h : X = U.val * diagonal (fun i => (singularValues X i : ℂ)) * V.valᴴ := by
    simpa only [singularValues, conjTranspose_conjTranspose] using h
  conv_lhs => rw [h]
  exact ν.unitary_invariant _ _ _ U.property hV

set_option maxHeartbeats 1000000 in
/-- Taking the adjoint preserves every unitarily invariant norm. -/
theorem N_conjTranspose (X : Matrix (Fin n) (Fin n) ℂ) : ν.N Xᴴ = ν.N X := by
  obtain ⟨U, V, h⟩ :=
    Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues X
  have h : X = U.val * diagonal (fun i => (singularValues X i : ℂ)) * V.valᴴ := by
    simpa only [singularValues, conjTranspose_conjTranspose] using h
  have hD : (diagonal (fun i => (singularValues X i : ℂ)))ᴴ =
      diagonal (fun i => (singularValues X i : ℂ)) := by simp
  calc
    ν.N Xᴴ = ν.N (V.val * diagonal (fun i => (singularValues X i : ℂ)) * U.valᴴ) := by
      conv_lhs => rw [h]
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hD,
        Matrix.mul_assoc]
    _ = ν.N (diagonal (fun i => (singularValues X i : ℂ))) :=
      ν.unitary_invariant _ _ _ V.property (star U).property
    _ = ν.N X := (ν.N_eq_singularValues X).symm

set_option maxHeartbeats 1000000 in
/-- Plain transpose also preserves every complex unitarily invariant norm. -/
theorem N_transpose (X : Matrix (Fin n) (Fin n) ℂ) : ν.N Xᵀ = ν.N X := by
  obtain ⟨U, V, h⟩ :=
    Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues X
  have h : X = U.val * diagonal (fun i => (singularValues X i : ℂ)) * V.valᴴ := by
    simpa only [singularValues, conjTranspose_conjTranspose] using h
  calc
    ν.N Xᵀ = ν.N ((V.valᴴ)ᵀ * diagonal (fun i => (singularValues X i : ℂ)) * U.valᵀ) := by
      conv_lhs => rw [h]
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    _ = ν.N (diagonal (fun i => (singularValues X i : ℂ))) :=
      ν.unitary_invariant _ _ _
        (transpose_mem_unitaryGroup_iff.mpr (star V).property)
        (transpose_mem_unitaryGroup_iff.mpr U.property)
    _ = ν.N X := (ν.N_eq_singularValues X).symm

private theorem N_diagonal_update_le (x : Fin n → ℝ) (i : Fin n) (c : ℝ)
    (hc : |c| ≤ 1) :
    ν.N (diagonal (fun j => ((Function.update x i (c * x i)) j : ℂ))) ≤
      ν.N (diagonal (fun j => (x j : ℂ))) := by
  classical
  let X := diagonal (fun j => (x j : ℂ))
  let U : Matrix (Fin n) (Fin n) ℂ := diagonal (fun j => if j = i then -1 else 1)
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff]
    change U * Uᴴ = 1
    simp only [U, diagonal_conjTranspose, diagonal_mul_diagonal]
    ext j k
    by_cases hjk : j = k
    · subst k
      by_cases hji : j = i <;> simp [hji]
    · simp [hjk]
  have hN : ν.N (U * X) = ν.N X := by
    simpa using ν.unitary_invariant U 1 X hU (by simp)
  let α : ℝ := (1 + c) / 2
  let β : ℝ := (1 - c) / 2
  have hα : 0 ≤ α := by dsimp [α]; linarith [(abs_le.mp hc).1]
  have hβ : 0 ≤ β := by dsimp [β]; linarith [(abs_le.mp hc).2]
  have hmix : diagonal (fun j => ((Function.update x i (c * x i)) j : ℂ)) =
      (α : ℂ) • X + (β : ℂ) • (U * X) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      by_cases hji : j = i
      · subst j
        simp [X, U, diagonal_mul_diagonal, α, β]
        ring
      · simp [X, U, diagonal_mul_diagonal, hji, α, β]
        ring
    · simp [X, U, diagonal_mul_diagonal, hjk]
  rw [hmix]
  calc
    ν.N ((α : ℂ) • X + (β : ℂ) • (U * X)) ≤
        ν.N ((α : ℂ) • X) + ν.N ((β : ℂ) • (U * X)) := ν.add_le _ _
    _ = α * ν.N X + β * ν.N X := by
      rw [ν.smul_eq, ν.smul_eq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hβ, hN]
    _ = ν.N X := by dsimp [α, β]; ring

/-- Coordinatewise contraction of real diagonal entries decreases a unitarily invariant norm. -/
theorem N_diagonal_contract (x c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1) :
    ν.N (diagonal (fun i => ((c i * x i : ℝ) : ℂ))) ≤
      ν.N (diagonal (fun i => (x i : ℂ))) := by
  classical
  have h (s : Finset (Fin n)) :
      ν.N (diagonal (fun i => (((if i ∈ s then c i * x i else x i) : ℝ) : ℂ))) ≤
        ν.N (diagonal (fun i => (x i : ℂ))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let y : Fin n → ℝ := fun j => if j ∈ s then c j * x j else x j
      have heq : (fun j => if j ∈ insert i s then c j * x j else x j) =
          Function.update y i (c i * y i) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [y, hi]
        · simp [hji, y]
      have heq' : diagonal (fun j => (((if j ∈ insert i s then c j * x j else x j) : ℝ) : ℂ)) =
          diagonal (fun j => ((Function.update y i (c i * y i)) j : ℂ)) := by
        congr 1
        funext j
        exact congrArg Complex.ofReal (congrFun heq j)
      rw [heq']
      exact (ν.N_diagonal_update_le y i (c i) (hc i)).trans ih
  simpa using h Finset.univ

/-- The real diagonal gauge is monotone with respect to coordinatewise absolute values. -/
theorem N_diagonal_mono (x y : Fin n → ℝ) (hxy : ∀ i, |x i| ≤ |y i|) :
    ν.N (diagonal (fun i => (x i : ℂ))) ≤
      ν.N (diagonal (fun i => (y i : ℂ))) := by
  classical
  let c : Fin n → ℝ := fun i => if y i = 0 then 0 else x i / y i
  have hc : ∀ i, |c i| ≤ 1 := by
    intro i
    by_cases hi : y i = 0
    · simp [c, hi]
    · simpa [c, hi, abs_div] using
        (div_le_one (abs_pos.mpr hi)).mpr (hxy i)
  have heq : ∀ i, c i * y i = x i := by
    intro i
    by_cases hi : y i = 0
    · have hx : x i = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hi] using hxy i)
          (abs_nonneg _))
      simp [c, hi, hx]
    · simp [c, hi]
  simpa only [heq] using ν.N_diagonal_contract y c hc

/-- Permuting real diagonal entries preserves every unitarily invariant norm. -/
theorem N_diagonal_perm (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ν.N (diagonal (fun i => (x (σ i) : ℂ))) =
      ν.N (diagonal (fun i => (x i : ℂ))) := by
  have hP : σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff]
    change σ.permMatrix ℂ * (σ.permMatrix ℂ)ᴴ = 1
    rw [conjTranspose_permMatrix, ← permMatrix_mul]
    simp
  have heq : σ.permMatrix ℂ * diagonal (fun i => (x i : ℂ)) * (σ.permMatrix ℂ)ᴴ =
      diagonal (fun i => (x (σ i) : ℂ)) := by
    rw [conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [submatrix_apply, diagonal, Equiv.Perm.inv_def]
  rw [← heq]
  exact ν.unitary_invariant _ _ _ hP (show _ from (star ⟨_, hP⟩ :
    Matrix.unitaryGroup (Fin n) ℂ).property)

/-- A diagonally weighted permutation has the diagonal gauge of its matched weights. -/
theorem N_diagonal_permMatrix (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ν.N (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
      diagonal (fun i => (b i : ℂ))) =
      ν.N (diagonal (fun i => ((a i * b (σ i) : ℝ) : ℂ))) := by
  have hP : σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff]
    change σ.permMatrix ℂ * (σ.permMatrix ℂ)ᴴ = 1
    rw [conjTranspose_permMatrix, ← permMatrix_mul]
    simp
  have hconj : σ.permMatrix ℂ * diagonal (fun i => (b i : ℂ)) *
      (σ.permMatrix ℂ)ᴴ = diagonal (fun i => (b (σ i) : ℂ)) := by
    rw [conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [submatrix_apply, diagonal, Equiv.Perm.inv_def]
  have heq : (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
      diagonal (fun i => (b i : ℂ))) * (σ.permMatrix ℂ)ᴴ =
      diagonal (fun i => ((a i * b (σ i) : ℝ) : ℂ)) := by
    calc
      _ = diagonal (fun i => (a i : ℂ)) * (σ.permMatrix ℂ *
          diagonal (fun i => (b i : ℂ)) * (σ.permMatrix ℂ)ᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hconj, diagonal_mul_diagonal]; simp
  rw [← heq]
  simpa only [one_mul] using (ν.unitary_invariant 1 (σ.permMatrix ℂ)ᴴ
    (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ * diagonal (fun i => (b i : ℂ)))
    (by simp) (show _ from (star ⟨_, hP⟩ : Matrix.unitaryGroup (Fin n) ℂ).property)).symm

private theorem N_diagonal_convex (x y : Fin n → ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ν.N (diagonal (fun i => (((1 - c) * x i + c * y i : ℝ) : ℂ))) ≤
      (1 - c) * ν.N (diagonal (fun i => (x i : ℂ))) +
        c * ν.N (diagonal (fun i => (y i : ℂ))) := by
  have heq : diagonal (fun i => (((1 - c) * x i + c * y i : ℝ) : ℂ)) =
      ((1 - c : ℝ) : ℂ) • diagonal (fun i => (x i : ℂ)) +
        (c : ℂ) • diagonal (fun i => (y i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [heq]
  convert ν.add_le (((1 - c : ℝ) : ℂ) • diagonal (fun i => (x i : ℂ)))
    ((c : ℂ) • diagonal (fun i => (y i : ℂ))) using 1
  rw [ν.smul_eq, ν.smul_eq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_nonneg hc0]

open Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector in
private theorem N_diagonal_tTransform {x y : Fin n → ℝ} (h : IsTTransform x y) :
    ν.N (diagonal (fun i => (y i : ℂ))) ≤
      ν.N (diagonal (fun i => (x i : ℂ))) := by
  obtain ⟨i, j, c, hc0, hc1, rfl⟩ := h
  calc
    ν.N (diagonal (fun k => (((1 - c) • x + c • (x ∘ Equiv.swap i j)) k : ℂ))) ≤
        (1 - c) * ν.N (diagonal (fun k => (x k : ℂ))) +
          c * ν.N (diagonal (fun k => (x (Equiv.swap i j k) : ℂ))) :=
      ν.N_diagonal_convex x (x ∘ Equiv.swap i j) c hc0 hc1
    _ = ν.N (diagonal (fun k => (x k : ℂ))) := by
      rw [ν.N_diagonal_perm x (Equiv.swap i j)]
      ring

open Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector in
/-- Weak majorization of nonnegative vectors decreases every unitarily invariant diagonal gauge.
Only the vector on the left needs to be in decreasing order. -/
theorem N_diagonal_weakMajorization (z q : Fin n → ℝ) (hz : Antitone z)
    (hz0 : ∀ i, 0 ≤ z i) (hq0 : ∀ i, 0 ≤ q i)
    (hpre : ∀ k, prefixSum k z ≤ prefixSum k q) :
    ν.N (diagonal (fun i => (z i : ℂ))) ≤
      ν.N (diagonal (fun i => (q i : ℂ))) := by
  classical
  suffices h : ∀ d (q : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      (∀ i, 0 ≤ q i) → (∀ k, prefixSum k z ≤ prefixSum k q) →
      ν.N (diagonal (fun i => (z i : ℂ))) ≤
        ν.N (diagonal (fun i => (q i : ℂ))) from
    h _ q le_rfl hq0 hpre
  intro d
  induction d with
  | zero =>
    intro q hcard hq0 hpre
    have heq : z = q := by
      funext i
      by_contra hi
      have hm : i ∈ Finset.univ.filter (fun i => z i ≠ q i) := by simp [hi]
      have hp := Finset.card_pos.mpr ⟨i, hm⟩
      omega
    simp [heq]
  | succ d ih =>
    intro q hcard hq0 hpre
    by_cases hle : ∀ i, z i ≤ q i
    · exact ν.N_diagonal_mono z q (fun i => by
        simpa only [abs_of_nonneg (hz0 i), abs_of_nonneg (hq0 i)] using hle i)
    · obtain ⟨q', htr, hq'0, hq'pre, hcard'⟩ :=
        exists_isTTransform_of_not_forall_le hz hz0 hq0 hpre hle
      exact (ih q' (by omega) hq'0 hq'pre).trans (ν.N_diagonal_tTransform htr)

end UINorm
end D5.S3.Quantum.Schatten
