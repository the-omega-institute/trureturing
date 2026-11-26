/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/ConstantDiagonal
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier conjugation makes a Hermitian matrix diagonal constant. -/

import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import Mathlib.Analysis.Matrix.Spectrum

/-! A Fourier change of eigenbasis replaces each diagonal entry of a
Hermitian matrix by its normalized trace. -/

namespace RefinedBMV.Tracial

open Matrix
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

/-- A unitary conjugate of a finite Hermitian matrix has constant
diagonal equal to the normalized trace. -/
theorem exists_unitary_const_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    ∃ U : Matrix.unitaryGroup ι ℂ, ∀ i,
      Unitary.conjStarAlgAut ℂ _ U B i i = trace B / (Fintype.card ι : ℂ) := by
  classical
  rcases isEmpty_or_nonempty ι with h | h
  · let _ := h
    exact ⟨1, fun i ↦ isEmptyElim i⟩
  let _ := h
  let d := Fintype.card ι
  let _ : NeZero d := ⟨Fintype.card_ne_zero⟩
  let e : ι ≃ ZMod d := (Fintype.equivFin ι).trans (ZMod.finEquiv d).toEquiv
  let F : Matrix ι ι ℂ := (transform d).submatrix e e
  have hF : F ∈ Matrix.unitaryGroup ι ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose]
    change (transform d).submatrix e e * ((transform d).submatrix e e)ᴴ = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      transform_unitary, Matrix.submatrix_one_equiv]
  have hflat (i j : ι) : F i j * star (F i j) = (d : ℂ)⁻¹ := by
    have ha : ‖F i j‖ = (Real.sqrt d)⁻¹ := by
      simp [F, transform, Matrix.submatrix_apply, ZMod.stdAddChar_apply,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_div]
    rw [Complex.star_def, Complex.mul_conj', ha, ← Complex.ofReal_pow, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_inv, Complex.ofReal_natCast]
  let V : Matrix.unitaryGroup ι ℂ := ⟨F, hF⟩
  refine ⟨V * star hB.eigenvectorUnitary, fun i ↦ ?_⟩
  rw [Unitary.conjStarAlgAut_mul_apply, hB.conjStarAlgAut_star_eigenvectorUnitary,
    Unitary.conjStarAlgAut_apply]
  change (F * diagonal (fun j ↦ (hB.eigenvalues j : ℂ)) * Fᴴ) i i = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  calc
    (∑ j, (F i j * (hB.eigenvalues j : ℂ)) * star (F i j)) =
        ∑ j, (hB.eigenvalues j : ℂ) * (d : ℂ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show F i j * (hB.eigenvalues j : ℂ) * star (F i j) =
          (hB.eigenvalues j : ℂ) * (F i j * star (F i j)) by ring, hflat]
    _ = _ := by
      rw [← Finset.sum_mul, hB.trace_eq_sum_eigenvalues, div_eq_mul_inv]
      rfl

/-- A block diagonal unitary makes each compressed Hermitian block have
constant diagonal while fixing every diagonal matrix scalar on each block. -/
theorem exists_unitary_const_diagonal_blocks {s : Type*} [Fintype s] [DecidableEq s]
    (ι : s → Type*) [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    {B : Matrix (Σ a, ι a) (Σ a, ι a) ℂ} (hB : B.IsHermitian) :
    ∃ U : Matrix.unitaryGroup (Σ a, ι a) ℂ,
      (∀ z : s → ℂ, Unitary.conjStarAlgAut ℂ _ U (diagonal (fun i ↦ z i.1)) =
        diagonal (fun i ↦ z i.1)) ∧
      (∀ a (i : ι a), Unitary.conjStarAlgAut ℂ _ U B ⟨a, i⟩ ⟨a, i⟩ =
        trace (B.submatrix (Sigma.mk a) (Sigma.mk a)) / (Fintype.card (ι a) : ℂ)) := by
  classical
  choose V hV using fun a ↦ exists_unitary_const_diagonal (hB.submatrix (Sigma.mk a))
  let M (a : s) : Matrix (ι a) (ι a) ℂ := V a
  let W : Matrix (Σ a, ι a) (Σ a, ι a) ℂ := blockDiagonal' M
  have hW : W ∈ Matrix.unitaryGroup (Σ a, ι a) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose]
    change blockDiagonal' M * (blockDiagonal' M)ᴴ = 1
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    have hM (a : s) : M a * (M a)ᴴ = 1 := by
      exact Matrix.mem_unitaryGroup_iff.mp (V a).property
    rw [show (fun a ↦ M a * (M a)ᴴ) = 1 by funext a; exact hM a,
      Matrix.blockDiagonal'_one]
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · intro z
    let D : Matrix (Σ a, ι a) (Σ a, ι a) ℂ := diagonal (fun i ↦ z i.1)
    have hcomm : W * D = D * W := by
      ext ⟨a, i⟩ ⟨b, j⟩
      change (W * diagonal (fun k : Σ q, ι q ↦ z k.1)) ⟨a, i⟩ ⟨b, j⟩ =
        (diagonal (fun k : Σ q, ι q ↦ z k.1) * W) ⟨a, i⟩ ⟨b, j⟩
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hab : a = b
      · subst b
        exact mul_comm _ _
      · rw [show W ⟨a, i⟩ ⟨b, j⟩ = 0 from Matrix.blockDiagonal'_apply_ne M i j hab,
          zero_mul, mul_zero]
    change W * D * star W = D
    rw [hcomm, mul_assoc, Matrix.mem_unitaryGroup_iff.mp hW, mul_one]
  · intro a i
    change (W * B * Wᴴ) ⟨a, i⟩ ⟨a, i⟩ = _
    have hcut (j : ι a) :
        (W * B) ⟨a, i⟩ ⟨a, j⟩ = (M a * B.submatrix (Sigma.mk a) (Sigma.mk a)) i j := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma]
      rw [Finset.sum_eq_single a]
      · simp only [W, Matrix.blockDiagonal'_apply_eq, Matrix.submatrix_apply]
      · intro b _ hba
        apply Finset.sum_eq_zero
        intro k _
        simp [W, Matrix.blockDiagonal'_apply_ne M i k hba.symm]
      · simp
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a]
    · simp_rw [hcut]
      simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.mul_apply, Matrix.conjTranspose_apply, W, M, Matrix.blockDiagonal'_apply_eq]
        using hV a i
    · intro b _ hba
      apply Finset.sum_eq_zero
      intro k _
      simp [W, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply_ne M i k hba.symm]
    · simp

/-- A single unitary flattens the diagonal of each spectral compression
and leaves every diagonal matrix indexed by the same spectral labels fixed. -/
theorem exists_unitary_const_diagonal_fibers {n s : Type*} [Fintype n] [DecidableEq n]
    [Finite s] [DecidableEq s] (label : n → s)
    {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      (∀ z : s → ℂ, Unitary.conjStarAlgAut ℂ _ U (diagonal (fun i ↦ z (label i))) =
        diagonal (fun i ↦ z (label i))) ∧
      (∀ i, Unitary.conjStarAlgAut ℂ _ U B i i =
        trace (B.submatrix (Subtype.val : {j // label j = label i} → n)
          Subtype.val) / (Fintype.card {j // label j = label i} : ℂ)) := by
  let _ := Fintype.ofFinite s
  let ι (a : s) := {i // label i = a}
  let e : (Σ a, ι a) ≃ n := Equiv.sigmaFiberEquiv label
  obtain ⟨V, hfix, hV⟩ := exists_unitary_const_diagonal_blocks ι (hB.submatrix e)
  let W : Matrix n n ℂ := V.val.submatrix e.symm e.symm
  have hW : W ∈ Matrix.unitaryGroup n ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose]
    change V.val.submatrix e.symm e.symm * (V.val.submatrix e.symm e.symm)ᴴ = 1
    have hVUnitary : V.val * V.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.property
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      hVUnitary, Matrix.submatrix_one_equiv]
  let U : Matrix.unitaryGroup n ℂ := ⟨W, hW⟩
  have hconj (T : Matrix (Σ a, ι a) (Σ a, ι a) ℂ) :
      Unitary.conjStarAlgAut ℂ _ U (T.submatrix e.symm e.symm) =
        (Unitary.conjStarAlgAut ℂ _ V T).submatrix e.symm e.symm := by
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    change W * T.submatrix e.symm e.symm * Wᴴ = _
    rw [show W = V.val.submatrix e.symm e.symm by rfl,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine ⟨U, ?_, ?_⟩
  · intro z
    have hdiag : (diagonal (fun j : Σ a, ι a ↦ z j.1)).submatrix e.symm e.symm =
        diagonal (fun i : n ↦ z (label i)) := by
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [← hdiag, hconj, hfix]
  · intro i
    have hsub : (B.submatrix e e).submatrix e.symm e.symm = B := by
      ext j k
      simp [Matrix.submatrix_apply]
    have hv := congrArg (fun T : Matrix n n ℂ ↦ T i i) (hconj (B.submatrix e e))
    rw [hsub] at hv
    rw [hv]
    exact hV (label i) ⟨i, rfl⟩

end RefinedBMV.Tracial
