import GRH.Lib.DiscreteSeries.FlenstedJensen.PsiBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: |det| of the block diagonal part of g in U(p,q) is at least (‖g‖/2)². -/


open Matrix Norms.L2Operator MatrixOrder CStarAlgebra Finset Real Unitary Complex U CStarRing Sgn
variable {n} [Fintype.{0} n] {ε} (σ) (g : @USign n _ ε)

lemma norm_det_blockDiagPart : ‖(blockDiagPart ε g).det‖ = ‖principalMinor g (ε · =
  σ)‖ ^ 2 := by rw [twoBlockTriangular_det₀ _ (ε · =
  σ), (_ : _ * _ = principalMinor g (ε · = σ) * principalMinor g (ε · ≠ σ)),
  principalMinor_compl] <;> congr 2 <;> aesop (add simp [blockDiagPart, toSquareBlockProp, sq])

@[simp] lemma U.principalMinor_sign_ne_zero : principalMinor g (ε · = σ) ≠ 0 :=
  (by simpa [·] using norm_det_blockDiagPart σ g)

lemma sq_le_norm_det_blockDiagPart [Nonempty n] :
  (‖g.1.1‖ / 2) ^ 2 ≤ ‖(blockDiagPart ε g).det‖ := by
  have ⟨k, z, hz, _⟩ := exists_polar g
  have := (cosh_log <| hz.eigenvalues_pos ·)
  simp_all [-prod_mul_distrib, ← mem_maxCompactU, star, show blockDiagPart ε z =
    hz.1.cfc fun x ↦ 2⁻¹ * (x + x⁻¹) by
    rw [← hz.1.cfc_eq, cfc_const_mul .., cfc_add .., cfc_id' .., cfc_inv_id _]
    simp [blockDiagPart_eq, inv_mat, hz.1.eq, ← ext_iff], norm_mem_unitary_mul, mem_iff,
    ← maxCompactU.coe_inv, IsHermitian.cfc, -conjStarAlgAut_apply, -ofReal_mul]
  have ⟨⟨i, _⟩, j, _⟩ := hz.1.spectrum_real_eq_range_eigenvalues ▸ And.intro
    (norm_mem_spectrum_of_nonneg z.1.1) (spectrum.inv₀_mem (norm_inv z ▸
    norm_mem_spectrum_of_nonneg _ (CFC.inv_nonneg_of_nonneg _)))
  grw [← subset_univ {i, j}, (by simp : ∀ a, ‖a‖ ≤ ‖a‖ + ‖a‖⁻¹)] <;> grind [one_le_cosh, sq]
