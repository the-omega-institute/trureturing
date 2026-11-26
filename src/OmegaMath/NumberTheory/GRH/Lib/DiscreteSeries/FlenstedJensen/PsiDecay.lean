import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.BlockDiagonalDet
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Decay of the coefficient like (2/‖g‖)^h, constant free of the parameter. -/


open Matrix MeasureTheory Finset Real ComplexOrder Norms.L2Operator PosDef U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) {c : ℕ} (hc : c ≤ h) (g : USign ε)

lemma weightMinors_pos {z} (hz :
  PosDef z) w : 0 < @weightMinors n _ w z := by apply finprod_induction <;>
  simp_all [principalMinor, toSquareBlockProp, toBlock, det_pos, hz.submatrix, apply_ite]

include hg hc

/-- For l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε): |ψ_λ(g)|²·|det a_g|^c ≤ 1, where
a_g is the block diagonal part of g. -/
lemma norm_dsCoeff_sq_mul_det_pow_le_one : ‖l.dsCoeff g‖ ^ 2 * ‖(blockDiagPart ε g).det‖ ^
  c ≤ 1 := by
  have d (g : USign ε) (p :
    g.1.1.PosDef) : ‖(blockDiagPart ε g).det‖ ^ c ≤ ‖weightMinors (-paramAddRho l) g‖ ^ 2 := by
    let v i := paramAddRho l i + ite True ↑c 0
    have q : (blockDiagPart ε g).PosDef :=
      p.1 ▸ by simp [blockDiagPart_eq, ← inv_mat, p, PosDef.add, PosDef.smul]
    suffices ‖weightMinors v (blockDiagPart ε g)‖ ≤ ‖_ * weightMinors (paramAddRho l) g *
      weightMinors v g⁻¹‖ by simpa [v, principalMinor_of_forall, ↓weightMinors_add_ite,
      weightMinors_neg, weightMinors_unitary_inv, q.isAccretive, field]
    obtain ⟨⟨⟩, ⟨B⟩⟩ := hg.mono hc, Finite.exists_le (|paramAddRho l| ⊔ |v|)
    norm_cast at *
    simp_all [abs_le, jacobi_complementary_minor, weightMinors_eq_det_zpow_mul_prod _ (-B) B,
      mul_assoc, ← prod_mul_distrib]
    gcongr
    grw [← fischer_inequality p.posSemidef (e := fun _ ↦ not_not), principalMinor_compl]; simp
    apply (fischer_inequality q.posSemidef ..).trans_eq
      congr(_ * ‖$(ext fun _ _ ↦ ite_eq_left _).det‖)
    repeat grind [paramAddRho]
  obtain ⟨I, k, z, ⟨p⟩⟩ := Integrable.of_integral_ne_zero (kTypeNormSq_pos l.lowestKType).ne',
    exists_polar g
  simp [*, by simpa using dsCoeff_polar hg k 1 p, ← maxCompactU.coe_inv]
  grw [norm_integral_le_of_norm_le (((I.comp_mul_left k).add I).div_const (2 * √(‖(blockDiagPart ε
    g).det‖ ^ c))) (.of_forall fun x ↦ ?_), integral_div, integral_add' integrable_of_compactSpace,
    ← integral_mul_left_eq_self _ k⁻¹, ← div_div] <;> simp [field, *, div_self_le_one]
  grw [← mul_rotate, two_mul_le_add_sq, sqrt_le_iff.2]; swap; simpa [← mem_maxCompactU] using
      d (x⁻¹ *
    z * x) (by simp [maxCompactU.coe_inv, p.conjTranspose_mul_mul_same, mulVec_injective_of_isUnit])
  repeat simp [← mem_maxCompactU]

/-- For a parameter l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε): |ψ_λ(g)| ≤
(2/‖g‖)^c, with the operator norm. -/
lemma norm_dsCoeff_le_pow [Nonempty n] : ‖l.dsCoeff g‖ ≤ (2 / ‖g.1.1‖) ^ c := by grw [← sq_le_sq₀,
          pow_right_comm, ← inv_div, inv_pow, sq_le_norm_det_blockDiagPart] <;> simp [field,
  norm_dsCoeff_sq_mul_det_pow_le_one hg hc]
