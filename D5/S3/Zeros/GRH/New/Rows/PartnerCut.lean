/- GID: D5/S3/Zeros/GRH/New/Rows/PartnerCut
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/PartnerCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.PartnerCut. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/PartnerCut.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.BlockMatrices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

Part of: Integral comparison forms seeing the twist through one number (see
New.Rows.ComparisonForms).

This file: Stabiliser subgroup, data on columns; on that subgroup the datum is a product. -/

open Matrix

variable {R S r a c N : Type} [CommRing R] [CommRing S] [Fintype r] [Fintype N] (χ : MulChar R ℂ)
  (φ : R →+* S) (w : Matrix c N S) (e : r ↪ N)

/-- The columns of the square matrix z outside the image of e are those of the identity matrix. -/
abbrev FixesColsOff z :=
  z * (1 - inclMatrix R e * (inclMatrix R e)ᵀ) = 1 - inclMatrix R e * (inclMatrix R e)ᵀ

/-- The subgroup of A in GL_N(R) whose columns outside the image of e are those of 1 and with
w·φ(A) = w. -/
noncomputable def rowStabilizer : Subgroup (GL N R) := .copy (s := {A | FixesColsOff e A.1 ∧
  w * A.1.map φ = w}) (MulAction.stabilizer .. ⊓ ((MulAction.stabilizer _ w.row).comap
  Units.opEquiv.symm.toMonoidHom).unop.comap (GeneralLinearGroup.map φ)) rfl

/-- The function of an N×r matrix σ equal to χ(det of the rows e of σ) if w·φ(σ) = w·inc(e), and
0 otherwise. -/
noncomputable def columnDatum σ :=
  ite (w * map σ φ = w * inclMatrix S e) (χ (submatrix σ e id).det) 0

/-- Let F be invariant under left multiplication by H = `rowStabilizer`, z square. Then
`columnDatum` at the columns e of z, times F(y) if `FixesColsOff` e z and 0 if not, equals
χ(det z)F(z⁻¹y) for z ∈ H and 0 otherwise. -/
lemma columnDatum_mul_ite_eq {F : _ → ℂ} (hF : ∀ A ∈ rowStabilizer φ w e, ∀ y, F (A.1 * y) = F y)
  (y : Matrix N a R) z : columnDatum χ φ w e (z.submatrix id e) * ite (FixesColsOff e z) (F y) 0 =
  ite (∃ Z ∈ rowStabilizer φ w e, Z = z) (χ z.det * F (z⁻¹ * y)) 0 := by
  have K (c : FixesColsOff e z) : columnDatum χ φ w e (z.submatrix id e) = ite (w * z.map φ =
    w) (χ z.det) 0 := (by grind [Matrix.mul_assoc, mul_sub, sub_mul] : z = 1 + (z - 1) * inclMatrix
    R e * (inclMatrix R e)ᵀ) ▸ by simp [columnDatum, ← mul_inclMatrix, ← inclMatrix_transpose_mul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc _ _ᵀ, map_inclMatrix,
    det_one_add_mul_comm _ᵀ, Matrix.map_add, transpose_map, ← w.mul_assoc,
    (mul_left_injective_of_inv _ _ (inclMatrix_transpose_mul_self e)).eq_iff' (Matrix.zero_mul _)]
  obtain ⟨z, rfl⟩ | _ := em (IsUnit z) <;> simp_all [χ.map_nonunit, isUnit_iff_isUnit_det,
    Units.val_inj, rowStabilizer] <;> grind [mul_inv_cancel_left_of_invertible]
