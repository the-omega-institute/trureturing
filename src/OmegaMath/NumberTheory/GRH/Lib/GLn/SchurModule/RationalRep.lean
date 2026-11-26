import OmegaMath.NumberTheory.GRH.Lib.GLn.SchurModule.SchurMatrix
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Rational representation of a product of GL_n on Weyl's lattice, twisted by
determinants. -/

/-- The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ. -/
noncomputable def weylRep {Φ R} [CommRing R] [Fintype Φ] {n : Φ → _}
    [∀ τ, Fintype (n τ)] κ (e : Φ → ℤ) := MonoidHom.mk ⟨fun g : ∀ τ, GL (n τ) R ↦
  (∏ τ, (g τ).det ^ e τ) • schur κ (g · |>.1), by simp⟩ (by simp [mul_zpow, smul_mul_smul])
