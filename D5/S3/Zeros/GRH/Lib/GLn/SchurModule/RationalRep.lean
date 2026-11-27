/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/RationalRep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/RationalRep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.RationalRep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/RationalRep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.SchurMatrix
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Rational representation of a product of GL_n on Weyl's lattice, twisted by
determinants. -/

/-- The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ. -/
noncomputable def weylRep {Φ R} [CommRing R] [Fintype Φ] {n : Φ → _}
    [∀ τ, Fintype (n τ)] κ (e : Φ → ℤ) := MonoidHom.mk ⟨fun g : ∀ τ, GL (n τ) R ↦
  (∏ τ, (g τ).det ^ e τ) • schur κ (g · |>.1), by simp⟩ (by simp [mul_zpow, smul_mul_smul])
