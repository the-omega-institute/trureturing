/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurContinuous
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurContinuous
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.SchurContinuous. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/SchurContinuous.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.Branching.Branching
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Continuity of the Schur matrix in its argument. -/

/-- Over a topological commutative ring R, the map sending a tuple g of square matrices to its
Schur matrix S_κ(g) is continuous. -/
@[fun_prop] lemma continuous_schur {Φ n κ R} [Fintype Φ] [∀ τ, Fintype (n τ)] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Continuous (@schur Φ R _ _ n n _ _ κ) :=
  .congr (by simp [Matrix.map, MvPolynomial.eval_eq]; fun_prop) fun g ↦
  funext (PolyRep.genericMatrixAt_map_evalMat g) ▸ (schur_map .refl ..).symm
