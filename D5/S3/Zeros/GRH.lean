/- GID: D5/S3/Zeros/GRH
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Main. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Main.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Main
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false
-- The proof is Levent Alpöge's, with Claude.

theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := New.grh

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := New.zeros_on_line New.grh

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
