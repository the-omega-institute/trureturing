/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/HeckePolyEval
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/HeckePolyEval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.HeckePolyEval. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/HeckePolyEval.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Unramified.SphericalHecke
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up used by: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular
forms.

This file: Two normalisations of the Hecke polynomial are reciprocal to each other. -/

lemma eval_heckePoly {E n} [Field E] [NumberField E] [Fintype n] (w : FinPlace E) t {x} (h :
  x ≠ 0) : (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t
  x⁻¹ := by erw [Polynomial.eval_finsetSum, Finset.mul_sum]; congr!; simp_all [pow_sub₀]; ring
