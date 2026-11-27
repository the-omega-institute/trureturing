/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/SumOverUnits
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/SumOverUnits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.SumOverUnits. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/SumOverUnits.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.ClassNumberBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Sum over Z/N, N prime, splits as zero term plus sum over units. -/

lemma sum_eq_add_sum_units {N} [Fact N.Prime] {V} [AddCommMonoid V] (f : ZMod N → V) : ∑ c, f c =
  f 0 +
  ∑ c : _ˣ, f c.1 := by simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
