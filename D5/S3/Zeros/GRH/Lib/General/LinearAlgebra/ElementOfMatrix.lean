/- GID: D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ElementOfMatrix
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/LinearAlgebra/ElementOfMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.LinearAlgebra.ElementOfMatrix. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/ElementOfMatrix.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Unitary.SpaceGram
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: The element of an adelic unitary group with a given isometric matrix. -/


variable {E} [Field E] [NumberField E] [NumberField.IsCMField E] {n} [Fintype n] {s : n → _}

/-- The element of the adelic unitary group of signs s given by an adelic matrix m with m*εm =
ε, ε the standard form. -/
noncomputable def G.ofMat m h := (toUnitary.symm (U.of isUnit_stdForm m h) : G E s)

@[simp] lemma G.mat_ofMat m h : (ofMat m h : G E s).mat = m := rfl
