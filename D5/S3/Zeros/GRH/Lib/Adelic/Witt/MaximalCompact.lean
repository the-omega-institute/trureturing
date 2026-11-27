/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Witt/MaximalCompact
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Witt/MaximalCompact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Witt.MaximalCompact. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Witt/MaximalCompact.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Witt.SpaceOperations
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ExpSurjective
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of group theory (textbook or folklore).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Block embedding of U(Y) into U(Y ⊕ Y'). Maximal compact subgroup of the adelic unitary
group and its compactness. -/

/-- The block embedding a ↦ diag(a, 1) of U(diag ε) into the unitary group of the concatenated
signs (ε, η). -/
@[simps! apply_coe_val] noncomputable def U.inl {n m} [Fintype n]
  [Fintype m] (ε : n → _) (η : m → _) := (sum (signMatrix_sum ε η)).comp (.inl ..)

variable (E) {n} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] (s : n → ℤˣ)

/-- The subgroup K_∞K₀ of G: elements that are unitary matrices at each infinite place and lie
in GL_n(Ô) at the finite places. -/
noncomputable def maxCompact : Subgroup (G E s) := .prod (.pi .univ fun _ ↦ maxCompactU s) (Kf ..)

variable {E s}

lemma isCompact_maxCompact : IsCompact (maxCompact E s : Set (G E s)) := (isCompact_univ_pi fun _ ↦
  isCompact_iff_compactSpace.2 ⟨@isCompact_univ (maxCompactU s) _ _⟩).prod isCompact_Kf
