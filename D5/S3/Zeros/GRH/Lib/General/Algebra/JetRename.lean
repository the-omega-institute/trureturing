/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/JetRename
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/JetRename
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.JetRename. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/JetRename.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.JetChainRule
import D5.S3.Zeros.GRH.Lib.Weil.Fock.EntireTheta
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: The Fischer pairing is preserved by an injective renaming of the variables. -/

/-- The jet pairing P(∂)F(0) of a polynomial P with a power series F over a commutative ring is
unchanged when both are renamed along an injective map of variables. -/
lemma jet_rename {σ τ R} (e : σ ↪ τ) [CommRing R] {P Q} (h : .rename e P = Q) F :
    jet R Q (F.rename e) = jet R P F := h ▸ P.induction_on' (by
  simp [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain, Finsupp.prod]) (by aesop)
