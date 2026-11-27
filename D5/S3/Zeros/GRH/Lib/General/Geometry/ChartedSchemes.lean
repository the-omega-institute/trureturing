/- GID: D5/S3/Zeros/GRH/Lib/General/Geometry/ChartedSchemes
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Geometry/ChartedSchemes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Geometry.ChartedSchemes. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Geometry/ChartedSchemes.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.ProperAtlas
import D5.S3.Zeros.GRH.Lib.PadicComparison.Descent.AlmostAcyclic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Faltings' toric towers and their Koszul complexes (known result; see
Lib.PadicComparison.ToricTower.CrystallineLines).

This file: Bijectivity of a comparison defines a closed class; charted schemes (`IsCharted`). -/

open CategoryTheory Functor AlgebraicGeometry


variable {C C' D} [Category C] [Category C'] [Category D] {F F'} (c : Comparison F F') {ψ : C ⥤ D}
  {ψ' : C' ⥤ D} (η : ψ' ⟶ c.φ ⋙ ψ)

/-- Given a comparison c from F to F' along φ, functors ψ, ψ' to D and η: ψ' → ψ∘φ, the property
of N on D that c along N(η) is bijective in every degree holds for 0 and passes along short
exact sequences (`IsClosedClass`). -/
lemma Comparison.isClosedClass : IsClosedClass fun N ↦ c.IsBijective (N :=
  ψ ⋙ N) (whiskerRight η N) := (c.devissage ((whiskeringLeft ..) ψ) ((whiskeringLeft ..).map η)).2

/-- For η: ψ' → ψ∘φ and a set-valued functor P on D, the comparison H^n(P∘ψ, F) → H^n(P∘ψ', F')
induced by c and η is bijective for every n. -/
abbrev Comparison.IsBijectiveOn P := c.IsBijective (freeAbMap (Y := ψ ⋙ P) (whiskerRight η P))

/-- Y is charted over the R-algebra k: some subfunctor of the functor of points of Y on
k-algebras satisfies `IsCharting`. -/
class IsCharted {R} (Y : Over (Spec R)) k [CommRing k] [Algebra R k] where
  exists_isCharting : ∃ V, @IsCharting k _ (algPointsOf k R Y) V
