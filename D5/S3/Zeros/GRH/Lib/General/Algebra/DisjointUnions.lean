/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/DisjointUnions
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/DisjointUnions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.DisjointUnions. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/DisjointUnions.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.CechDescent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore). -/

open CategoryTheory Abelian.Ext Function Comparison LongExactSeq ShortComplex

/-- Cohomology turns disjoint unions into products: the map H^n(∐ X_i, F) → ∏ H^n(X_i, F) given
by pull-back along the inclusions is bijective. -/
lemma H.sigma_bijective {C} [Category C] {ι} X F n :
    Bijective fun x i ↦ map F (freeAb.map (@sigma.ι C _ ι X i)) n x := by
  induction n generalizing F
  have e Y := (homEquiv₀.trans (freeAb.homEquiv Y F)).symm.bijective
  exact (bijective_iff_of_comm_sq (by simp +instances [funext_iff, Adjunction.homEquiv, map,
    freeAb]) (e _) (.piMap (e ∘' X))).1 (Equiv.mk (swap (sigma.ι X · ≫ ·)) sigma.desc).bijective
  simp_all [← id_pull]
  apply Hom.bijective_succ_family fun _ ↦ pull_hom_covariant (φ := 𝟭 C) ⟨exact_cokernel (Injective.ι
    F)⟩ ⟨exact_cokernel _⟩ (𝟙 _) _ <;> solve_by_elim [(exact_delta_f ..).1, eq_zero_of_injective]
