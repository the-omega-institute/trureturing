/- GID: D5/S3/Zeros/GRH/Lib/General/NumberTheory/Embeddings
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/NumberTheory/Embeddings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.NumberTheory.Embeddings. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/NumberTheory/Embeddings.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.CoprimeValuation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Complex embeddings of a totally complex field come in conjugate pairs. -/

open NumberField Polynomial ComplexEmbedding InfinitePlace Finset IsTotallyComplex


variable {E} [Field E] [IsTotallyComplex E]

@[simp, grind] lemma conjugate_ne_self σ : @conjugate E _ σ ≠ σ := complexEmbedding_not_isReal _

@[to_additive] lemma prod_embeddings_eq_prod_pairs [NumberField E]
  [PlaceEmbedding E] {M} [CommMonoid M] (F : (E →+* ℂ) → M) : ∏ σ, F σ = ∏ v, F (Φ v) * F (conjugate
  (Φ v)) := prod_fiberwise _ mk F ▸ by congr!; apply prod_eq_mul <;> grind [mk_Φ, mk_eq_iff]

omit [IsTotallyComplex E] in
lemma roots_map_conjugate (P : E[X]) σ : (P.map (conjugate σ)).roots = (P.map σ).roots.map star :=
  (P.map_map ..).rec ((IsAlgClosed.splits _).roots_map _)
