import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.CoprimeValuation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

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
