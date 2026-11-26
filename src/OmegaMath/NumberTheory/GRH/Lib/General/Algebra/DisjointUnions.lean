import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.CechDescent
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

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
