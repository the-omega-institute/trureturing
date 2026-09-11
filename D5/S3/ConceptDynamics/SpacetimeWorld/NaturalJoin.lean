/- GID: D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximal dependent natural joins with explicit extra joint constraints. -/

import D5.S3.ConceptDynamics.SpacetimeWorld.WorldDomains

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeWorld.NaturalJoin

open WorldDomains

variable {S : Type*} {V : S → Type*}

abbrev LocalValuation (V : S → Type*) (names : Set S) := Valuation (fun s : names => V s.val)

/-- Both maps are actual dependent restrictions from valuations on the union. -/
def naturalJoin (left right : Set S)
    (Γ₁ : Set (LocalValuation V left)) (Γ₂ : Set (LocalValuation V right)) :
    Set (LocalValuation V (left ∪ right)) :=
  Set.domRestrict₂ Set.subset_union_left ⁻¹' Γ₁ ∩
    Set.domRestrict₂ Set.subset_union_right ⁻¹' Γ₂

/-- Every domain satisfying both restriction constraints is contained in the join. -/
theorem naturalJoin_greatest (left right : Set S)
    (Γ₁ : Set (LocalValuation V left)) (Γ₂ : Set (LocalValuation V right)) :
    IsGreatest {Δ : Set (LocalValuation V (left ∪ right)) |
      Set.MapsTo (Set.domRestrict₂ Set.subset_union_left) Δ Γ₁ ∧
        Set.MapsTo (Set.domRestrict₂ Set.subset_union_right) Δ Γ₂}
      (naturalJoin left right Γ₁ Γ₂) := by
  refine ⟨⟨fun _ hv => hv.1, fun _ hv => hv.2⟩, ?_⟩
  intro Δ hΔ v hv
  exact ⟨hΔ.1 hv, hΔ.2 hv⟩

def constrainedJoin (left right : Set S)
    (Γ₁ : Set (LocalValuation V left)) (Γ₂ : Set (LocalValuation V right))
    (extra : Set (LocalValuation V (left ∪ right))) : Set (LocalValuation V (left ∪ right)) :=
  naturalJoin left right Γ₁ Γ₂ ∩ extra

/-- Extra constraints are retained in the greatest admissible domain, not discarded. -/
theorem constrainedJoin_greatest (left right : Set S)
    (Γ₁ : Set (LocalValuation V left)) (Γ₂ : Set (LocalValuation V right))
    (extra : Set (LocalValuation V (left ∪ right))) :
    IsGreatest {Δ : Set (LocalValuation V (left ∪ right)) |
      (Set.MapsTo (Set.domRestrict₂ Set.subset_union_left) Δ Γ₁ ∧
        Set.MapsTo (Set.domRestrict₂ Set.subset_union_right) Δ Γ₂) ∧ Δ ⊆ extra}
      (constrainedJoin left right Γ₁ Γ₂ extra) := by
  refine ⟨⟨⟨fun _ hv => hv.1.1, fun _ hv => hv.1.2⟩, fun _ hv => hv.2⟩, ?_⟩
  intro Δ hΔ v hv
  exact ⟨(naturalJoin_greatest left right Γ₁ Γ₂).2 hΔ.1 hv, hΔ.2 hv⟩

/-- Any admissible subdomain can be realized by a genuine extra joint constraint. -/
theorem constrainedJoin_realizes (left right : Set S)
    (Γ₁ : Set (LocalValuation V left)) (Γ₂ : Set (LocalValuation V right))
    (Δ : Set (LocalValuation V (left ∪ right)))
    (h₁ : Set.MapsTo (Set.domRestrict₂ Set.subset_union_left) Δ Γ₁)
    (h₂ : Set.MapsTo (Set.domRestrict₂ Set.subset_union_right) Δ Γ₂) :
    constrainedJoin left right Γ₁ Γ₂ Δ = Δ :=
  Set.inter_eq_right.mpr ((naturalJoin_greatest left right Γ₁ Γ₂).2 ⟨h₁, h₂⟩)

end D5.S3.ConceptDynamics.SpacetimeWorld.NaturalJoin
