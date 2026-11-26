/- GID: D5/S3/Combinatorics/Graph/StarForming/Semantics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Semantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Equivalence of local set witnesses and canonical finite star predicates. -/

import D5.S3.Combinatorics.Graph.StarForming.Foundations.LocalFormation
import D5.S3.Combinatorics.Graph.StarForming.Foundations.Invariants

/-!
The set-valued local predicate and canonical non-induced-star predicate
describe the same selections on any finite simple graph. Inclusion-minimality
is transported in both directions, including the empty vertex type.
-/

namespace D5.S3.Combinatorics.Graph.StarForming

open StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local neighbor-count and existential-witness presentations agree. -/
theorem forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Amplification.Forms G (↑S : Set V) ↔ IsStarForming G 2 S := by
  rw [starForming_two_iff]
  constructor
  · intro h x hx
    rcases h x hx with ⟨a, ha, b, hb, hab, hxa, hxb⟩ | ⟨c, hc, hxc, l, hl, hcl⟩
    · exact Or.inl (Nat.succ_le_iff.mpr (Finset.one_lt_card.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hxa⟩,
          b, Finset.mem_filter.mpr ⟨hb, hxb⟩, hab⟩))
    · exact Or.inr ⟨c, hc, hxc, Finset.one_le_card.mpr
        ⟨l, Finset.mem_filter.mpr ⟨hl, hcl⟩⟩⟩
  · intro h x hx
    rcases h x hx with hd | ⟨c, hc, hxc, hd⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
        1 < (S.filter (G.Adj x)).card)
      exact Or.inl ⟨a, (Finset.mem_filter.mp ha).1,
        b, (Finset.mem_filter.mp hb).1, hab,
        (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
    · obtain ⟨l, hl⟩ := Finset.one_le_card.mp hd
      exact Or.inr ⟨c, hc, hxc, l,
        (Finset.mem_filter.mp hl).1, (Finset.mem_filter.mp hl).2⟩

/-- Set minimality ranges over precisely the same finite subsets. -/
theorem minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Amplification.Minimal G (↑S : Set V) ↔ IsMinimalStarForming G 2 S := by
  classical
  constructor
  · rintro ⟨hf, hm⟩
    refine ⟨(forms_iff G S).mp hf, ?_⟩
    intro T hT hfT
    exact hm (↑T) (Finset.coe_ssubset.mpr hT) ((forms_iff G T).mpr hfT)
  · rintro ⟨hf, hm⟩
    refine ⟨(forms_iff G S).mpr hf, ?_⟩
    intro T hT hfT
    let U : Finset V := Finset.univ.filter (· ∈ T)
    have hU : (↑U : Set V) = T := by ext x; simp [U]
    have hproper : U ⊂ S := Finset.coe_ssubset.mp (hU ▸ hT)
    exact hm U hproper ((forms_iff G U).mp (hU ▸ hfT))

end D5.S3.Combinatorics.Graph.StarForming
