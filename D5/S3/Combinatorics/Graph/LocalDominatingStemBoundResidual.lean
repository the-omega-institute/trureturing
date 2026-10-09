/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: []
   utility: none
   digest: Residual graph families transport to the original vertices preserving counts and means. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundStructure
import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
import Mathlib.Data.Finset.Image

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundResidual

open Finset DominatingSetAverage LocalDominatingStemBoundStructure
  LocalDominatingStemBoundReplication

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Embed finite sets of residual vertices into finite sets of the original vertices. -/
noncomputable def residualEmbedding (G : SimpleGraph V) (v : V) :
    Finset {x // x ∈ remaining G v} ↪ Finset V := by
  classical
  exact ⟨fun S => S.map (Function.Embedding.subtype _), fun _ _ h => Finset.map_injective _ h⟩

/-- Full dominating sets of the residual graph, on the original vertex labels. -/
noncomputable def residualDomSets (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact (domSets (residualGraph G v)).map (residualEmbedding G v)

theorem residualDomSets_card (G : SimpleGraph V) (v : V) :
    (residualDomSets G v).card = (domSets (residualGraph G v)).card := by
  classical
  exact card_map _

theorem residualDomSets_average (G : SimpleGraph V) (v : V) :
    familyAverage (residualDomSets G v) = avd (residualGraph G v) := by
  classical
  unfold familyAverage avd residualDomSets
  rw [card_map, sum_map]
  congr 1
  apply sum_congr rfl
  intro S _
  change (((S.map (Function.Embedding.subtype _)).card : ℚ)) = (S.card : ℚ)
  simp

@[simp] theorem mem_residualDomSets {G : SimpleGraph V} {v : V} {T : Finset V} :
    T ∈ residualDomSets G v ↔ T ⊆ remaining G v ∧
      ∀ x ∈ remaining G v, x ∈ T ∨ ∃ y ∈ T, G.Adj x y := by
  classical
  constructor
  · intro hT
    obtain ⟨S, hS, rfl⟩ := mem_map.mp hT
    change (S.map (Function.Embedding.subtype _)) ⊆ remaining G v ∧ _
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := mem_map.mp hx
      exact y.property
    · intro x hx
      rcases mem_domSets.mp hS ⟨x,hx⟩ with hs | ⟨y, hy, hxy⟩
      · exact Or.inl (mem_map.mpr ⟨⟨x,hx⟩, hs, rfl⟩)
      · exact Or.inr ⟨y.val, mem_map.mpr ⟨y,hy,rfl⟩, hxy⟩
  · rintro ⟨hsub,hdom⟩
    refine mem_map.mpr ⟨T.subtype (fun x => x ∈ remaining G v), ?_, ?_⟩
    · apply mem_domSets.mpr
      intro x
      rcases hdom x.val x.property with hx | ⟨y,hy,hxy⟩
      · exact Or.inl (by simpa using hx)
      · exact Or.inr ⟨⟨y,hsub hy⟩, by simpa using hy, hxy⟩
    · change (T.subtype (fun x => x ∈ remaining G v)).map (Function.Embedding.subtype _) = T
      exact subtype_map_of_mem hsub

theorem residualDomSets_subset (G : SimpleGraph V) (v : V) :
    residualDomSets G v ⊆ partialDomSets G v := by
  intro T hT
  obtain ⟨hsub,hdom⟩ := mem_residualDomSets.mp hT
  exact mem_partialDomSets.mpr ⟨hsub, fun x hx _ => hdom x hx⟩

theorem residualDomSets_card_pos (G : SimpleGraph V) (v : V) :
    0 < (residualDomSets G v).card := by
  classical
  rw [residualDomSets_card]
  exact domSets_card_pos _

theorem residual_equal_of_card_equal (G : SimpleGraph V) (v : V)
    (hcard : (partialDomSets G v).card = (residualDomSets G v).card) :
    partialDomSets G v = residualDomSets G v :=
  (eq_of_subset_of_card_le (residualDomSets_subset G v) hcard.le).symm

/-- Neighbours of the removed stem, viewed in the residual graph. -/
noncomputable def residualNeighbors (G : SimpleGraph V) (v : V) :
    Finset {x // x ∈ remaining G v} := by
  classical
  exact univ.filter (fun x => G.Adj v x.val)

@[simp] theorem mem_residualNeighbors {G : SimpleGraph V} {v : V}
    {x : {x // x ∈ remaining G v}} : x ∈ residualNeighbors G v ↔ G.Adj v x.val := by
  classical
  simp [residualNeighbors]

theorem residualPartial_map (G : SimpleGraph V) (v : V) :
    (partialSets (residualGraph G v) (residualNeighbors G v)).map
      (residualEmbedding G v) = partialDomSets G v := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨S,hS,rfl⟩ := mem_map.mp hT
    apply mem_partialDomSets.mpr
    change (S.map (Function.Embedding.subtype _)) ⊆ remaining G v ∧ _
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y,_,rfl⟩ := mem_map.mp hx
      exact y.property
    · intro x hx hvx
      have hU : (⟨x,hx⟩ : {x // x ∈ remaining G v}) ∉ residualNeighbors G v := by
        simpa using hvx
      rcases (mem_partialSets _ _ _).mp hS ⟨x,hx⟩ hU with hs | ⟨y,hy,hxy⟩
      · exact Or.inl (mem_map.mpr ⟨⟨x,hx⟩,hs,rfl⟩)
      · exact Or.inr ⟨y.val,mem_map.mpr ⟨y,hy,rfl⟩,hxy⟩
  · intro hT
    obtain ⟨hsub,hpartial⟩ := mem_partialDomSets.mp hT
    refine mem_map.mpr ⟨T.subtype (fun x => x ∈ remaining G v), ?_, ?_⟩
    · apply (mem_partialSets _ _ _).mpr
      intro x hx
      have hvx : ¬ G.Adj v x.val := by simpa using hx
      rcases hpartial x.val x.property hvx with hxs | ⟨y,hy,hxy⟩
      · exact Or.inl (by simpa using hxs)
      · exact Or.inr ⟨⟨y,hsub hy⟩,by simpa using hy,hxy⟩
    · change (T.subtype (fun x => x ∈ remaining G v)).map
        (Function.Embedding.subtype _) = T
      exact subtype_map_of_mem hsub

theorem residualPartial_card (G : SimpleGraph V) (v : V) :
    (partialSets (residualGraph G v) (residualNeighbors G v)).card =
      (partialDomSets G v).card := by
  classical
  rw [← residualPartial_map, card_map]

theorem residualPartial_average (G : SimpleGraph V) (v : V) :
    familyAverage (partialSets (residualGraph G v) (residualNeighbors G v)) =
      familyAverage (partialDomSets G v) := by
  classical
  rw [← residualPartial_map]
  unfold familyAverage
  rw [card_map,sum_map]
  congr 1
  apply sum_congr rfl
  intro S _
  change (S.card : ℚ) = (((S.map (Function.Embedding.subtype _)).card : ℚ))
  simp

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundResidual
