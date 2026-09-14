/- GID: D5/S3/ConceptDynamics/ZfcFiniteCollections/OrderDense
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteCollections/OrderDense
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.PFilter]
   utility: none
   digest: Countable dense families admit a generic preorder filter through any prescribed element. -/
module

public import Mathlib.Order.PFilter
public import Mathlib.Data.Set.Countable

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Order/Dense.lean: bundled density and genericity API.
   Modifications: canonical header, reduced imports, and source-command excerpts.
   Generic-filter existence applies Mathlib.Order.Ideal's idealOfCofinals and its
   membership specifications on the dual order, indexed by the countable family.
   The Foundation sequence, choice and descending-chain construction is omitted.
   Attribution: FormalizedFormalLogic contributors; Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Mathlib contributors supply the ideal construction under Apache-2.0.
   The retained bundled API translates downward density to dual cofinality. -/

@[expose] public section

namespace Order

variable {α : Type*} [Preorder α]

def IsDense (s : Set α) : Prop := ∀ p, ∃ q ≤ p, q ∈ s

variable (α)

@[ext] structure DenseSet where
  set : Set α
  is_dense : IsDense set

variable {α}

namespace DenseSet

instance : SetLike (DenseSet α) α where
  coe s := s.set
  coe_injective s t e := by ext; simp_all

end DenseSet

namespace PFilter

class IsGeneric (F : PFilter α) (𝓓 : Set (DenseSet α)) where
  isGeneric : ∀ d ∈ 𝓓, ∃ a ∈ F, a ∈ d

theorem exists_genericFilter_of_countable
    (𝓓 : Set (DenseSet α)) (ctb : Set.Countable 𝓓) (a : α) :
    ∃ G : PFilter α, G.IsGeneric 𝓓 ∧ a ∈ G := by
  let : Encodable 𝓓 := ctb.toEncodable
  let D : 𝓓 → Cofinal (OrderDual α) := fun d ↦
    ⟨d.val.set, fun p ↦ by
      obtain ⟨q, hqp, hq⟩ := d.val.is_dense p
      exact ⟨q, hq, hqp⟩⟩
  refine ⟨⟨idealOfCofinals (OrderDual.toDual a) D⟩, ⟨?_⟩,
    mem_idealOfCofinals (OrderDual.toDual a) D⟩
  intro d hd
  obtain ⟨q, hqd, hqG⟩ :=
    cofinal_meets_idealOfCofinals (OrderDual.toDual a) D ⟨d, hd⟩
  exact ⟨q, hqG, hqd⟩

end PFilter

end Order

end
