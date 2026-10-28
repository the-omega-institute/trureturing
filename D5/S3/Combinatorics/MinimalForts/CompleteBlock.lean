/- GID: D5/S3/Combinatorics/MinimalForts/CompleteBlock
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/CompleteBlock
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: All minimal forts of a complete graph are pairs, with their exact binomial count. -/

import D5.S3.Combinatorics.MinimalForts.UniversalRoot

/-! The complete-graph block retains every vertex subset, rather than a selected fort class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.CompleteBlock

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.MinimalForts.UniversalRoot

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

private theorem complete_no_isolated (v : V) : ∃ w, (⊤ : SimpleGraph V).Adj v w := by
  obtain ⟨w, hw⟩ := exists_ne v
  exact ⟨w, by simpa using hw.symm⟩

private theorem isFort_complete_iff (S : Finset V) :
    IsFort (⊤ : SimpleGraph V) S ↔ 2 ≤ S.card := by
  constructor
  · intro hf
    have hn := Finset.card_pos.mpr hf.1
    have hne := fort_card_ne_one (⊤ : SimpleGraph V) complete_no_isolated hf
    omega
  · intro hc
    refine ⟨Finset.card_pos.mp (by omega), ?_⟩
    intro v hv
    have he : finiteNeighbors (⊤ : SimpleGraph V) v ∩ S = S := by
      ext w
      simp only [Finset.mem_inter, finiteNeighbors, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.top_adj]
      exact and_iff_right_of_imp (fun hw => fun h => hv (h ▸ hw))
    rw [he]
    omega

private theorem minimalFort_complete_iff (S : Finset V) :
    MinimalFort (⊤ : SimpleGraph V) S ↔ S.card = 2 := by
  constructor
  · rintro ⟨hf, hm⟩
    have hc := (isFort_complete_iff S).mp hf
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hp : ({a, b} : Finset V).card = 2 := by simp [hab]
    have hsub : ({a, b} : Finset V) ⊆ S := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> assumption
    have he := hm {a, b} hsub ((isFort_complete_iff _).mpr (by omega))
    exact le_antisymm (hp ▸ Finset.card_le_card he) hc
  · intro hc
    refine ⟨(isFort_complete_iff S).mpr (by omega), ?_⟩
    intro T hTS hT
    have ht := (isFort_complete_iff T).mp hT
    have he : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
    exact he ▸ Finset.Subset.refl S

/-- The full minimal-fort family consists of all pairs, and has the binomial count. -/
theorem complete_block :
    (∀ S : Finset V, MinimalFort (⊤ : SimpleGraph V) S ↔ S.card = 2) ∧
      (minimalForts (⊤ : SimpleGraph V)).card = (Fintype.card V).choose 2 := by
  refine ⟨minimalFort_complete_iff, ?_⟩
  have he : minimalForts (⊤ : SimpleGraph V) =
      (Finset.univ : Finset V).powersetCard 2 := by
    ext S
    simp [minimalForts, minimalFort_complete_iff]
  rw [he, Finset.card_powersetCard, Finset.card_univ]

end D5.S3.Combinatorics.MinimalForts.CompleteBlock
