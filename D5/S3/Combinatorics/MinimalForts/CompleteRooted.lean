/- GID: D5/S3/Combinatorics/MinimalForts/CompleteRooted
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/CompleteRooted
   mirror-E: none(waiver:counting-bijection-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: The full root-containing minimal-fort choices of a complete block are its singletons. -/

import D5.S3.Combinatorics.MinimalForts.CompleteBlock
import D5.S3.Combinatorics.MinimalForts.UniversalRoot

/-! The complete rooted class is characterized before its cardinality is counted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.CompleteRooted

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.MinimalForts.CompleteBlock
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

private theorem no_isolated (v : V) : ∃ w, (⊤ : SimpleGraph V).Adj v w := by
  obtain ⟨w, hw⟩ := exists_ne v
  exact ⟨w, by simpa using hw.symm⟩

private theorem singleton_dom (a : V) :
    (⊤ : SimpleGraph V).IsDominating ({a} : Set V) := by
  intro v
  by_cases h : v = a
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨a, by simp, by simpa using h⟩

/-- This equivalence concerns all actual subsets, including empty subsets. -/
theorem complete_rooted_iff (S : Finset V) :
    MinimalFort (cone (⊤ : SimpleGraph V)) (rootSet S) ↔ S.card = 1 := by
  rw [minimalFort_rootSet_iff (⊤ : SimpleGraph V) no_isolated]
  constructor
  · rintro ⟨hd, hfree⟩
    have hn : S.Nonempty := by
      let v : V := Classical.choice inferInstance
      rcases hd.1 v with hv | ⟨w, hw, _⟩
      · exact ⟨v, hv⟩
      · exact ⟨w, hw⟩
    have hc := Finset.card_pos.mpr hn
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hp : ({a, b} : Finset V).card = 2 := by simp [hab]
    apply hfree {a, b}
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    · exact ((complete_block (V := V)).1 _).mpr hp |>.1
  · intro hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨?_, ?_⟩
    · refine ⟨by simpa using singleton_dom a, ?_⟩
      intro T hT hd v hv
      have hva : v = a := by simpa using hv
      rcases hd a with ha | ⟨w, hw, hadj⟩
      · simpa [hva] using ha
      · have hw' : w = a := by simpa using hT hw
        exact (hadj.ne hw'.symm).elim
    · intro T hT hf
      have hle : T.card ≤ 1 := by simpa using Finset.card_le_card hT
      have hp := Finset.card_pos.mpr hf.1
      exact fort_card_ne_one (⊤ : SimpleGraph V) no_isolated hf (by omega)

/-- The complete graph supplies exactly one root-containing choice per vertex. -/
theorem complete_rooted_count :
    (rootedChoices (⊤ : SimpleGraph V)).card = Fintype.card V := by
  classical
  have he : rootedChoices (⊤ : SimpleGraph V) =
      (Finset.univ : Finset V).image (fun a => ({a} : Finset V)) := by
    ext S
    simp only [rootedChoices, Finset.mem_filter, Finset.mem_univ, true_and,
      complete_rooted_iff, Finset.mem_image]
    simpa only [eq_comm] using (Finset.card_eq_one (s := S))
  rw [he, Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ]

end D5.S3.Combinatorics.MinimalForts.CompleteRooted
