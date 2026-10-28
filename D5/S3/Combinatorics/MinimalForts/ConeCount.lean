/- GID: D5/S3/Combinatorics/MinimalForts/ConeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/ConeCount
   mirror-E: none(waiver:counting-bijection-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: The complete minimal-fort count splits into root-free and root-containing classes. -/

import D5.S3.Combinatorics.MinimalForts.UniversalRoot

/-! The two classes are disjoint and exhaust all actual minimal forts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.ConeCount

open D5.S3.Combinatorics.MinimalForts.UniversalRoot

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem lift_injective : Function.Injective (lift : Finset V → Finset (Option V)) := by
  intro S T h
  ext v
  have hv := Finset.ext_iff.mp h (some v)
  simpa [lift] using hv

private theorem rootSet_injective : Function.Injective (rootSet : Finset V → Finset (Option V)) := by
  intro S T h
  ext v
  have hv := Finset.ext_iff.mp h (some v)
  simpa [rootSet, lift] using hv

/-- Exact exhaustive counting; no formula for either class is assumed. -/
theorem cone_minimalFort_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : ∀ v, ∃ w, G.Adj v w) :
    (minimalForts (cone G)).card = (minimalForts G).card + (rootedChoices G).card := by
  classical
  have he : minimalForts (cone G) =
      (minimalForts G).image lift ∪ (rootedChoices G).image rootSet := by
    ext F
    simp only [minimalForts, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image, rootedChoices]
    constructor
    · intro hf
      by_cases hr : none ∈ F
      · right
        have hF : rootSet (baseSet F) = F := by
          ext v
          cases v <;> simp [rootSet, lift, baseSet, hr]
        exact ⟨baseSet F, by simpa only [hF] using hf, hF⟩
      · left
        have hF : lift (baseSet F) = F := by
          ext v
          cases v <;> simp [lift, baseSet, hr]
        exact ⟨baseSet F, (minimalFort_lift_iff G hn _).mp (hF.symm ▸ hf), hF⟩
    · rintro (⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩)
      · exact (minimalFort_lift_iff G hn _).mpr hS
      · exact hS
  have hd : Disjoint ((minimalForts G).image lift) ((rootedChoices G).image rootSet) := by
    apply Finset.disjoint_left.mpr
    intro F hL hR
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hR
    have hroot : none ∈ rootSet T := by simp [rootSet]
    rw [hT] at hroot
    simpa [lift] using hroot
  rw [he, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ lift_injective,
    Finset.card_image_of_injective _ rootSet_injective]

end D5.S3.Combinatorics.MinimalForts.ConeCount
