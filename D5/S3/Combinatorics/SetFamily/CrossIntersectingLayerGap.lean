/- GID: D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap
   mirror-E: none(waiver:general-structural-theorem)
   anchors: []
   utility: none
   digest: Two cross-intersecting upper families above the endpoint mass have coatom-singleton gap two. -/

import Mathlib.Data.Finset.Slice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The mass of a family when every set of a given rank has the same weight. -/
def weightedMass (ω : ℕ → ℝ) (C : Finset (Finset α)) : ℝ :=
  ∑ A ∈ C, ω A.card

private def singletonIndices (C : Finset (Finset α)) : Finset α :=
  univ.filter fun a => ({a} : Finset α) ∈ C

private def coatomIndices (C : Finset (Finset α)) : Finset α :=
  univ.filter fun a => (univ.erase a : Finset α) ∈ C

private theorem singleton_count (C : Finset (Finset α)) :
    (singletonIndices C).card = (C.slice 1).card := by
  classical
  apply Finset.card_bij (fun a _ => ({a} : Finset α))
  · intro a ha
    simp only [singletonIndices, mem_filter, mem_univ, true_and] at ha
    simpa [Finset.mem_slice] using ha
  · intro a ha b hb hab
    simpa using hab
  · intro s hs
    obtain ⟨hsC, hscard⟩ := Finset.mem_slice.mp hs
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
    exact ⟨a, by simpa [singletonIndices], rfl⟩

private theorem coatom_count (C : Finset (Finset α)) (hd : 1 ≤ Fintype.card α) :
    (coatomIndices C).card = (C.slice (Fintype.card α - 1)).card := by
  classical
  apply Finset.card_bij (fun a _ => (univ.erase a : Finset α))
  · intro a ha
    simp only [coatomIndices, mem_filter, mem_univ, true_and] at ha
    simpa [Finset.mem_slice] using ha
  · intro a ha b hb hab
    exact (Finset.erase_inj univ (mem_univ a)).mp hab
  · intro s hs
    obtain ⟨hsC, hscard⟩ := Finset.mem_slice.mp hs
    have hcompl : (univ \ s).card = 1 := by
      rw [Finset.card_sdiff_of_subset (subset_univ s), card_univ, hscard]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl
    have hsa : s = univ.erase a := by
      ext b
      have hx := Finset.ext_iff.mp ha b
      simp only [mem_sdiff, mem_univ, true_and, mem_singleton, mem_erase,
        true_and] at hx ⊢
      tauto
    subst s
    exact ⟨a, by simpa [coatomIndices], rfl⟩

private theorem mass_le_endpoint_of_mandatory_coatom
    (ω : ℕ → ℝ) (C : Finset (Finset α)) (a : α)
    (hω : ∀ r, 0 ≤ ω r)
    (hC : ∀ s ∈ C, (univ.erase a : Finset α) ⊆ s) :
    weightedMass ω C ≤ ω (Fintype.card α - 1) + ω (Fintype.card α) := by
  classical
  have hsub : C ⊆ ({univ.erase a, univ} : Finset (Finset α)) := by
    intro s hs
    have h := hC s hs
    by_cases ha : a ∈ s
    · have heq : s = univ := by
        apply eq_univ_of_forall
        intro b
        by_cases hba : b = a
        · simpa [hba] using ha
        · exact h (by simp [hba])
      simp [heq]
    · have heq : s = univ.erase a := by
        apply Subset.antisymm
        · intro b hb
          exact mem_erase.mpr ⟨by intro hab; exact ha (hab ▸ hb), mem_univ b⟩
        · exact h
      simp [heq]
  have hne : (univ.erase a : Finset α) ≠ univ := by
    intro h
    have := Finset.ext_iff.mp h a
    simpa using this
  calc
    weightedMass ω C ≤ ∑ s ∈ ({univ.erase a, univ} : Finset (Finset α)), ω s.card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => hω s.card)
    _ = _ := by simp [hne]

private theorem two_le_coatom_count
    (ω : ℕ → ℝ) (C : Finset (Finset α))
    (hd : 1 ≤ Fintype.card α) (hω : ∀ r, 0 ≤ ω r)
    (hupper : IsUpperSet (C : Set (Finset α)))
    (hmass : ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω C) :
    2 ≤ (coatomIndices C).card := by
  classical
  haveI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  by_contra hsmall
  have hcard : (coatomIndices C).card ≤ 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  apply (not_le_of_gt hmass)
  apply mass_le_endpoint_of_mandatory_coatom ω C a hω
  intro s hs b hb
  obtain ⟨hba, _⟩ := mem_erase.mp hb
  by_contra hbs
  have hsub : s ⊆ (univ.erase b : Finset α) := by
    intro c hc
    exact mem_erase.mpr ⟨by intro hcb; exact hbs (hcb ▸ hc), mem_univ c⟩
  have hbC : (univ.erase b : Finset α) ∈ C := hupper hsub hs
  have hbK : b ∈ coatomIndices C := by simpa [coatomIndices] using hbC
  have := mem_singleton.mp (ha hbK)
  exact hba this

private theorem singleton_count_add_two_le_card
    (ω : ℕ → ℝ) (C D : Finset (Finset α))
    (hd : 1 ≤ Fintype.card α) (hω : ∀ r, 0 ≤ ω r)
    (hcross : ∀ s ∈ C, ∀ t ∈ D, (s ∩ t).Nonempty)
    (hmass : ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω D) :
    (singletonIndices C).card + 2 ≤ Fintype.card α := by
  classical
  haveI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  by_contra hsmall
  have hcompl : (univ \ singletonIndices C).card ≤ 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_card (subset_univ (singletonIndices C))
    simp only [card_univ] at this
    omega
  obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcompl
  apply (not_le_of_gt hmass)
  apply mass_le_endpoint_of_mandatory_coatom ω D a hω
  intro t ht b hb
  have hbS : b ∈ singletonIndices C := by
    by_contra hn
    have hbcompl : b ∈ univ \ singletonIndices C := by simp [hn]
    have := mem_singleton.mp (ha hbcompl)
    exact (mem_erase.mp hb).1 this
  have hbC : ({b} : Finset α) ∈ C := by simpa [singletonIndices] using hbS
  obtain ⟨c, hc⟩ := hcross {b} hbC t ht
  simp only [mem_inter, mem_singleton] at hc
  simpa [hc.1] using hc.2

/-- Cross-intersecting upward families whose masses exceed the coatom/top
threshold have at least two more coatoms than singletons on the first side.
No monotonicity or strict positivity of the rank weights is assumed. -/
theorem weighted_cross_intersecting_layer_gap
    (ω : ℕ → ℝ) (C D : Finset (Finset α))
    (hd : 4 ≤ Fintype.card α) (hω : ∀ r, 0 ≤ ω r)
    (hC : IsUpperSet (C : Set (Finset α)))
    (hD : IsUpperSet (D : Set (Finset α)))
    (hcross : ∀ s ∈ C, ∀ t ∈ D, (s ∩ t).Nonempty)
    (hmassC : ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω C)
    (hmassD : ω (Fintype.card α - 1) + ω (Fintype.card α) < weightedMass ω D) :
    (C.slice 1).card + 2 ≤ (C.slice (Fintype.card α - 1)).card := by
  classical
  rw [← singleton_count, ← coatom_count C (by omega)]
  have htwo := two_le_coatom_count ω C (by omega) hω hC hmassC
  have hsingle := singleton_count_add_two_le_card ω C D (by omega) hω hcross hmassD
  by_cases hzero : (singletonIndices C).card = 0
  · omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (singletonIndices C).card)
  have haC : ({a} : Finset α) ∈ C := by simpa [singletonIndices] using ha
  have hcoat : ∀ b : α, b ≠ a → b ∈ coatomIndices C := by
    intro b hba
    have hsub : ({a} : Finset α) ⊆ univ.erase b := by simp [Ne.symm hba]
    have := hC hsub haC
    simpa [coatomIndices] using this
  by_cases hone : (singletonIndices C).card = 1
  · have hsub : (univ.erase a : Finset α) ⊆ coatomIndices C := by
      intro b hb
      exact hcoat b (mem_erase.mp hb).1
    have hbound := card_le_card hsub
    simp only [card_erase_of_mem (mem_univ a), card_univ] at hbound
    omega
  · have hS : 1 < (singletonIndices C).card := by omega
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hS a
    have hbC : ({b} : Finset α) ∈ C := by simpa [singletonIndices] using hb
    have hfull : coatomIndices C = univ := by
      apply eq_univ_of_forall
      intro c
      by_cases hca : c = a
      · subst c
        have hsub : ({b} : Finset α) ⊆ univ.erase a := by simp [hba]
        have := hC hsub hbC
        simpa [coatomIndices] using this
      · exact hcoat c hca
    rw [hfull, card_univ]
    exact hsingle

end D5.S3.Combinatorics.SetFamily.CrossIntersectingLayerGap
