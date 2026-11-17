/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The closed six-point mixed Y exhausts all exceptional high vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCore
import D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
import Batteries.Tactic.OpenPrivate

/-! The actual Y complement in the mixed high profile. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCycle

open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private mixed_saturated_y_core from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCore
open private small_two_regular_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle

variable {X : Type*} [Fintype X]

/-- The complement of the actual Y is an actual eight-cycle. The degree-two
Y arm and its leaf are explicitly outside this cycle. -/
private theorem mixed_high_cycle
    (H : SimpleGraph X) {L R : Finset X}
    (hpart : H.IsBipartiteWith (L : Set X) (R : Set X))
    (hcard : Fintype.card X = 14) (hg : (8 : ℕ∞) ≤ H.egirth)
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hL : ((L.filter fun x => H.degree x = 1).card,
      (L.filter fun x => H.degree x = 2).card,
      (L.filter fun x => H.degree x = 3).card) = (1, 6, 0))
    (hR : ((R.filter fun x => H.degree x = 1).card,
      (R.filter fun x => H.degree x = 2).card,
      (R.filter fun x => H.degree x = 3).card) = (2, 4, 1))
    (hsatL : ∀ x ∈ L, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2) :
    ∃ s r, H.degree s = 2 ∧ H.degree r = 1 ∧ H.Adj s r ∧
      ∃ e : cycleGraph 8 ↪g H, (∀ i, H.degree (e i) = 2) ∧
        (∀ i, s ≠ e i) ∧ (∀ i, r ≠ e i) := by
  classical
  obtain ⟨t, a, s₁, s₂, r₁, r₂, htR, haL, hs₁L, hs₂L, hr₁R, hr₂R,
    ht3, ha1, hs₁2, hs₂2, hr₁1, hr₂1, hn, hNt, hNa, hNs₁, hNs₂, hNr₁, hNr₂⟩ :=
    mixed_saturated_y_core hpart hdeg hL hR hsatL
  let S : Finset X := ([a, s₁, s₂, t, r₁, r₂] : List X).toFinset
  have hScard : S.card = 6 := by rw [List.toFinset_card_of_nodup hn]; rfl
  have hSmem (x : X) : x ∈ S ↔
      x = a ∨ x = s₁ ∨ x = s₂ ∨ x = t ∨ x = r₁ ∨ x = r₂ := by simp [S]
  have hrne : r₁ ≠ r₂ := by
    have := hn
    simp only [List.nodup_cons, List.mem_cons] at this
    simpa using this.2.2.2.2.1
  have hL1 : L.filter (fun x => H.degree x = 1) = {a} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      have he := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_filter.mpr ⟨haL, ha1⟩
    · have hc := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hL
      simpa using hc.le
  have hR1 : R.filter (fun x => H.degree x = 1) = {r₁, r₂} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨hr₁R, hr₁1⟩
      · have he := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_filter.mpr ⟨hr₂R, hr₂1⟩
    · have hc := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hR
      simpa [hrne] using hc.le
  have hL3 : L.filter (fun x => H.degree x = 3) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hL
  have hR3 : R.filter (fun x => H.degree x = 3) = {t} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      have he := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_filter.mpr ⟨htR, ht3⟩
    · have hc := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hR
      simpa using hc.le
  have hother (x : X) (hx : x ∉ S) : H.degree x = 2 := by
    have hp : 0 < H.degree x := by rcases hdeg x with h | h | h <;> omega
    obtain ⟨y, hxy⟩ := (H.degree_pos_iff_exists_adj x).mp hp
    have hside : x ∈ L ∨ x ∈ R := by
      rcases hpart.mem_of_adj hxy with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    rcases hdeg x with h | h | h
    · exfalso
      apply hx
      rcases hside with hxL | hxR
      · have hm : x ∈ L.filter (fun z => H.degree z = 1) := Finset.mem_filter.mpr ⟨hxL, h⟩
        rw [hL1] at hm
        exact (hSmem x).mpr (Or.inl (Finset.mem_singleton.mp hm))
      · have hm : x ∈ R.filter (fun z => H.degree z = 1) := Finset.mem_filter.mpr ⟨hxR, h⟩
        rw [hR1] at hm
        rcases Finset.mem_insert.mp hm with he | he
        · exact (hSmem x).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
        · have he := Finset.mem_singleton.mp he
          exact (hSmem x).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
    · exact h
    · exfalso
      rcases hside with hxL | hxR
      · have hm : x ∈ L.filter (fun z => H.degree z = 3) := Finset.mem_filter.mpr ⟨hxL, h⟩
        rw [hL3] at hm
        exact Finset.notMem_empty _ hm
      · have hm : x ∈ R.filter (fun z => H.degree z = 3) := Finset.mem_filter.mpr ⟨hxR, h⟩
        rw [hR3] at hm
        exact hx ((hSmem x).mpr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp hm))))))
  have hma : a ∈ S := by simp [S]
  have hms₁ : s₁ ∈ S := by simp [S]
  have hms₂ : s₂ ∈ S := by simp [S]
  have hmt : t ∈ S := by simp [S]
  have hmr₁ : r₁ ∈ S := by simp [S]
  have hmr₂ : r₂ ∈ S := by simp [S]
  have hclosed : ∀ y ∈ S, H.neighborFinset y ⊆ S := by
    intro y hy
    rcases (hSmem y).mp hy with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [hNa, Finset.singleton_subset_iff] using hmt
    · simpa only [hNs₁, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hmt hmr₁
    · simpa only [hNs₂, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hmt hmr₂
    · simpa only [hNt, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hma (And.intro hms₁ hms₂)
    · simpa only [hNr₁, Finset.singleton_subset_iff] using hms₁
    · simpa only [hNr₂, Finset.singleton_subset_iff] using hms₂
  let T : Set X := {x | x ∉ S}
  have hTcard : Fintype.card T = 8 := by
    rw [← Set.toFinset_card]
    have he : T.toFinset = Sᶜ := by ext x; simp [T]
    rw [he, Finset.card_compl, hScard, hcard]
  let K := H.induce T
  have hne : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty T := hne
  have hdegree (x : T) : K.degree x = 2 := by
    have hsub : H.neighborSet x.val ⊆ T := by
      intro y hxy hy
      have hm : x.val ∈ H.neighborFinset y := (H.mem_neighborFinset _ _).mpr hxy.symm
      exact x.property (hclosed y hy hm)
    exact (H.degree_induce_of_neighborSet_subset hsub).trans (hother x.val x.property)
  have hKg : (8 : ℕ∞) ≤ K.egirth :=
    hg.trans (SimpleGraph.Embedding.induce T).isContained.egirth_le
  obtain ⟨_, p, _, hlen, _, hiso⟩ := small_two_regular_cycle K hdegree hKg (by omega)
  have hl : p.length = 8 := hlen.trans hTcard
  obtain ⟨e⟩ : Nonempty (cycleGraph 8 ≃g K) := hl ▸ hiso
  have hsr : H.Adj s₁ r₁ := by
    apply (H.mem_neighborFinset _ _).mp
    rw [hNs₁]
    simp
  let e' : cycleGraph 8 ↪g H :=
    { toFun := fun i => (e i).val
      inj' := fun i j he => e.injective (Subtype.ext he)
      map_rel_iff' := by intro i j; exact e.map_rel_iff }
  refine ⟨s₁, r₁, hs₁2, hr₁1, hsr, e', fun i => hother _ (e i).property, ?_, ?_⟩
  · intro i he
    change s₁ = (e i).val at he
    exact (e i).property (he ▸ hms₁)
  · intro i he
    change r₁ = (e i).val at he
    exact (e i).property (he ▸ hmr₁)

#print axioms mixed_high_cycle

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCycle
