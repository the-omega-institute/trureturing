/- GID: D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting
   mirror-E: none(waiver:general-path-counting)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Fin]
   utility: none
   digest: Endpoint occupancy bounds the number of broadcasters at an interior path vertex. -/

import D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathDefs
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathCounting

open PackingDomaticPathDefs Finset

/-- The endpoint and interior counts force a uniform palette lower bound. -/
theorem local_counting {n k t : ℕ} {f : Fin n → ℕ}
    (hf : IsPackingDomatic n k t f) (hn : t + 1 ≤ n) : 16 * k ≤ 15 * t + 12 := by
  classical
  obtain ⟨hcolour, hpacking, A, hdom⟩ := hf
  let E : Finset (Fin n) := univ.filter fun a => a.val ≤ f a
  let C : Finset ℕ := E.image f
  let P : Finset ℕ := Icc 1 t
  let M : Finset ℕ := P \ C
  have memE (a : Fin n) : a ∈ E ↔ a.val ≤ f a := by simp [E]
  have einj : Set.InjOn f E := by
    intro a ha b hb hab
    by_contra hne
    have hp := hpacking a b hne hab
    have ha' := (memE a).mp ha
    have hb' := (memE b).mp hb
    unfold Nat.dist at hp
    omega
  have ccard : C.card = E.card := card_image_of_injOn einj
  have cp : C ⊆ P := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr (hcolour a)
  have pcard : P.card = t := by simp [P]
  have et : E.card ≤ t := by
    have := card_le_card cp
    omega
  have count_dom (x : Fin n) :
      k ≤ (univ.filter fun a : Fin n => Nat.dist x.val a.val ≤ f a).card := by
    choose g hg hgcover using fun i => hdom i x
    have hi : Function.Injective g := by
      intro i j hij
      exact (hg i).symm.trans ((congrArg A hij).trans (hg j))
    have hc := card_le_card_of_injOn g
      (s := (univ : Finset (Fin k)))
      (t := univ.filter fun a : Fin n => Nat.dist x.val a.val ≤ f a)
      (by intro i _; simp [hgcover i]) (hi.injOn)
    simpa using hc
  have ke : k ≤ E.card := by
    have := count_dom (⟨0, by omega⟩ : Fin n)
    simpa [E, Nat.dist_zero_left] using this
  let δ := t - E.card
  have mcard : M.card = δ := by
    rw [card_sdiff_of_subset cp, pcard, ccard]
  have edelta : E.card + δ = t := by omega
  let d := t - k
  have kt : k ≤ t := by omega
  have kd : k + d = t := by omega
  have deltad : δ ≤ d := by omega
  by_contra hbound
  have ht : 16 * d + 13 ≤ t := by omega
  let z := 8 * d + 7
  let h := 4 * d + 3
  have hz : z < n := by omega
  have hzt : z ≤ t := by omega
  have hht : h ≤ t := by omega
  have hgap : 2 * z ≤ t + 1 := by omega
  let x : Fin n := ⟨z, hz⟩
  let B : Finset (Fin n) := univ.filter fun a => Nat.dist z a.val ≤ f a
  let B₁ := E.filter fun a => Nat.dist z a.val ≤ f a
  let I : Finset (Fin n) := univ.filter fun a => a.val ≤ t
  let B₂ := I \ E
  let R : Finset (Fin n) := univ.filter fun a => t < a.val ∧ Nat.dist z a.val ≤ f a
  have prefix_card (q : ℕ) (hq : q ≤ n) :
      (univ.filter fun a : Fin n => a.val < q).card = q := by
    calc
      _ = (range q).card := by
        apply card_bij (fun a _ => a.val)
        · intro a ha
          simpa using ha
        · intro a ha b hb hab
          exact Fin.ext hab
        · intro b hb
          have hb' : b < q := mem_range.mp hb
          exact ⟨⟨b, by omega⟩, by simp [hb'], rfl⟩
      _ = q := card_range q
  have icard : I.card = t + 1 := by
    have := prefix_card (t + 1) hn
    simpa [I, Nat.lt_succ_iff] using this
  have ei : E ⊆ I := by
    intro a ha
    have ha' := (memE a).mp ha
    have := (hcolour a).2
    simp only [I, mem_filter, mem_univ, true_and]
    omega
  have b2card : B₂.card = δ + 1 := by
    have hc : B₂.card = I.card - E.card := card_sdiff_of_subset ei
    omega
  -- Endpoint broadcasters covering z must have colour greater than h.
  have b1high (a : Fin n) (ha : a ∈ B₁) : h < f a := by
    obtain ⟨hae, hac⟩ := mem_filter.mp ha
    have ha' := (memE a).mp hae
    unfold Nat.dist at hac
    dsimp [z, h] at *
    omega
  have b1card : B₁.card ≤ t - h := by
    have hc := card_le_card_of_injOn f
      (s := B₁) (t := Icc (h + 1) t)
      (by
        intro a ha
        have := b1high a ha
        have := (hcolour a).2
        exact mem_Icc.mpr ⟨by omega, by omega⟩)
      (einj.mono (filter_subset _ _))
    simpa using hc
  -- Low colours missing from E are charged to M.
  have low_count (q : ℕ) (hq : q ≤ t) :
      q ≤ (E.filter fun a => f a ≤ q).card + δ := by
    have hs : Icc 1 q ⊆ (E.filter fun a => f a ≤ q).image f ∪ M := by
      intro j hj
      obtain ⟨hjpos, hjq⟩ := mem_Icc.mp hj
      by_cases hjc : j ∈ C
      · obtain ⟨a, ha, hfa⟩ := mem_image.mp hjc
        apply mem_union_left
        exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, by omega⟩, hfa⟩
      · apply mem_union_right
        exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hjpos, by omega⟩, hjc⟩
    have hc := card_le_card hs
    have hu := card_union_le ((E.filter fun a => f a ≤ q).image f) M
    have he := card_image_le (s := E.filter fun a => f a ≤ q) (f := f)
    have hqcard : (Icc 1 q).card = q := by simp
    omega
  -- High-colour endpoint occurrences below z compete for positions with the low ones.
  let L := E.filter fun a => f a ≤ z - 1
  let H := E.filter fun a => a.val < z ∧ z ≤ f a
  have lcount : z - 1 ≤ L.card + δ := low_count (z - 1) (by omega)
  have lhdis : Disjoint L H := by
    apply disjoint_left.mpr
    intro a ha hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2.2
    omega
  have lhsub : L ∪ H ⊆ univ.filter fun a : Fin n => a.val < z := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · have hae := (mem_filter.mp ha).1
      have haf := (mem_filter.mp ha).2
      have hav := (memE a).mp hae
      simp only [mem_filter, mem_univ, true_and]
      omega
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2.1⟩
  have hcard : H.card ≤ δ + 1 := by
    have hc := card_le_card lhsub
    have hu := card_union_of_disjoint lhdis
    have hzcard := prefix_card z (by omega)
    omega
  -- Every right-hand broadcaster has large colour, and its colour is unique there.
  have rlarge (b : Fin n) (hb : b ∈ R) : z ≤ f b := by
    have hb' := (mem_filter.mp hb).2
    unfold Nat.dist at hb'
    omega
  have rinj : Set.InjOn f R := by
    intro a ha b hb hab
    by_contra hne
    have hp := hpacking a b hne hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    unfold Nat.dist at hp ha' hb'
    omega
  have rsub : R.image f ⊆ H.image f ∪ M := by
    intro j hj
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hj
    by_cases hc : f b ∈ C
    · obtain ⟨a, ha, hab⟩ := mem_image.mp hc
      have hav := (memE a).mp ha
      have hat := (hcolour a).2
      have hb' := (mem_filter.mp hb).2
      have hne : a ≠ b := by
        intro heq
        subst b
        omega
      have hp := hpacking a b hne hab
      have hr := rlarge b hb
      have haz : a.val < z := by
        unfold Nat.dist at hp hb'
        omega
      apply mem_union_left
      exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, haz, by omega⟩, hab⟩
    · apply mem_union_right
      exact mem_sdiff.mpr ⟨mem_Icc.mpr (hcolour b), hc⟩
  have rcard : R.card ≤ 2 * δ + 1 := by
    have hc := card_le_card rsub
    have hu := card_union_le (H.image f) M
    have he := card_image_le (s := H) (f := f)
    have hr := card_image_of_injOn rinj
    omega
  have bsub : B ⊆ B₁ ∪ B₂ ∪ R := by
    intro a ha
    have hac := (mem_filter.mp ha).2
    by_cases hae : a ∈ E
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hae, hac⟩))
    · by_cases hai : a.val ≤ t
      · exact mem_union_left _ (mem_union_right _
          (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hai⟩, hae⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega, hac⟩)
  have bcard : B.card ≤ B₁.card + B₂.card + R.card := by
    have hc := card_le_card bsub
    have hu := card_union_le (B₁ ∪ B₂) R
    have hv := card_union_le B₁ B₂
    omega
  have kb : k ≤ B.card := count_dom x
  dsimp [h] at b1card
  omega

end D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathCounting
