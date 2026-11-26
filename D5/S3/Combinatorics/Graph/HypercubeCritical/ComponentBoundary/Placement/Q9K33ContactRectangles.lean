/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ContactRectangles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ContactRectangles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The two-coordinate swap rule forces coincident Cartesian products. -/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Prod
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! Contact rectangles for the six active coordinates of a K₃,₃ mask graph.
The abstract statement takes the two companion swaps as hypotheses. -/

set_option autoImplicit false

namespace Q9K33ContactRectangles

variable {α β : Type*}

/-- A contact differs in both coordinates. Both endpoints can simultaneously
swap their first coordinates, and both can simultaneously swap their second. -/
def ClosedUnderContactSwaps (A D : Set (α × β)) : Prop :=
  ∀ ⦃a a' : α⦄ ⦃b b' : β⦄, (a, b) ∈ A → (a', b') ∈ D → a ≠ a' → b ≠ b' →
    ((a', b) ∈ A ∧ (a, b') ∈ D) ∧ ((a, b') ∈ A ∧ (a', b) ∈ D)

/-- Every contact fills the four corners in both aligned sets. -/
theorem contact_rectangle {A D : Set (α × β)} (h : ClosedUnderContactSwaps A D)
    {a a' : α} {b b' : β} (ha : (a, b) ∈ A) (hd : (a', b') ∈ D)
    (hr : a ≠ a') (hc : b ≠ b') :
    (a, b) ∈ A ∩ D ∧ (a', b) ∈ A ∩ D ∧ (a, b') ∈ A ∩ D ∧ (a', b') ∈ A ∩ D := by
  obtain ⟨⟨h10A, h01D⟩, ⟨h01A, h10D⟩⟩ := h ha hd hr hc
  obtain ⟨_, ⟨h11A, h00D⟩⟩ := h h10A h01D hr.symm hc
  exact ⟨⟨ha, h00D⟩, ⟨h10A, h10D⟩, ⟨h01A, h01D⟩, ⟨h11A, hd⟩⟩

/-- One contact forces the aligned sets to coincide with the product of their
coordinate projections. The factors can have arbitrary cardinality. -/
theorem eq_prod_of_contact {A D : Set (α × β)} (h : ClosedUnderContactSwaps A D)
    {a a' : α} {b b' : β} (ha : (a, b) ∈ A) (hd : (a', b') ∈ D)
    (hr : a ≠ a') (hc : b ≠ b') :
    A = D ∧ A = (Prod.fst '' A) ×ˢ (Prod.snd '' A) := by
  classical
  obtain ⟨h00, h10, h01, h11⟩ := contact_rectangle h ha hd hr hc
  -- For any point, some corner of this shared rectangle differs in both coordinates.
  have opposite (x : α) (y : β) : ∃ u v, (u, v) ∈ A ∩ D ∧ x ≠ u ∧ y ≠ v := by
    by_cases hx : x = a
    · have hxa : x ≠ a' := fun he => hr (hx.symm.trans he)
      by_cases hy : y = b
      · exact ⟨a', b', h11, hxa, fun he => hc (hy.symm.trans he)⟩
      · exact ⟨a', b, h10, hxa, hy⟩
    · by_cases hy : y = b
      · exact ⟨a, b', h01, hx, fun he => hc (hy.symm.trans he)⟩
      · exact ⟨a, b, h00, hx, hy⟩
  have heq : A = D := by
    apply Set.ext
    rintro ⟨x, y⟩
    obtain ⟨u, v, huv, hxu, hyv⟩ := opposite x y
    constructor
    · intro hxy
      exact (contact_rectangle h hxy huv.2 hxu hyv).1.2
    · intro hxy
      obtain ⟨_, _, _, hcorner⟩ := contact_rectangle h huv.1 hxy hxu.symm hyv.symm
      exact hcorner.1
  refine ⟨heq, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Set.mem_prod.mp hxy
    obtain ⟨⟨x', v⟩, hxmin, hx'⟩ := (Set.mem_image Prod.fst A x).mp hx
    obtain ⟨⟨u, y'⟩, hymin, hy'⟩ := (Set.mem_image Prod.snd A y).mp hy
    change x' = x at hx'
    change y' = y at hy'
    subst x'
    subst y'
    by_cases hxu : x = u
    · simpa only [hxu] using hymin
    by_cases hvy : v = y
    · simpa only [hvy] using hxmin
    have hyD : (u, y) ∈ D := heq ▸ hymin
    exact (h hxmin hyD hxu hvy).2.1

section Differences

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]

/-- All nonzero differences within one factor. -/
def nonzeroDifferences (S : Finset G) : Finset G :=
  S.offDiag.image fun p => p.2 - p.1

theorem mem_nonzeroDifferences {S : Finset G} {d : G} :
    d ∈ nonzeroDifferences S ↔ ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ y - x = d := by
  unfold nonzeroDifferences
  constructor
  · intro hd
    obtain ⟨⟨x, y⟩, hxy, he⟩ := Finset.mem_image.mp hd
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
    exact ⟨x, hx, y, hy, hne, he⟩
  · rintro ⟨x, hx, y, hy, hne, he⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, he⟩

/-- The differences of cross pairs in the aligned layers encode the contact masks. -/
def contactMasks (A D : Finset (G × H)) : Finset (G × H) :=
  ((A.product D).filter fun p => p.1.1 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2).image
    fun p => (p.2.1 - p.1.1, p.2.2 - p.1.2)

theorem mem_contactMasks {A D : Finset (G × H)} {d : G × H} :
    d ∈ contactMasks A D ↔ ∃ p ∈ A, ∃ q ∈ D,
      p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ (q.1 - p.1, q.2 - p.2) = d := by
  unfold contactMasks
  constructor
  · intro hd
    obtain ⟨⟨p, q⟩, hpq, he⟩ := Finset.mem_image.mp hd
    obtain ⟨hmem, hr, hc⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hmem
    exact ⟨p, hp, q, hq, hr, hc, he⟩
  · rintro ⟨p, hp, q, hq, hr, hc, he⟩
    exact Finset.mem_image.mpr ⟨(p, q),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hr, hc⟩, he⟩

theorem contactMasks_product (R : Finset G) (S : Finset H) :
    contactMasks (R.product S) (R.product S) =
      (nonzeroDifferences R).product (nonzeroDifferences S) := by
  ext d
  constructor
  · intro hd
    obtain ⟨p, hp, q, hq, hr, hc, he⟩ := mem_contactMasks.mp hd
    obtain ⟨hpR, hpS⟩ := Finset.mem_product.mp hp
    obtain ⟨hqR, hqS⟩ := Finset.mem_product.mp hq
    exact Finset.mem_product.mpr
      ⟨mem_nonzeroDifferences.mpr ⟨p.1, hpR, q.1, hqR, hr, congrArg Prod.fst he⟩,
        mem_nonzeroDifferences.mpr ⟨p.2, hpS, q.2, hqS, hc, congrArg Prod.snd he⟩⟩
  · intro hd
    obtain ⟨hR, hS⟩ := Finset.mem_product.mp hd
    obtain ⟨a, ha, a', ha', hr, heR⟩ := mem_nonzeroDifferences.mp hR
    obtain ⟨b, hb, b', hb', hc, heS⟩ := mem_nonzeroDifferences.mp hS
    exact mem_contactMasks.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, (a', b'), Finset.mem_product.mpr ⟨ha', hb'⟩,
        hr, hc, Prod.ext heR heS⟩

end Differences

section KleinFour

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
  [Fintype G] [Fintype H] [IsAddKleinFour G] [IsAddKleinFour H]

/-- Two points give one direction. Any three points give all three directions. -/
theorem card_nonzeroDifferences {S : Finset G} (hS : 2 ≤ S.card) :
    (nonzeroDifferences S).card = if S.card = 2 then 1 else 3 := by
  have swap_sub (x y : G) : x - y = y - x := by
    rw [← neg_sub y x, IsAddKleinFour.neg_eq_self]
  by_cases htwo : S.card = 2
  · rw [ite_eq_left htwo]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
    have hdiff : nonzeroDifferences ({a, b} : Finset G) = {b - a} := by
      ext d
      rw [mem_nonzeroDifferences, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact (hxy (hx.trans hy.symm)).elim
        · simp only [hx, hy]
        · simpa only [hx, hy] using swap_sub a b
        · exact (hxy (hx.trans hy.symm)).elim
      · rintro rfl
        exact ⟨a, by simp, b, by simp, hab, rfl⟩
    rw [hdiff, Finset.card_singleton]
  · rw [ite_eq_right htwo]
    have hsub : nonzeroDifferences S ⊆ (Finset.univ : Finset G).erase 0 := by
      intro d hd
      obtain ⟨x, _, y, _, hxy, rfl⟩ := mem_nonzeroDifferences.mp hd
      exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hxy.symm, Finset.mem_univ _⟩
    have hupper : (nonzeroDifferences S).card ≤ 3 := by
      have hsize : ((Finset.univ : Finset G).erase 0).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : G))]
        change Fintype.card G - 1 = 3
        rw [IsAddKleinFour.card_four']
      exact le_trans (Finset.card_le_card hsub) hsize.le
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card.mp (lt_of_le_of_ne hS (fun he => htwo he.symm))
    have hlower : 2 < (nonzeroDifferences S).card := by
      refine Finset.two_lt_card.mpr
        ⟨b - a, mem_nonzeroDifferences.mpr ⟨a, ha, b, hb, hab, rfl⟩,
          c - a, mem_nonzeroDifferences.mpr ⟨a, ha, c, hc, hac, rfl⟩,
          c - b, mem_nonzeroDifferences.mpr ⟨b, hb, c, hc, hbc, rfl⟩, ?_, ?_, ?_⟩
      · exact fun he => hbc (sub_left_inj.mp he)
      · rw [swap_sub b a]
        exact fun he => hac (sub_left_inj.mp he)
      · exact fun he => hab (sub_right_inj.mp he)
    exact Nat.le_antisymm hupper (Nat.succ_le_of_lt hlower)

/-- For two Klein four factors, the exact mask set is the product of the
factor differences. The cardinality depends only on the two factor sizes. -/
theorem contactMasks_of_contact {A D : Finset (G × H)}
    (h : ClosedUnderContactSwaps (A : Set (G × H)) (D : Set (G × H)))
    {p q : G × H} (hp : p ∈ A) (hq : q ∈ D) (hr : p.1 ≠ q.1) (hc : p.2 ≠ q.2) :
    ∃ R : Finset G, ∃ S : Finset H,
      2 ≤ R.card ∧ 2 ≤ S.card ∧ A = R.product S ∧ D = R.product S ∧
      contactMasks A D = (nonzeroDifferences R).product (nonzeroDifferences S) ∧
      (contactMasks A D).card = (if R.card = 2 then 1 else 3) * (if S.card = 2 then 1 else 3) := by
  let R := A.image Prod.fst
  let S := A.image Prod.snd
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  obtain ⟨heq, hprod⟩ := eq_prod_of_contact h (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hr hc
  have hAD : A = D := Finset.coe_injective heq
  have hA : A = R.product S := by
    apply Finset.coe_injective
    change (A : Set (G × H)) =
      ((R ×ˢ S : Finset (G × H)) : Set (G × H))
    rw [Finset.coe_product]
    simpa only [Finset.coe_image, R, S] using hprod
  have hD : D = R.product S := hAD.symm.trans hA
  have hqA : (q₁, q₂) ∈ A := hAD.symm ▸ hq
  have hR : 2 ≤ R.card := Nat.succ_le_of_lt (Finset.one_lt_card.mpr
    ⟨p₁, Finset.mem_image_of_mem Prod.fst hp, q₁, Finset.mem_image_of_mem Prod.fst hqA, hr⟩)
  have hS : 2 ≤ S.card := Nat.succ_le_of_lt (Finset.one_lt_card.mpr
    ⟨p₂, Finset.mem_image_of_mem Prod.snd hp, q₂, Finset.mem_image_of_mem Prod.snd hqA, hc⟩)
  have hmask : contactMasks A D = (nonzeroDifferences R).product (nonzeroDifferences S) := by
    rw [hA, hD, contactMasks_product]
  refine ⟨R, S, hR, hS, hA, hD, hmask, ?_⟩
  rw [hmask]
  change ((nonzeroDifferences R) ×ˢ (nonzeroDifferences S)).card = _
  rw [Finset.card_product, card_nonzeroDifferences hR, card_nonzeroDifferences hS]

theorem contactMasks_card_one_three_or_nine {A D : Finset (G × H)}
    (h : ClosedUnderContactSwaps (A : Set (G × H)) (D : Set (G × H)))
    {p q : G × H} (hp : p ∈ A) (hq : q ∈ D) (hr : p.1 ≠ q.1) (hc : p.2 ≠ q.2) :
    (contactMasks A D).card = 1 ∨ (contactMasks A D).card = 3 ∨ (contactMasks A D).card = 9 := by
  obtain ⟨R, S, _, _, _, _, _, hcard⟩ := contactMasks_of_contact h hp hq hr hc
  rw [hcard]
  by_cases hR : R.card = 2 <;> by_cases hS : S.card = 2 <;>
    simp only [hR, hS, ite_true, ite_false] <;> decide

end KleinFour

end Q9K33ContactRectangles
