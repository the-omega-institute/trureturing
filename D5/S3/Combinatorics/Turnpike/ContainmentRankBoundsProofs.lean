/- GID: D5/S3/Combinatorics/Turnpike/ContainmentRankBoundsProofs
   generality: G
   mirror-B: none(waiver:covered-by-containment-rank-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole multiplicity blocks of realized distances -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-! Omega original.
# Whole multiplicity blocks of realized distances

Known containment-rank bounds of Elder, Marçais and Kingsford, WABI 2026,
Lemma 14 and Appendix A.3 (arXiv:2603.18283v1, Lemma 13), CC BY 4.0.
The histogram bridge allows unused labels with zero multiplicity.
-/
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators
noncomputable section

private theorem containing_distance {n : ℕ} {x : Fin n → ℝ}
    (hx : StrictMono x) (e a : Interval n)
    (hl : a.1.1 ≤ e.1.1) (hr : e.1.2 ≤ a.1.2) :
    a = e ∨ x e.1.2 - x e.1.1 < x a.1.2 - x a.1.1 := by
  by_cases he : a = e
  · exact Or.inl he
  right
  have hxl := hx.monotone hl
  have hxr := hx.monotone hr
  by_cases hleft : a.1.1 = e.1.1
  · have hright : e.1.2 < a.1.2 := lt_of_le_of_ne hr (by
      intro h
      apply he
      apply Subtype.ext
      exact Prod.ext hleft h.symm)
    have := hx hright
    rw [hleft] at hxl ⊢
    linarith
  · have := hx (lt_of_le_of_ne hl hleft)
    linarith

private theorem card_containing {n : ℕ} (e : Interval n) :
    (Finset.univ.filter fun a : Interval n => a.1.1 ≤ e.1.1 ∧ e.1.2 ≤ a.1.2).card =
      (e.1.1.val + 1) * (n - e.1.2.val) := by
  classical
  calc
    _ = ((Finset.Iic e.1.1) ×ˢ (Finset.Ici e.1.2)).card := by
      apply Finset.card_bij (fun a _ => a.1)
      · intro a ha
        simpa using (Finset.mem_filter.mp ha).2
      · intro a ha b hb hab
        exact Subtype.ext hab
      · intro b hb
        have h := Finset.mem_product.mp hb
        have hl := Finset.mem_Iic.mp h.1
        have hr := Finset.mem_Ici.mp h.2
        exact ⟨⟨b, lt_of_le_of_lt hl (lt_of_lt_of_le e.2 hr)⟩,
          by simp [hl, hr], rfl⟩
    _ = _ := by simp

private theorem card_contained {n : ℕ} (e : Interval n) :
    (Finset.univ.filter fun a : Interval n => e.1.1 ≤ a.1.1 ∧ a.1.2 ≤ e.1.2).card =
      (e.1.2.val - e.1.1.val + 1).choose 2 := by
  classical
  calc
    _ = (((Finset.Icc e.1.1 e.1.2) ×ˢ (Finset.Icc e.1.1 e.1.2)).filter
        fun a => a.1 < a.2).card := by
      apply Finset.card_bij (fun a _ => a.1)
      · intro a ha
        have h := (Finset.mem_filter.mp ha).2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨h.1, le_trans (le_of_lt a.2) h.2⟩,
          ⟨le_trans h.1 (le_of_lt a.2), h.2⟩⟩, a.2⟩
      · intro a ha b hb hab
        exact Subtype.ext hab
      · intro b hb
        have h := Finset.mem_filter.mp hb
        have hp := Finset.mem_product.mp h.1
        refine ⟨⟨b,h.2⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(Finset.mem_Icc.mp hp.1).1,(Finset.mem_Icc.mp hp.2).2⟩
    _ = _ := by
      rw [Finset.card_product_filter_lt, Fin.card_Icc]
      congr 1
      have := e.2
      omega

private theorem card_intervals (n : ℕ) :
    Fintype.card (Interval n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin n))

/-- Every used label has its entire multiplicity block inside the containment bounds. -/
theorem containment_rank_bounds {n d : ℕ} {y : Fin d → ℝ} {mu : Fin d → ℕ}
    {x : Fin n → ℝ} (hy : StrictAnti y) (hx : Realizes y mu x)
    (e : Interval n) (q : Fin d) (heq : x e.1.2 - x e.1.1 = y q) :
    (e.1.1.val + 1) * (n - e.1.2.val) ≤
        (∑ r ∈ Finset.univ.filter (· < q), mu r) + 1 ∧
    (∑ r ∈ Finset.univ.filter (· ≤ q), mu r) ≤
        n.choose 2 - (e.1.2.val - e.1.1.val + 1).choose 2 + 1 ∧
    RankAllowed mu e q := by
  classical
  let label : Interval n → Fin d := fun a => Classical.choose (hx.2.1 a)
  have label_spec (a : Interval n) : x a.1.2 - x a.1.1 = y (label a) :=
    Classical.choose_spec (hx.2.1 a)
  have fiber (r : Fin d) :
      (Finset.univ.filter fun a : Interval n => label a = r).card = mu r := by
    convert hx.2.2 r using 2
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [label_spec a]
    exact hy.injective.eq_iff.symm
  have cdf (t : Finset (Fin d)) :
      (∑ r ∈ t, mu r) = (Finset.univ.filter fun a => label a ∈ t).card := by
    simp_rw [← fiber]
    exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
  have le_label : label e = q := hy.injective ((label_spec e).symm.trans heq)
  have upper_super :
      (e.1.1.val + 1) * (n - e.1.2.val) ≤
      (Finset.univ.filter fun a : Interval n => label a < q).card + 1 := by
    rw [← card_containing e]
    calc
      _ ≤ ((Finset.univ.filter fun a : Interval n => label a < q) ∪ {e}).card := by
        apply Finset.card_le_card
        intro a ha
        have h := (Finset.mem_filter.mp ha).2
        rcases containing_distance hx.1 e a h.1 h.2 with h | h
        · simp [h]
        · have hq : label a < q := hy.lt_iff_gt.mp (by
            rw [← label_spec a, ← heq]; exact h)
          simp [hq]
      _ ≤ _ := by
        simpa using (Finset.card_union_le
          (Finset.univ.filter fun a : Interval n => label a < q) {e})
  have upper_sub :
      (e.1.2.val - e.1.1.val + 1).choose 2 ≤
      (Finset.univ.filter fun a : Interval n => q < label a).card + 1 := by
    rw [← card_contained e]
    calc
      _ ≤ ((Finset.univ.filter fun a : Interval n => q < label a) ∪ {e}).card := by
        apply Finset.card_le_card
        intro a ha
        have h := (Finset.mem_filter.mp ha).2
        rcases containing_distance hx.1 a e h.1 h.2 with h | h
        · simp [h.symm]
        · have hq : q < label a := hy.lt_iff_gt.mp (by
            rw [← label_spec a, ← heq]; exact h)
          simp [hq]
      _ ≤ _ := by
        simpa using (Finset.card_union_le
          (Finset.univ.filter fun a : Interval n => q < label a) {e})
  have partition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Interval n))) (p := fun a => label a ≤ q)
  have total :
      (∑ r ∈ Finset.univ.filter (· ≤ q), mu r) +
      (Finset.univ.filter fun a : Interval n => q < label a).card = n.choose 2 := by
    simpa [cdf, card_intervals, not_le] using partition
  have lo : (e.1.1.val + 1) * (n - e.1.2.val) ≤
      (∑ r ∈ Finset.univ.filter (· < q), mu r) + 1 := by
    simpa only [cdf, Finset.mem_filter, Finset.mem_univ, true_and] using upper_super
  have hi : (∑ r ∈ Finset.univ.filter (· ≤ q), mu r) ≤
      n.choose 2 - (e.1.2.val - e.1.1.val + 1).choose 2 + 1 := by omega
  have positive : 0 < mu q := by
    rw [← fiber q]
    exact Finset.card_pos.mpr ⟨e, by simp [le_label]⟩
  have block : (∑ r ∈ Finset.univ.filter (· < q), mu r) + 1 ≤
      ∑ r ∈ Finset.univ.filter (· ≤ q), mu r := by
    have split : Finset.univ.filter (· ≤ q) =
        insert q (Finset.univ.filter (· < q)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      exact le_iff_lt_or_eq.trans or_comm
    rw [split, Finset.sum_insert (by simp)]
    omega
  exact ⟨lo, hi, le_trans lo block, le_trans block hi⟩

end
end Omega.Turnpike
