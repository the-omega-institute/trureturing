/- GID: D5/S3/Combinatorics/Circle/SmallStepOrdering
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SmallStepOrdering
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.List]
   utility: none
   digest: Pairwise compatible opposite steps can be permuted between any two legal endpoints. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Data.List.Perm.Basic

/-! # Ordering compatible integer steps between arbitrary legal endpoints

The list carries all occurrences, including repetitions. Pairwise compatibility
of positive and negative steps prevents a dead end inside the closed strip. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SmallStepOrdering
open SourceWidth

private theorem complete_between {α : Type*} (f : α → ℤ) (C : ℤ)
    (fuel : ℕ) (labels : List α) (h : ℤ)
    (hlen : labels.length ≤ fuel)
    (hstart : 0 ≤ h ∧ h ≤ C)
    (hend : 0 ≤ h + (labels.map f).sum ∧ h + (labels.map f).sum ≤ C)
    (hcompatible : ∀ p ∈ labels, ∀ n ∈ labels,
      0 < f p → f n < 0 → f p - f n ≤ C) :
    ∃ word : List α, word.Perm labels ∧ InStrip f C h word := by
  classical
  induction fuel generalizing labels h with
  | zero =>
    have hempty : labels = [] := List.length_eq_zero_iff.mp (by omega)
    subst labels
    exact ⟨[], .refl _, hstart⟩
  | succ fuel ih =>
    by_cases hpos : ∃ p ∈ labels, 0 < f p
    · obtain ⟨p, hp, hp0⟩ := hpos
      have hstep : ∃ q ∈ labels, 0 ≤ h + f q ∧ h + f q ≤ C := by
        by_cases hfit : ∃ n ∈ labels, f n < 0 ∧ 0 ≤ h + f n
        · obtain ⟨n, hn, hn0, hnfit⟩ := hfit
          exact ⟨n, hn, hnfit, by omega⟩
        · refine ⟨p, hp, by omega, ?_⟩
          by_contra hover
          have hexneg : ∃ n ∈ labels, f n < 0 := by
            by_contra hn
            have hnonneg : ∀ n ∈ labels, 0 ≤ f n := by
              intro n hnmem
              by_contra hn0
              exact hn ⟨n, hnmem, by omega⟩
            have hle : f p ≤ (labels.map f).sum :=
              List.single_le_sum (by simpa using hnonneg) _
                (List.mem_map.mpr ⟨p, hp, rfl⟩)
            omega
          obtain ⟨n, hn, hn0⟩ := hexneg
          have hnfail : ¬ 0 ≤ h + f n := fun hnfit => hfit ⟨n, hn, hn0, hnfit⟩
          have hcross := hcompatible p hp n hn hp0 hn0
          omega
      obtain ⟨q, hq, hqlo, hqhi⟩ := hstep
      have he := ((List.perm_cons_erase hq).map f).sum_eq
      simp only [List.map_cons, List.sum_cons] at he
      have hlen' := List.length_erase_add_one hq
      obtain ⟨word, hw, hs⟩ := ih (labels.erase q) (h + f q) (by omega)
        ⟨hqlo, hqhi⟩ (by constructor <;> omega)
        (fun p hp n hn => hcompatible p (List.mem_of_mem_erase hp)
          n (List.mem_of_mem_erase hn))
      exact ⟨q :: word, (hw.cons q).trans (List.perm_cons_erase hq).symm,
        hstart.1, hstart.2, hs⟩
    · have hnonpos : ∀ q ∈ labels, f q ≤ 0 := by
        intro q hq
        by_contra hq0
        exact hpos ⟨q, hq, by omega⟩
      exact ⟨labels, .refl _, inStrip_nonpos hnonpos hstart.2 hend.1⟩

/-- Opposite steps whose combined magnitudes fit C can always be ordered
between any prescribed legal start and the resulting legal endpoint.
Repeated labels and equal-valued distinct occurrences are preserved by Perm. -/
theorem exists_order_between {α : Type*} (f : α → ℤ) (labels : List α) (C h : ℤ)
    (hstart : 0 ≤ h ∧ h ≤ C)
    (hend : 0 ≤ h + (labels.map f).sum ∧ h + (labels.map f).sum ≤ C)
    (hcompatible : ∀ p ∈ labels, ∀ n ∈ labels,
      0 < f p → f n < 0 → f p - f n ≤ C) :
    ∃ word : List α, word.Perm labels ∧ InStrip f C h word := by
  exact complete_between f C labels.length labels h (le_refl _) hstart hend hcompatible

end D5.S3.Combinatorics.Circle.SmallStepOrdering
