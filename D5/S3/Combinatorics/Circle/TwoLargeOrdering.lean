/- GID: D5/S3/Combinatorics/Circle/TwoLargeOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoLargeOrdering
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [D5/S3/Combinatorics/Circle/SourceWidth]
   utility: none
   digest: Conservation completes zero-sum rows with one large occurrence per sign. -/
import D5.S3.Combinatorics.Circle.SourceWidth

/-! # Complete strip orderings with at most one large occurrence of either sign -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoLargeOrdering

open SourceWidth

/-- After retiring the large positive, conservation prevents a dead end. -/
private theorem complete_small_positives {n : ℕ} (f : Fin n → ℤ) (B : ℤ)
    (fuel : ℕ) (labels : List (Fin n)) (H : ℤ)
    (hlen : labels.length ≤ fuel) (hnd : labels.Nodup)
    (hh : 0 ≤ H ∧ H ≤ B) (hsum : H + (labels.map f).sum = 0)
    (hbound : ∀ x ∈ labels, |f x| ≤ B)
    (hsmall : ∀ x ∈ labels, 2 * f x ≤ B)
    (hneg : ∀ x ∈ labels, ∀ y ∈ labels,
      B < -2 * f x → B < -2 * f y → x = y) :
    ∃ word : List (Fin n), word.Perm labels ∧ InStrip f B H word := by
  induction fuel generalizing labels H with
  | zero =>
    have he : labels = [] := List.length_eq_zero_iff.mp (by omega)
    subst labels
    exact ⟨[], .refl _, hh⟩
  | succ fuel ih =>
    by_cases hpos : ∃ p ∈ labels, 0 < f p
    · obtain ⟨p, hp, hp0⟩ := hpos
      have hstep : ∃ x ∈ labels, 0 ≤ H + f x ∧ H + f x ≤ B := by
        by_cases hfit : ∃ q ∈ labels, f q < 0 ∧ 0 ≤ H + f q
        · obtain ⟨q, hq, hq0, hqfit⟩ := hfit
          exact ⟨q, hq, hqfit, by omega⟩
        · refine ⟨p, hp, by omega, ?_⟩
          by_contra hover
          have hhalf := hsmall p hp
          have hH : B < 2 * H := by omega
          have hlarge : ∀ q ∈ labels, f q < 0 → B < -2 * f q := by
            intro q hq hq0
            have hnfit : ¬ 0 ≤ H + f q := fun h => hfit ⟨q, hq, hq0, h⟩
            omega
          have hex : ∃ q ∈ labels, f q < 0 := by
            by_contra hn
            have hnneg : ∀ q ∈ labels, 0 ≤ f q := by
              intro q hq
              by_contra hq0
              exact hn ⟨q, hq, by omega⟩
            have hle : f p ≤ (labels.map f).sum :=
              List.single_le_sum (by simpa using hnneg) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
            omega
          obtain ⟨q, hq, hq0⟩ := hex
          have hrest : ∀ x ∈ labels.erase q, 0 ≤ f x := by
            intro x hx
            obtain ⟨hxq, hxl⟩ := hnd.mem_erase_iff.mp hx
            by_contra hx0
            exact hxq (hneg x hxl q hq (hlarge x hxl (by omega)) (hlarge q hq hq0))
          have hpq : p ≠ q := by intro he; subst p; omega
          have hp' : p ∈ labels.erase q := hnd.mem_erase_iff.mpr ⟨hpq, hp⟩
          have hle : f p ≤ ((labels.erase q).map f).sum :=
            List.single_le_sum (by simpa using hrest) _ (List.mem_map.mpr ⟨p, hp', rfl⟩)
          have he := ((List.perm_cons_erase hq).map f).sum_eq
          simp only [List.map_cons, List.sum_cons] at he
          have hqbound := (abs_le.mp (hbound q hq)).1
          omega
      obtain ⟨x, hx, hxlo, hxhi⟩ := hstep
      have he := ((List.perm_cons_erase hx).map f).sum_eq
      simp only [List.map_cons, List.sum_cons] at he
      have hlen' := List.length_erase_add_one hx
      obtain ⟨word, hw, hs⟩ := ih (labels.erase x) (H + f x) (by omega)
        (hnd.erase x) ⟨hxlo, hxhi⟩ (by omega)
        (fun y hy => hbound y (List.mem_of_mem_erase hy))
        (fun y hy => hsmall y (List.mem_of_mem_erase hy))
        (fun y hy z hz => hneg y (List.mem_of_mem_erase hy) z (List.mem_of_mem_erase hz))
      exact ⟨x :: word, (hw.cons x).trans (List.perm_cons_erase hx).symm,
        hh.1, hh.2, hs⟩
    · have hnonpos : ∀ x ∈ labels, f x ≤ 0 := by
        intro x hx
        by_contra hx0
        exact hpos ⟨x, hx, by omega⟩
      exact ⟨labels, .refl _, inStrip_nonpos hnonpos hh.2 (by omega)⟩

/-- A complete permutation of physical labels stays in the closed strip [0,B].
The strict doubled thresholds count labels, including equal-valued occurrences. -/
theorem exists_order {n : ℕ} (f : Fin n → ℤ) (labels : List (Fin n)) (B : ℤ)
    (hnd : labels.Nodup) (hB : 0 ≤ B) (hsum : (labels.map f).sum = 0)
    (hbound : ∀ x ∈ labels, |f x| ≤ B)
    (hpos : ∀ x ∈ labels, ∀ y ∈ labels,
      B < 2 * f x → B < 2 * f y → x = y)
    (hneg : ∀ x ∈ labels, ∀ y ∈ labels,
      B < -2 * f x → B < -2 * f y → x = y) :
    ∃ word : List (Fin n), word.Perm labels ∧ InStrip f B 0 word := by
  by_cases hlarge : ∃ p ∈ labels, B < 2 * f p
  · obtain ⟨p, hp, hplarge⟩ := hlarge
    have hpbound := abs_le.mp (hbound p hp)
    have he := ((List.perm_cons_erase hp).map f).sum_eq
    simp only [List.map_cons, List.sum_cons] at he
    have hsmall : ∀ x ∈ labels.erase p, 2 * f x ≤ B := by
      intro x hx
      obtain ⟨hxp, hxl⟩ := hnd.mem_erase_iff.mp hx
      by_contra hxlarge
      exact hxp (hpos x hxl p hp (by omega) hplarge)
    obtain ⟨word, hw, hs⟩ := complete_small_positives f B
      (labels.erase p).length (labels.erase p) (f p) (le_refl _) (hnd.erase p)
      ⟨by omega, hpbound.2⟩ (by omega)
      (fun x hx => hbound x (List.mem_of_mem_erase hx)) hsmall
      (fun x hx y hy => hneg x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy))
    refine ⟨p :: word, (hw.cons p).trans (List.perm_cons_erase hp).symm, ?_⟩
    simpa only [InStrip, zero_add] using And.intro (le_refl (0 : ℤ)) (And.intro hB hs)
  · apply complete_small_positives f B labels.length labels 0 (le_refl _) hnd
      ⟨le_refl _, hB⟩ (by omega) hbound ?_ hneg
    intro x hx
    by_contra hxlarge
    exact hlarge ⟨x, hx, by omega⟩

end D5.S3.Combinatorics.Circle.TwoLargeOrdering
