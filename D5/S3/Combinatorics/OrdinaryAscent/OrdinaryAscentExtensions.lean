/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions
   mirror-E: none(waiver:literal-ordinary-avoider-unique-parent)
   anchors: []
   utility: none
   digest: Actual ordinary avoiders of any literal pattern set have a unique legal one-letter parent. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentSemantics

/-! The shared ordinary-ascent and literal adjacent-pair predicates give the
unique-parent decomposition for every subset of the thirteen patterns, including
the empty root. This supplies an actual-object interface for subsequent refined
generating-tree arguments; it does not identify any two pattern classes. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentExtensions

open OrdinaryAscentSemantics
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)

/-- The exact ascent bound and all new literal occurrences at the appended letter. -/
def CanAppend (B : Finset Pattern) (w : List ℕ) (x : ℕ) : Prop :=
  x ≤ (if w = [] then 0 else 1 + asc w) ∧
    ∀ p ∈ B, ∀ i, i + 1 < w.length →
      ¬ Fits p (w.getD i 0) (w.getD (i + 1) 0) x

/-- Exact one-letter admission, uniformly in the literal pattern set and the root. -/
theorem append_avoiders_iff (n : ℕ) (B : Finset Pattern) (w : List ℕ) (x : ℕ) :
    w ++ [x] ∈ avoiders (n + 1) B ↔ w ∈ avoiders n B ∧ CanAppend B w x := by
  constructor
  · rintro ⟨hl, ha, hb⟩
    obtain ⟨hp, hx⟩ := (ascent_append_iff w x).mp ha
    refine ⟨⟨by simpa using hl, hp, ?_⟩, hx, ?_⟩
    · intro p hpb hc
      exact hb p hpb ((contains_append_iff p w x).mpr (Or.inl hc))
    · intro p hpb i hi hf
      exact hb p hpb ((contains_append_iff p w x).mpr (Or.inr ⟨i, hi, hf⟩))
  · rintro ⟨⟨hl, ha, hb⟩, hx, hs⟩
    refine ⟨by simpa [hl], (ascent_append_iff w x).mpr ⟨ha, hx⟩, ?_⟩
    intro p hpb hc
    rcases (contains_append_iff p w x).mp hc with hc | ⟨i, hi, hf⟩
    · exact hb p hpb hc
    · exact hs p hpb i hi hf

private theorem take_append_last (n : ℕ) (w : List ℕ) (hl : w.length = n + 1) :
    w.take n ++ [w.getD n 0] = w := by
  have hi : n < w.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.take_append_getElem hi]
  simp [← hl]

/-- Removing the final letter preserves the actual class and records exact admission. -/
theorem parent_admission (n : ℕ) (B : Finset Pattern)
    (w : avoiders (n + 1) B) :
    w.val.take n ∈ avoiders n B ∧ CanAppend B (w.val.take n) (w.val.getD n 0) := by
  apply (append_avoiders_iff n B _ _).mp
  rw [take_append_last n w.val w.property.1]
  exact w.property

/-- Every actual nonempty avoider is uniquely a legal one-letter child of an
actual parent. The inverse is literal concatenation; no tree label is assumed. -/
def extensionEquiv (n : ℕ) (B : Finset Pattern) :
    (avoiders (n + 1) B) ≃
      (Σ w : avoiders n B, {x : ℕ // CanAppend B w.val x}) where
  toFun w := ⟨⟨w.val.take n, (parent_admission n B w).1⟩,
    ⟨w.val.getD n 0, (parent_admission n B w).2⟩⟩
  invFun v := ⟨v.1.val ++ [v.2.val],
    (append_avoiders_iff n B _ _).mpr ⟨v.1.property, v.2.property⟩⟩
  left_inv w := Subtype.ext (take_append_last n w.val w.property.1)
  right_inv v := by
    rcases v with ⟨⟨w, hw⟩, ⟨x, hx⟩⟩
    have hl : w.length = n := hw.1
    have ht : (w ++ [x]).take n = w := by rw [← hl]; simp
    have hg : (w ++ [x]).getD n 0 = x := by rw [← hl]; simp
    apply Sigma.ext (Subtype.ext ht)
    exact (Subtype.heq_iff_coe_eq (by intro z; simp only [ht])).mpr hg

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentExtensions
