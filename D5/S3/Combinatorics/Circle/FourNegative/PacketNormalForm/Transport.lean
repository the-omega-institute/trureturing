/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Transport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Transport
   mirror-E: none(waiver:consumed-packet-transport)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Positive packet symmetry and rightward transport of a literal ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! Endpoint-controlled transport along positive packets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem strip_append_iff {α : Type*} (f : α → ℤ) (B h : ℤ)
    (l r : List α) :
    InStrip f B h (l ++ r) ↔
      InStrip f B h l ∧ InStrip f B (h + (l.map f).sum) r := by
  induction l generalizing h with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.sum_nil, add_zero]
    constructor
    · intro hr
      have hh : 0 ≤ h ∧ h ≤ B := by
        cases r with
        | nil => exact hr
        | cons x xs => exact ⟨hr.1, hr.2.1⟩
      exact ⟨hh, hr⟩
    · exact And.right
  | cons x xs ih =>
    simp only [List.cons_append, InStrip, List.map_cons, List.sum_cons]
    rw [ih]
    constructor
    · rintro ⟨h0, hB, hl, hr⟩
      exact ⟨⟨h0, hB, hl⟩, by simpa [add_assoc] using hr⟩
    · rintro ⟨⟨h0, hB, hl⟩, hr⟩
      exact ⟨h0, hB, hl, by simpa [add_assoc] using hr⟩

private theorem strip_of_prefix {α : Type*} (f : α → ℤ) (B h : ℤ)
    (l : List α)
    (hp : ∀ n : ℕ, 0 ≤ h + ((l.take n).map f).sum ∧
      h + ((l.take n).map f).sum ≤ B) : InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using hp 0
  | cons x xs ih =>
    refine ⟨by simpa using (hp 0).1, by simpa using (hp 0).2, ih (h + f x) ?_⟩
    intro n
    simpa [List.take_succ_cons, add_assoc] using hp (n + 1)

/-- Moving the ear right across a nonnegative interval preserves every prefix. -/
private theorem slide_ear_right {α : Type*} (f : α → ℤ) (B h : ℤ)
    (ear : α) (pre pos post : List α)
    (he : 0 ≤ f ear) (hp : ∀ x ∈ pos, 0 ≤ f x)
    (hw : InStrip f B h (pre ++ ear :: (pos ++ post))) :
    InStrip f B h (pre ++ pos ++ ear :: post) := by
  obtain ⟨hpre, htail⟩ := (strip_append_iff f B h pre _).mp hw
  let H := h + (pre.map f).sum
  change InStrip f B H (ear :: (pos ++ post)) at htail
  obtain ⟨hpos, hpost⟩ := (strip_append_iff f B (H + f ear) pos post).mp htail.2.2
  have hend := inStrip_prefix hpos pos.length
  simp only [List.take_length] at hend
  have hH : 0 ≤ H := htail.1
  have hs : 0 ≤ (pos.map f).sum := by simpa using List.sum_le_sum hp
  have hpos' : InStrip f B H pos :=
    positive_block_strip hp htail.1 (by omega)
  have hear : InStrip f B (H + (pos.map f).sum) (ear :: post) := by
    refine ⟨by omega, by omega, ?_⟩
    convert hpost using 1 <;> ring
  rw [List.append_assoc]
  apply (strip_append_iff f B h pre _).mpr
  refine ⟨hpre, ?_⟩
  exact inStrip_append hpos' hear

private theorem last_nonpositive {α : Type*} (f : α → ℤ) (B : ℤ)
    (pre : List α) (x : α)
    (hw : InStrip f B 0 (pre ++ [x]))
    (hz : ((pre ++ [x]).map f).sum = 0) : f x ≤ 0 := by
  have hpre := ((strip_append_iff f B 0 pre [x]).mp hw).1
  have hh := (inStrip_prefix hpre pre.length).1
  simp only [List.take_length, zero_add] at hh
  simp only [List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton] at hz
  omega

private theorem ear_not_at_end {α : Type*} (f : α → ℤ) (B : ℤ)
    (pre : List α) (ear : α) (A : ℤ) (hA : 0 < A)
    (hz : (pre.map f).sum = -A)
    (hw : InStrip f B 0 (pre ++ [ear])) : False := by
  have hpre := ((strip_append_iff f B 0 pre [ear]).mp hw).1
  have hh := (inStrip_prefix hpre pre.length).1
  simp only [List.take_length, zero_add, hz] at hh
  omega

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
