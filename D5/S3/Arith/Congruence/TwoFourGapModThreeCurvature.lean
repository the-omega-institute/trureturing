/- GID: D5/S3/Arith/Congruence/TwoFourGapModThreeCurvature
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TwoFourGapModThreeCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-four gaps omit a residue modulo three exactly at nonzero adjacent curvatures. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.TwoFourGapModThreeCurvature

private theorem local_curvature_classification
    (points : List ℤ)
    (hdense : ∀ (i : ℕ) (hi : i + 1 < points.length),
      points[i + 1] - points[i] = 2 ∨ points[i + 1] - points[i] = 4)
    (i : ℕ) (hi : i + 2 < points.length) :
    ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = 0) ↔
        (points[i + 1] - points[i] = points[i + 2] - points[i + 1] ∧
          ∀ residue : ZMod 3,
            (points[i] : ZMod 3) = residue ∨
              (points[i + 1] : ZMod 3) = residue ∨
              (points[i + 2] : ZMod 3) = residue)) ∧
      ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = 1) ↔
        (points[i + 1] - points[i] = 2 ∧
          points[i + 2] - points[i + 1] = 4 ∧
          ∃ omitted : ZMod 3,
            (points[i] : ZMod 3) ≠ omitted ∧
              (points[i + 1] : ZMod 3) ≠ omitted ∧
              (points[i + 2] : ZMod 3) ≠ omitted)) ∧
      ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = -1) ↔
        (points[i + 1] - points[i] = 4 ∧
          points[i + 2] - points[i + 1] = 2 ∧
          ∃ omitted : ZMod 3,
            (points[i] : ZMod 3) ≠ omitted ∧
              (points[i + 1] : ZMod 3) ≠ omitted ∧
              (points[i + 2] : ZMod 3) ≠ omitted)) := by
  have hfirst := hdense i (by omega)
  have hsecond := hdense (i + 1) (by simpa [Nat.add_assoc] using hi)
  rcases hfirst with hfirst | hfirst <;>
      rcases hsecond with hsecond | hsecond
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 2 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 2 := by
      linear_combination hcast'
    have hcover : ∀ residue : ZMod 3,
        (points[i] : ZMod 3) = residue ∨
          (points[i + 1] : ZMod 3) = residue ∨
          (points[i + 2] : ZMod 3) = residue := by
      intro residue
      have hall : ∀ x r : ZMod 3, x = r ∨ x + 2 = r ∨ x + 2 + 2 = r := by decide
      rcases hall (points[i] : ZMod 3) residue with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hp1.trans h))
      · exact Or.inr (Or.inr (by rw [hp2, hp1]; exact h))
    have hnoomit : ¬ ∃ omitted : ZMod 3,
        (points[i] : ZMod 3) ≠ omitted ∧
          (points[i + 1] : ZMod 3) ≠ omitted ∧
          (points[i + 2] : ZMod 3) ≠ omitted := by
      rintro ⟨omitted, h0, h1, h2⟩
      rcases hcover omitted with h | h | h
      · exact h0 h
      · exact h1 h
      · exact h2 h
    norm_num [hfirst, hsecond, hcover, hnoomit]
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 2 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 4 := by
      linear_combination hcast'
    have homit : ∃ omitted : ZMod 3,
        (points[i] : ZMod 3) ≠ omitted ∧
          (points[i + 1] : ZMod 3) ≠ omitted ∧
          (points[i + 2] : ZMod 3) ≠ omitted := by
      refine ⟨(points[i] : ZMod 3) + 1, ?_⟩
      have h0 : ∀ x : ZMod 3, x ≠ x + 1 := by decide
      have h1 : ∀ x : ZMod 3, x + 2 ≠ x + 1 := by decide
      have h2 : ∀ x : ZMod 3, x + 2 + 4 ≠ x + 1 := by decide
      exact ⟨h0 _, by simpa [hp1] using h1 (points[i] : ZMod 3),
        by rw [hp2, hp1]; exact h2 _⟩
    norm_num [hfirst, hsecond, homit]
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 4 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 2 := by
      linear_combination hcast'
    have homit : ∃ omitted : ZMod 3,
        (points[i] : ZMod 3) ≠ omitted ∧
          (points[i + 1] : ZMod 3) ≠ omitted ∧
          (points[i + 2] : ZMod 3) ≠ omitted := by
      refine ⟨(points[i] : ZMod 3) + 2, ?_⟩
      have h0 : ∀ x : ZMod 3, x ≠ x + 2 := by decide
      have h1 : ∀ x : ZMod 3, x + 4 ≠ x + 2 := by decide
      have h2 : ∀ x : ZMod 3, x + 4 + 2 ≠ x + 2 := by decide
      exact ⟨h0 _, by simpa [hp1] using h1 (points[i] : ZMod 3),
        by rw [hp2, hp1]; exact h2 _⟩
    norm_num [hfirst, hsecond, homit]
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 4 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 4 := by
      linear_combination hcast'
    have hcover : ∀ residue : ZMod 3,
        (points[i] : ZMod 3) = residue ∨
          (points[i + 1] : ZMod 3) = residue ∨
          (points[i + 2] : ZMod 3) = residue := by
      intro residue
      have hall : ∀ x r : ZMod 3, x = r ∨ x + 4 = r ∨ x + 4 + 4 = r := by decide
      rcases hall (points[i] : ZMod 3) residue with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hp1.trans h))
      · exact Or.inr (Or.inr (by rw [hp2, hp1]; exact h))
    have hnoomit : ¬ ∃ omitted : ZMod 3,
        (points[i] : ZMod 3) ≠ omitted ∧
          (points[i + 1] : ZMod 3) ≠ omitted ∧
          (points[i + 2] : ZMod 3) ≠ omitted := by
      rintro ⟨omitted, h0, h1, h2⟩
      rcases hcover omitted with h | h | h
      · exact h0 h
      · exact h1 h
      · exact h2 h
    norm_num [hfirst, hsecond, hcover, hnoomit]

private theorem residues_repeat_after_two
    (points : List ℤ)
    (hdense : ∀ (i : ℕ) (hi : i + 1 < points.length),
      points[i + 1] - points[i] = 2 ∨ points[i + 1] - points[i] = 4)
    (hcurvature : ∀ (i : ℕ) (hi : i + 2 < points.length),
      ((points[i + 2] - points[i + 1]) / 2 - 1) -
        ((points[i + 1] - points[i]) / 2 - 1) ≠ 0)
    (i : ℕ) (hi : i + 2 < points.length) :
    (points[i + 2] : ZMod 3) = (points[i] : ZMod 3) := by
  have hfirst := hdense i (by omega)
  have hsecond := hdense (i + 1) (by simpa [Nat.add_assoc] using hi)
  have hturn := hcurvature i hi
  rcases hfirst with hfirst | hfirst <;>
      rcases hsecond with hsecond | hsecond
  · norm_num [hfirst, hsecond] at hturn
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 2 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 4 := by
      linear_combination hcast'
    rw [hp2, hp1]
    exact (by decide : ∀ x : ZMod 3, x + 2 + 4 = x) _
  · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hfirst
    have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hsecond
    push_cast at hcast hcast'
    have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 4 := by
      linear_combination hcast
    have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 2 := by
      linear_combination hcast'
    rw [hp2, hp1]
    exact (by decide : ∀ x : ZMod 3, x + 4 + 2 = x) _
  · norm_num [hfirst, hsecond] at hturn

private theorem every_residue_is_first_or_second
    (points : List ℤ)
    (hsize : 2 ≤ points.length)
    (hrepeat : ∀ (i : ℕ) (hi : i + 2 < points.length),
      (points[i + 2] : ZMod 3) = (points[i] : ZMod 3))
    (i : ℕ) (hi : i < points.length) :
    (points[i] : ZMod 3) = (points[0] : ZMod 3) ∨
      (points[i] : ZMod 3) = (points[1] : ZMod 3) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hi0 : i = 0
      · left
        subst i
        rfl
      by_cases hi1 : i = 1
      · right
        subst i
        rfl
      have hi2 : 2 ≤ i := by omega
      have hsub : i - 2 + 2 = i := by omega
      have hpreviousBound : i - 2 < points.length := by omega
      have hprevious := ih (i - 2) (by omega) hpreviousBound
      have hstep := hrepeat (i - 2) (by omega)
      have hstep' : (points[i] : ZMod 3) = (points[i - 2] : ZMod 3) := by
        simpa [hsub] using hstep
      rcases hprevious with hprevious | hprevious
      · exact Or.inl (hstep'.trans hprevious)
      · exact Or.inr (hstep'.trans hprevious)

/-- For a finite integer constellation with every consecutive gap equal to two or four,
omitting one residue modulo three is equivalent to nonzero normalized adjacent-gap curvature.
At each local turn, zero curvature is exactly an equal-gap triple covering all residues, while
curvatures plus and minus one are the two unequal-gap turns and each omits a residue. -/
theorem two_four_gap_mod_three_admissible_iff
    (points : List ℤ)
    (hdense : ∀ (i : ℕ) (hi : i + 1 < points.length),
      points[i + 1] - points[i] = 2 ∨ points[i + 1] - points[i] = 4) :
    (((∃ omitted : ZMod 3, ∀ (i : ℕ) (hi : i < points.length),
        (points[i] : ZMod 3) ≠ omitted) ↔
      ∀ (i : ℕ) (hi : i + 2 < points.length),
        ((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) ≠ 0) ∧
    ∀ (i : ℕ) (hi : i + 2 < points.length),
      ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = 0) ↔
        (points[i + 1] - points[i] = points[i + 2] - points[i + 1] ∧
          ∀ residue : ZMod 3,
            (points[i] : ZMod 3) = residue ∨
              (points[i + 1] : ZMod 3) = residue ∨
              (points[i + 2] : ZMod 3) = residue)) ∧
      ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = 1) ↔
        (points[i + 1] - points[i] = 2 ∧
          points[i + 2] - points[i + 1] = 4 ∧
          ∃ omitted : ZMod 3,
            (points[i] : ZMod 3) ≠ omitted ∧
              (points[i + 1] : ZMod 3) ≠ omitted ∧
              (points[i + 2] : ZMod 3) ≠ omitted)) ∧
      ((((points[i + 2] - points[i + 1]) / 2 - 1) -
          ((points[i + 1] - points[i]) / 2 - 1) = -1) ↔
        (points[i + 1] - points[i] = 4 ∧
          points[i + 2] - points[i + 1] = 2 ∧
          ∃ omitted : ZMod 3,
            (points[i] : ZMod 3) ≠ omitted ∧
              (points[i + 1] : ZMod 3) ≠ omitted ∧
              (points[i + 2] : ZMod 3) ≠ omitted))) := by
  refine ⟨?_, local_curvature_classification points hdense⟩
  constructor
  · rintro ⟨omitted, homitted⟩ i hi hzero
    have hlocal := (local_curvature_classification points hdense i hi).1.mp hzero
    rcases hlocal.2 omitted with h | h | h
    · exact homitted i (by omega) h
    · exact homitted (i + 1) (by omega) h
    · exact homitted (i + 2) hi h
  · intro hcurvature
    by_cases hsize : 2 ≤ points.length
    · have hrepeat := residues_repeat_after_two points hdense hcurvature
      have hdistinct : (points[0] : ZMod 3) ≠ (points[1] : ZMod 3) := by
        have hgap := hdense 0 (by omega)
        rcases hgap with hgap | hgap
        · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hgap
          push_cast at hcast
          have hp1 : (points[1] : ZMod 3) = (points[0] : ZMod 3) + 2 := by
            linear_combination hcast
          have hne : ∀ x : ZMod 3, x ≠ x + 2 := by decide
          intro heq
          exact hne _ (heq.trans hp1)
        · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hgap
          push_cast at hcast
          have hp1 : (points[1] : ZMod 3) = (points[0] : ZMod 3) + 4 := by
            linear_combination hcast
          have hne : ∀ x : ZMod 3, x ≠ x + 4 := by decide
          intro heq
          exact hne _ (heq.trans hp1)
      have hthird : ∀ x y : ZMod 3, x ≠ y →
          ∃ omitted : ZMod 3, x ≠ omitted ∧ y ≠ omitted := by decide
      obtain ⟨omitted, hfirst, hsecond⟩ :=
        hthird (points[0] : ZMod 3) (points[1] : ZMod 3) hdistinct
      refine ⟨omitted, ?_⟩
      intro i hi
      rcases every_residue_is_first_or_second points hsize hrepeat i hi with h | h
      · exact h.symm ▸ hfirst
      · exact h.symm ▸ hsecond
    · have hsmall : points.length = 0 ∨ points.length = 1 := by omega
      rcases hsmall with hzero | hone
      · refine ⟨0, ?_⟩
        intro i hi
        omega
      · have hne : ∀ x : ZMod 3, x ≠ x + 1 := by decide
        refine ⟨(points[0] : ZMod 3) + 1, ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        exact hne _

#print axioms two_four_gap_mod_three_admissible_iff

end D5.S3.Arith.Congruence.TwoFourGapModThreeCurvature
