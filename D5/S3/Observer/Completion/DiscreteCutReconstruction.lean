/- GID: D5/S3/Observer/Completion/DiscreteCutReconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/DiscreteCutReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational cuts reconstruct reals; finite subfamilies remain nonidentifying. -/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 name and body-shape searches for rational threshold cuts, Boolean
     profiles, supremum reconstruction, and finite-cut nonidentification found
     no definition or theorem with this source construction.
   * Pinned Mathlib has no whole-statement rational-cut reconstruction theorem.
     Its exact constituents `exists_rat_btwn` and `IsLUB.csSup_eq` are applied
     below for rational density and conditional-completeness reconstruction.
   * Reachable GitHub Lean-code searches for rational density with cut
     reconstruction found uses of `exists_rat_btwn`, but no exact theorem or
     admissible port candidate covering the finite-family and compatibility
     clauses together. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace D5.S3.Observer.Completion.DiscreteCutReconstruction

/-- The Boolean threshold names at all rational cuts reconstruct `x` as their
supremum. No single cut or finite family identifies `x`: a distinct nearby real
has the same selected readouts. The final conjuncts expose the downward-true
and upward-false compatibility laws of the complete rational profile. -/
theorem discrete_cut_reconstruction (x : ℝ) :
    sSup {z : ℝ | ∃ q : ℚ,
      z = (q : ℝ) ∧ decide ((q : ℝ) < x) = true} = x ∧
      (∀ q : ℚ, ∃ y : ℝ,
        y ≠ x ∧ decide ((q : ℝ) < x) = decide ((q : ℝ) < y)) ∧
      (∀ cuts : Finset ℚ, ∃ y : ℝ,
        y ≠ x ∧ ∀ q ∈ cuts,
          decide ((q : ℝ) < x) = decide ((q : ℝ) < y)) ∧
      (∀ p q : ℚ, p ≤ q →
        (decide ((q : ℝ) < x) = true →
          decide ((p : ℝ) < x) = true) ∧
        (decide ((p : ℝ) < x) = false →
          decide ((q : ℝ) < x) = false)) := by
  have cutIsLUB : IsLUB
      {z : ℝ | ∃ q : ℚ, z = (q : ℝ) ∧ decide ((q : ℝ) < x) = true} x := by
    constructor
    · rintro z ⟨q, rfl, hqx⟩
      exact (of_decide_eq_true hqx).le
    · intro upper hUpper
      by_contra hxUpper
      have hUpperX : upper < x := lt_of_not_ge hxUpper
      obtain ⟨q, hUpperQ, hqx⟩ := exists_rat_btwn hUpperX
      have hqMem : (q : ℝ) ∈
          {z : ℝ | ∃ r : ℚ, z = (r : ℝ) ∧ decide ((r : ℝ) < x) = true} :=
        ⟨q, rfl, by simp [hqx]⟩
      exact (not_le_of_gt hUpperQ) (hUpper hqMem)
  have cutNonempty :
      {z : ℝ | ∃ q : ℚ, z = (q : ℝ) ∧
        decide ((q : ℝ) < x) = true}.Nonempty := by
    obtain ⟨q, -, hqx⟩ := exists_rat_btwn (sub_one_lt x)
    exact ⟨(q : ℝ), q, rfl, by simp [hqx]⟩
  have reconstruction :
      sSup {z : ℝ | ∃ q : ℚ, z = (q : ℝ) ∧
        decide ((q : ℝ) < x) = true} = x :=
    cutIsLUB.csSup_eq cutNonempty
  have finiteIndeterminacy : ∀ cuts : Finset ℚ, ∃ y : ℝ,
      y ≠ x ∧ ∀ q ∈ cuts,
        decide ((q : ℝ) < x) = decide ((q : ℝ) < y) := by
    classical
    intro cuts
    let lower : Finset ℚ := cuts.filter fun (q : ℚ) => (q : ℝ) < x
    by_cases hLower : lower.Nonempty
    · let m := lower.max' hLower
      let y : ℝ := ((m : ℝ) + x) / 2
      have hmMem : m ∈ lower := Finset.max'_mem lower hLower
      have hmX : (m : ℝ) < x := (Finset.mem_filter.mp hmMem).2
      have hyX : y < x := by
        dsimp [y]
        linarith
      have hmY : (m : ℝ) < y := by
        dsimp [y]
        linarith
      refine ⟨y, ne_of_lt hyX, ?_⟩
      intro q hqCuts
      by_cases hqx : (q : ℝ) < x
      · have hqLower : q ∈ lower := Finset.mem_filter.mpr ⟨hqCuts, hqx⟩
        have hqm : q ≤ m := Finset.le_max' lower q hqLower
        have hqy : (q : ℝ) < y := (Rat.cast_le.2 hqm).trans_lt hmY
        simp [hqx, hqy]
      · have hxq : x ≤ (q : ℝ) := le_of_not_gt hqx
        have hqy : ¬ (q : ℝ) < y := not_lt_of_ge (hyX.le.trans hxq)
        simp [hqx, hqy]
    · let y : ℝ := x - 1
      have hyX : y < x := by
        dsimp [y]
        linarith
      refine ⟨y, ne_of_lt hyX, ?_⟩
      intro q hqCuts
      have hqx : ¬ (q : ℝ) < x := by
        intro hqx
        apply hLower
        exact ⟨q, Finset.mem_filter.mpr ⟨hqCuts, hqx⟩⟩
      have hxq : x ≤ (q : ℝ) := le_of_not_gt hqx
      have hqy : ¬ (q : ℝ) < y := not_lt_of_ge (hyX.le.trans hxq)
      simp [hqx, hqy]
  refine ⟨reconstruction, ?_, finiteIndeterminacy, ?_⟩
  · intro q
    obtain ⟨y, hy, hnames⟩ := finiteIndeterminacy {q}
    exact ⟨y, hy, hnames q (by simp)⟩
  · intro p q hpq
    have hpqReal : (p : ℝ) ≤ (q : ℝ) := Rat.cast_le.2 hpq
    constructor
    · intro hq
      exact decide_eq_true (hpqReal.trans_lt (of_decide_eq_true hq))
    · intro hp
      apply decide_eq_false
      intro hqx
      exact (of_decide_eq_false hp) (hpqReal.trans_lt hqx)

-- The source carrier is inhabited independently of the theorem conclusion.
example : Nonempty ℝ := ⟨0⟩

#print axioms discrete_cut_reconstruction

end D5.S3.Observer.Completion.DiscreteCutReconstruction
