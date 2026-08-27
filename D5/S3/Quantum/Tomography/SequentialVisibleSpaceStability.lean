/- GID: D5/S3/Quantum/Tomography/SequentialVisibleSpaceStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/SequentialVisibleSpaceStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A stable sequential word-effect span remains permanently stable. -/

import D5.S3.Quantum.Completion.SequentialWordObservationResidual

/- Library-search audit trail (2026-08-27):
   * Exact family hit `sequentialWordEffect` is the canonical source-order fold
     of branch dual maps on the full real Hermitian carrier and is reused.
   * The centered-effect and operator-system permanent-stability theorems each
     use one map and a different recursive carrier, so neither is an exact hit
     for the source's family-indexed sequential word effects.
   * Pinned Mathlib hits `Submodule.span_induction`, `Submodule.span_le`, and
     `Submodule.subset_span` supply the invariant-span and inclusion steps.
     Searches found no exact bounded action-word span permanence theorem.
   * Body-shape searches for `List.foldr`, instrument duals, and bounded word
     spans found the imported word-effect primitive and no existing visible-span
     definition. No new `def` or `abbrev` is introduced. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.SequentialVisibleSpaceStability

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Completion.SequentialWordObservationResidual

variable {d : Nat}

/-- Once two consecutive real spans of bounded sequential word effects agree,
every later bounded word-effect span is the same subspace. -/
theorem sequential_visible_space_once_stable_permanently
    {Alphabet : Type*}
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (n : Nat)
    (hStable :
      Submodule.span ℝ {effect | ∃ word : List Alphabet,
        word.length ≤ n + 1 ∧
          effect = sequentialWordEffect instrumentDual word} =
      Submodule.span ℝ {effect | ∃ word : List Alphabet,
        word.length ≤ n ∧
          effect = sequentialWordEffect instrumentDual word}) :
    ∀ m : Nat, n ≤ m →
      Submodule.span ℝ {effect | ∃ word : List Alphabet,
        word.length ≤ m ∧
          effect = sequentialWordEffect instrumentDual word} =
      Submodule.span ℝ {effect | ∃ word : List Alphabet,
        word.length ≤ n ∧
          effect = sequentialWordEffect instrumentDual word} := by
  let visible (bound : Nat) : Submodule ℝ (HermitianSpace d) :=
    Submodule.span ℝ {effect | ∃ word : List Alphabet,
      word.length ≤ bound ∧
        effect = sequentialWordEffect instrumentDual word}
  have hStable' : visible (n + 1) = visible n := by
    simpa only [visible] using hStable
  have hmap (generator : Alphabet) :
      ∀ effect ∈ visible n, instrumentDual generator effect ∈ visible n := by
    intro effect heffect
    refine Submodule.span_induction
      (p := fun effect _ => instrumentDual generator effect ∈ visible n)
      ?_ ?_ ?_ ?_ heffect
    · rintro effect ⟨word, hlength, rfl⟩
      have hnext :
          sequentialWordEffect instrumentDual (generator :: word) ∈
            visible (n + 1) := by
        apply Submodule.subset_span
        refine ⟨generator :: word, ?_, rfl⟩
        simpa only [List.length_cons, Nat.succ_eq_add_one] using
          Nat.add_le_add_right hlength 1
      rw [hStable'] at hnext
      exact hnext
    · simpa only [map_zero] using (Submodule.zero_mem (visible n))
    · intro first second _ _ hfirst hsecond
      simpa only [map_add] using Submodule.add_mem (visible n) hfirst hsecond
    · intro scalar effect _ heffect
      simpa only [map_smul] using Submodule.smul_mem (visible n) scalar heffect
  have allWords : ∀ word : List Alphabet,
      sequentialWordEffect instrumentDual word ∈ visible n := by
    intro word
    induction word with
    | nil =>
        apply Submodule.subset_span
        exact ⟨[], Nat.zero_le n, rfl⟩
    | cons generator word inductionHypothesis =>
        change instrumentDual generator
          (sequentialWordEffect instrumentDual word) ∈ visible n
        exact hmap generator _ inductionHypothesis
  change ∀ m : Nat, n ≤ m → visible m = visible n
  intro m hnm
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro effect ⟨word, _, rfl⟩
    exact allWords word
  · apply Submodule.span_le.2
    rintro effect ⟨word, hlength, rfl⟩
    apply Submodule.subset_span
    exact ⟨word, hlength.trans hnm, rfl⟩

#print axioms sequential_visible_space_once_stable_permanently

end D5.S3.Quantum.Tomography.SequentialVisibleSpaceStability
