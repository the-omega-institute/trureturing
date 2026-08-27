/- GID: D5/S3/Quantum/PredictionDepth/FiniteSequentialCompletenessDepth
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FiniteSequentialCompletenessDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite sequential word spans reach full Hermitian visibility. -/

import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate

/- Library-search audit trail (2026-08-27):
   * Exact family hits `sequentialWordEffect`, `centeredHermitianMap`, and
     `identityHermitian` provide the canonical instrument-word effect and the
     public bridge between full and trace-zero real Hermitian carriers.
   * The frozen `finite_sequential_word_certificate` theorem provides the
     centered bounded-depth certificate used in the carrier bridge.
   * Pinned Mathlib supplies supporting finite-dimensional span lemmas but has
     no exact theorem about completeness of bounded instrument words.
   * Body-shape searches found the imported family primitives and no competing
     definition. This module introduces no new `def` or `abbrev`. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.FiniteSequentialCompletenessDepth

open D5.S3.Quantum.Completion.SequentialWordObservationResidual
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate

private theorem hermitian_trace_eq_re {d : Nat} (effect : HermitianSpace d) :
    Matrix.trace effect.1 = ((Matrix.trace effect.1).re : ℂ) := by
  have heffectStar := effect.2
  change star effect.1 = effect.1 at heffectStar
  have heffect : effect.1ᴴ = effect.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using heffectStar
  have htraceStar : star (Matrix.trace effect.1) = Matrix.trace effect.1 := by
    calc
      star (Matrix.trace effect.1) = Matrix.trace effect.1ᴴ :=
        (Matrix.trace_conjTranspose effect.1).symm
      _ = Matrix.trace effect.1 := by rw [heffect]
  exact (Complex.conj_eq_iff_re.mp htraceStar).symm

private theorem centered_hermitian_map_coe (d : Nat) [NeZero d]
    (effect : HermitianSpace d) :
    (centeredHermitianMap d effect).1 =
      effect - ((Matrix.trace effect.1).re / d) • identityHermitian d := by
  apply Subtype.ext
  change centeredEffect effect.1 =
    effect.1 - (((Matrix.trace effect.1).re / d : ℝ) : ℂ) • 1
  rw [centeredEffect, hermitian_trace_eq_re effect]
  norm_num

private theorem centered_hermitian_map_fixed (d : Nat) [NeZero d]
    (effect : traceZeroHermitian d) :
    centeredHermitianMap d effect.1 = effect := by
  apply Subtype.ext
  apply Subtype.ext
  change centeredEffect effect.1.1 = effect.1.1
  rw [centeredEffect, effect.2]
  simp

/-- Completeness of all finite sequential word effects in the full real
Hermitian carrier is witnessed at depth at most `d^2 - 1`. -/
theorem finite_sequential_completeness_depth
    (d : Nat) [NeZero d] {Alphabet : Type*}
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (hcomplete :
      Submodule.span ℝ
          (Set.range fun word : List Alphabet =>
            sequentialWordEffect instrumentDual word) = ⊤) :
    ∃ n ≤ d ^ 2 - 1,
      Submodule.span ℝ
          {effect | ∃ word : List Alphabet,
            word.length ≤ n ∧
              effect = sequentialWordEffect instrumentDual word} = ⊤ := by
  let allCenteredWords := Submodule.span ℝ
    (Set.range fun word : List Alphabet =>
      centeredHermitianMap d (sequentialWordEffect instrumentDual word))
  have hcenteredComplete : allCenteredWords = ⊤ := by
    apply top_unique
    intro effect _
    have hraw : effect.1 ∈ Submodule.span ℝ
        (Set.range fun word : List Alphabet =>
          sequentialWordEffect instrumentDual word) := by
      rw [hcomplete]
      exact Submodule.mem_top
    have hmapSpan : ∀ value : HermitianSpace d,
        value ∈ Submodule.span ℝ
            (Set.range fun word : List Alphabet =>
              sequentialWordEffect instrumentDual word) →
          centeredHermitianMap d value ∈ allCenteredWords := by
      intro value hvalue
      induction hvalue using Submodule.span_induction with
      | mem value hvalue =>
          rcases hvalue with ⟨word, rfl⟩
          exact Submodule.subset_span (Set.mem_range_self word)
      | zero => simp
      | add first second _ _ hfirst hsecond =>
          simpa using Submodule.add_mem allCenteredWords hfirst hsecond
      | smul scalar value _ hvalue =>
          simpa using Submodule.smul_mem allCenteredWords scalar hvalue
    have hmapped := hmapSpan effect.1 hraw
    rwa [centered_hermitian_map_fixed d effect] at hmapped
  obtain ⟨depth, hdepth, hcenteredBounded⟩ :=
    (finite_sequential_word_certificate d instrumentDual hcenteredComplete).2
  refine ⟨depth, hdepth, ?_⟩
  let rawBoundedWords := Submodule.span ℝ
    {effect | ∃ word : List Alphabet,
      word.length ≤ depth ∧ effect = sequentialWordEffect instrumentDual word}
  let centeredBoundedWords := Submodule.span ℝ
    {effect | ∃ word : List Alphabet,
      word.length ≤ depth ∧
        effect = centeredHermitianMap d
          (sequentialWordEffect instrumentDual word)}
  have hcenteredBounded' : centeredBoundedWords = ⊤ := by
    simpa [centeredBoundedWords] using hcenteredBounded
  have hidentity : identityHermitian d ∈ rawBoundedWords := by
    apply Submodule.subset_span
    exact ⟨[], by simp, rfl⟩
  have hcenteredToRaw : ∀ effect : traceZeroHermitian d,
      effect ∈ centeredBoundedWords → effect.1 ∈ rawBoundedWords := by
    intro effect heffect
    induction heffect using Submodule.span_induction with
    | mem value hvalue =>
        rcases hvalue with ⟨word, hlength, rfl⟩
        rw [centered_hermitian_map_coe]
        apply Submodule.sub_mem
        · apply Submodule.subset_span
          exact ⟨word, hlength, rfl⟩
        · exact Submodule.smul_mem rawBoundedWords _ hidentity
    | zero => simp
    | add first second _ _ hfirst hsecond =>
        simpa using Submodule.add_mem rawBoundedWords hfirst hsecond
    | smul scalar value _ hvalue =>
        simpa using Submodule.smul_mem rawBoundedWords scalar hvalue
  change rawBoundedWords = ⊤
  apply top_unique
  intro effect _
  have hcenteredMembership : centeredHermitianMap d effect ∈ centeredBoundedWords := by
    rw [hcenteredBounded']
    exact Submodule.mem_top
  have hcenteredRaw :=
    hcenteredToRaw (centeredHermitianMap d effect) hcenteredMembership
  rw [centered_hermitian_map_coe] at hcenteredRaw
  have hscalar :
      ((Matrix.trace effect.1).re / d) • identityHermitian d ∈ rawBoundedWords :=
    Submodule.smul_mem rawBoundedWords _ hidentity
  simpa using Submodule.add_mem rawBoundedWords hcenteredRaw hscalar

#print axioms hermitian_trace_eq_re
#print axioms centered_hermitian_map_coe
#print axioms centered_hermitian_map_fixed
#print axioms finite_sequential_completeness_depth

end D5.S3.Quantum.PredictionDepth.FiniteSequentialCompletenessDepth
