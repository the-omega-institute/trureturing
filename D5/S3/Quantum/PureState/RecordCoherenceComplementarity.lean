/- GID: D5/S3/Quantum/PureState/RecordCoherenceComplementarity
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/RecordCoherenceComplementarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized pure records obey exact distinguishability-coherence complementarity. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt

/- Library-search audit trail (2026-08-16):
   * Repository search found the environment-record overlap and channel laws, but no theorem
     stating the distinguishability-visibility identity or both endpoint consequences.
   * Loogle and LeanSearch returned `norm_inner_le_norm` as the exact normalized-overlap bound.
   * LeanSearch returned `Real.sq_sqrt` as the exact square-root identity used below; local
     pinned-Mathlib search confirmed both declarations in their imported modules.
   * Loogle also returned `Real.sqrt_sq_eq_abs`; it is related but does not close this statement.
-/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.PureState.RecordCoherenceComplementarity

/-- Two normalized pure records have complementary distinguishability and retained coherence.
The two overlap endpoints and their operational consequences are retained in the same named
statement. -/
theorem pure_record_distinguishability_coherence_complementarity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (recordLeft recordRight : E) (hLeft : ‖recordLeft‖ = 1) (hRight : ‖recordRight‖ = 1) :
    let c := ⟪recordLeft, recordRight⟫_ℂ
    let visibility := ‖c‖
    let distinguishability := Real.sqrt (1 - visibility ^ 2)
    distinguishability ^ 2 + visibility ^ 2 = 1 ∧
      (c = 0 → distinguishability = 1 ∧ visibility = 0) ∧
      (visibility = 1 → distinguishability = 0 ∧ visibility = 1) ∧
      (distinguishability = 1 → visibility = 0 ∧ ∀ amplitude : ℂ, c * amplitude = 0) ∧
      (visibility = 1 → distinguishability = 0) := by
  dsimp only
  have hoverlap : ‖⟪recordLeft, recordRight⟫_ℂ‖ ≤ 1 := by
    calc
      ‖⟪recordLeft, recordRight⟫_ℂ‖ ≤ ‖recordLeft‖ * ‖recordRight‖ :=
        norm_inner_le_norm recordLeft recordRight
      _ = 1 := by rw [hLeft, hRight, one_mul]
  have hradicand : 0 ≤ 1 - ‖⟪recordLeft, recordRight⟫_ℂ‖ ^ 2 := by
    nlinarith [norm_nonneg ⟪recordLeft, recordRight⟫_ℂ]
  have hcomplementarity :
      Real.sqrt (1 - ‖⟪recordLeft, recordRight⟫_ℂ‖ ^ 2) ^ 2 +
          ‖⟪recordLeft, recordRight⟫_ℂ‖ ^ 2 = 1 := by
    rw [Real.sq_sqrt hradicand]
    ring
  refine ⟨hcomplementarity, ?_, ?_, ?_, ?_⟩
  · intro hzero
    simp [hzero]
  · intro hunit
    rw [hunit]
    norm_num
  · intro hperfect
    have hvisibility : ‖⟪recordLeft, recordRight⟫_ℂ‖ = 0 := by
      nlinarith [hcomplementarity]
    have hoverlapZero : ⟪recordLeft, recordRight⟫_ℂ = 0 := norm_eq_zero.mp hvisibility
    simp [hoverlapZero]
  · intro hunit
    rw [hunit]
    norm_num

example : ℂ := 0

example : ‖(1 : ℂ)‖ = 1 ∧ ‖(1 : ℂ)‖ = 1 := by norm_num

#print axioms pure_record_distinguishability_coherence_complementarity

end D5.S3.Quantum.PureState.RecordCoherenceComplementarity
