/- GID: D5/S3/Quantum/Measurement/PovmOutcomeLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/PovmOutcomeLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A normalized finite effect family needs at least d squared outcomes for completeness. -/

import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/- Library-search audit trail (2026-08-27):
   * Exact family hits `HermitianSpace`, `identityHermitian`, `traceZeroHermitian`,
     `centeredHermitianMap`, `trace_zero_hermitian_finrank`, and
     `informational_completeness_four_way` supply the source carrier, canonical
     centering operation, its dimension, and the completeness interpretation.
   * Exact pinned-Mathlib hits `Fintype.not_linearIndependent_iff`,
     `linearIndependent_iff_card_eq_finrank_span`, and `finrank_range_le_card`
     turn normalization into the sharp one-relation span bound.
   * Repository and pinned-Mathlib searches found no theorem packaging the
     centered-sum, span-dimension, and complete-outcome clauses together. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Measurement.PovmOutcomeLowerBound

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
open D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Centering a normalized finite effect family produces one nontrivial linear
relation. Hence its centered span has dimension at most one less than the
number of outcomes, and completeness requires at least `d ^ 2` outcomes. -/
theorem povm_outcome_lower_bound
    (d m : Nat) [NeZero d]
    (effects : Fin m → HermitianSpace d)
    (hnormalized : ∑ a, effects a = identityHermitian d) :
    let centered := fun a => centeredHermitianMap d (effects a)
    (∑ a, centered a = 0) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range centered)) ≤ m - 1 ∧
      (Submodule.span ℝ (Set.range centered) = ⊤ → d ^ 2 ≤ m) := by
  dsimp only
  have hcentered : ∑ a, centeredHermitianMap d (effects a) = 0 := by
    rw [← map_sum, hnormalized]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp [centeredHermitianMap, centeredEffect, identityHermitian]
  have hmPositive : 0 < m := by
    by_contra hm
    have hmZero : m = 0 := by omega
    subst m
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hnormalized
    have hidentityZero : (1 : Matrix (Fin d) (Fin d) ℂ) = 0 :=
      congrArg Subtype.val hnormalized.symm
    exact one_ne_zero hidentityZero
  have hdependent :
      ¬LinearIndependent ℝ (fun a => centeredHermitianMap d (effects a)) := by
    rw [Fintype.not_linearIndependent_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · simpa using hcentered
    · exact ⟨⟨0, hmPositive⟩, one_ne_zero⟩
  have hspanLe :
      Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range (fun a => centeredHermitianMap d (effects a)))) ≤ m := by
    simpa only [Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := ℝ)
        (fun a => centeredHermitianMap d (effects a)))
  have hspanNe :
      Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range (fun a => centeredHermitianMap d (effects a)))) ≠ m := by
    intro heq
    apply hdependent
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Set.finrank, Fintype.card_fin] using heq.symm
  have hspanPred :
      Module.finrank ℝ
          (Submodule.span ℝ
            (Set.range (fun a => centeredHermitianMap d (effects a)))) ≤ m - 1 := by
    omega
  refine ⟨hcentered, hspanPred, ?_⟩
  intro hcomplete
  have hdimension : d ^ 2 - 1 ≤ m - 1 := by
    rw [hcomplete, finrank_top, trace_zero_hermitian_finrank d] at hspanPred
    exact hspanPred
  have hdPositive : 0 < d ^ 2 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne d)) 2
  omega

#print axioms povm_outcome_lower_bound

end D5.S3.Quantum.Measurement.PovmOutcomeLowerBound
