/- GID: D5/S3/Quantum/Measurement/Auric/ScoreReadout
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ScoreReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The terminal Kraus score is the measured Choi score. -/

import D5.S3.Quantum.Measurement.Auric.ProtocolScore
import D5.S3.Quantum.Measurement.Auric.FiveLevelReadout

/-! # The terminal Kraus score is the measured Choi score -/

namespace D5.S3.Quantum.Measurement.Auric.ScoreReadout

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Measurement.Auric.FiveLevelReadout
open D5.S3.Quantum.Measurement.Auric.FiveLevelTilt
open D5.S3.Quantum.Measurement.Auric.ProtocolScore
open D5.S3.Quantum.Measurement.Auric.RankOneFour
open D5.S3.Quantum.Measurement.Auric.TiltedInstrument

/-- The measured Choi quadratic form for a full flagged matrix map. -/
noncomputable def measuredScore (r : ℝ) (F : MatrixMap Level (Flag × Level) ℂ) : ℝ :=
  ((witnessFrame r)ᴴ * F.choi_matrix * witnessFrame r).trace.re

private theorem witnessZero_eq (r : ℝ) : witnessZero r = flagTest r 0 := by
  simp [flagTest, witnessZero]

private theorem witnessOne_eq (r : ℝ) : witnessOne r = flagTest r 1 := by
  simp [flagTest, witnessOne]

private theorem witnessFrame_apply' (r : ℝ) (j f : Flag) (o i : Level) :
    witnessFrame r ((f, o), i) j = if f = j then flagTest r j o i else 0 := by
  by_cases h : f = j
  · subst f
    fin_cases j <;> simp [witnessFrame, witnessZero_eq, witnessOne_eq]
  · simp [witnessFrame, h]

private def flaggedVector (f : Flag) (K : Matrix Level Level ℂ) (x : ChoiIndex) : ℂ :=
  flagKraus f K x.1 x.2

private theorem witness_pairing (r : ℝ) (j f : Flag) (K : Matrix Level Level ℂ) :
    ((witnessFrame r)ᴴ *ᵥ flaggedVector f K) j =
      if j = f then ((flagTest r j)ᴴ * K).trace else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    witnessFrame_apply', flaggedVector, flagKraus]
  by_cases h : j = f
  · subst f
    rw [Finset.sum_eq_single j]
    · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.conjTranspose_apply]
      exact Finset.sum_comm
    · intro a _ ha
      simp [ha]
    · simp
  · simp [h, Ne.symm h]

private theorem trace_pullback_rank_one {a b : Type*} [Fintype a] [Fintype b]
    (W : Matrix a b ℂ) (x : a → ℂ) :
    (Wᴴ * vecMulVec x (star x) * W).trace.re = ∑ i, ‖(Wᴴ *ᵥ x) i‖ ^ 2 := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  have hz := Matrix.star_mulVec Wᴴ x
  rw [Matrix.conjTranspose_conjTranspose] at hz
  rw [← hz]
  simp [dotProduct, Pi.star_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow]

/-- Arbitrarily many terminal Kraus operators with the same flag contribute
additively to the measured score, with no interference between flags. -/
theorem measuredScore_of_flagged_kraus {i : Type*} [Fintype i] (r : ℝ)
    (f : i → Flag) (K : i → Matrix Level Level ℂ) :
    measuredScore r
      (MatrixMap.of_kraus (fun h => flagKraus (f h) (K h)) fun h => flagKraus (f h) (K h)) =
      ∑ h, ‖((flagTest r (f h))ᴴ * K h).trace‖ ^ 2 := by
  classical
  unfold measuredScore
  rw [MatrixMap.choi_of_kraus, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro h _
  change ((witnessFrame r)ᴴ * vecMulVec (flaggedVector (f h) (K h))
    (star (flaggedVector (f h) (K h))) * witnessFrame r).trace.re = _
  rw [trace_pullback_rank_one]
  simp_rw [witness_pairing]
  rw [Finset.sum_eq_single (f h)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The full channel of a finite strategy, preserving both the flag and its
five-level output. -/
def protocolMap (p : Protocol Level) : MatrixMap Level (Flag × Level) ℂ :=
  let K := fun h : Terminal p => flagKraus (flag p h) (kraus p h)
  MatrixMap.of_kraus K K

theorem protocolMap_cp (p : Protocol Level) : (protocolMap p).IsCompletelyPositive :=
  MatrixMap.of_kraus_isCompletelyPositive _

theorem protocolMap_tp (p : Protocol Level) : (protocolMap p).IsTracePreserving :=
  MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _ (flagged_normalized p)

/-- Measured Choi score of any finite deterministic protocol is bounded by
the maximizing tilted score. -/
theorem measuredScore_protocolMap_le (r : WitnessInterval) (p : Protocol Level) :
    measuredScore r (protocolMap p) ≤ tiltScore r (tiltMass r) := by
  unfold protocolMap
  rw [measuredScore_of_flagged_kraus]
  simpa only [Submonoid.coe_one, Matrix.mul_one] using protocol_score_le r p 1

end D5.S3.Quantum.Measurement.Auric.ScoreReadout
