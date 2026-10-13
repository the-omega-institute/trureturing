/-
  GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernsteinBatchExecution
  Generality: G

  This file contains the zero-safe conditional row construction needed by the
  common-table batch argument.  The actual two-source acquired-history law is
  deliberately not assumed here: a later execution theorem must supply that
  bridge from the frozen source kernel.
-/

import D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryCriticalMoment
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open scoped BigOperators ENNReal

namespace D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinBatchExecution

/-! A row has one continuation outcome (`none`) and one outcome for every
finite output colour.  The entries are absolute masses at a reached node. -/

variable {E : Type*} [Fintype E] [Nonempty E]

def fallbackRow : PMF (Option E) :=
  PMF.ofFintype (fun o : Option E => match o with | none => 1 | some _ => 0) (by
    rw [Fintype.sum_option]
    simp)

def stageRow (z : ℝ≥0∞) (delta : E → ℝ≥0∞) (continuation : ℝ≥0∞)
    (hmass : (∑ e, delta e) + continuation = z) (hz_top : z ≠ ∞) : PMF (Option E) :=
  if hz : z = 0 then
    fallbackRow
  else
    PMF.ofFintype
      (fun o : Option E => match o with
        | none => continuation * z⁻¹
        | some e => delta e * z⁻¹) (by
          rw [Fintype.sum_option]
          calc
            continuation * z⁻¹ + ∑ e, delta e * z⁻¹ =
                (continuation + ∑ e, delta e) * z⁻¹ := by
                  rw [add_mul, Finset.sum_mul]
            _ = ((∑ e, delta e) + continuation) * z⁻¹ := by
                  congr 1
                  ac_rfl
            _ = z * z⁻¹ := by rw [hmass]
            _ = 1 := ENNReal.mul_inv_cancel hz hz_top)

@[simp]
theorem stageRow_apply_none_of_ne_zero (z : ℝ≥0∞) (delta : E → ℝ≥0∞)
    (continuation : ℝ≥0∞) (hmass : (∑ e, delta e) + continuation = z)
    (hz_top : z ≠ ∞) (hz : z ≠ 0) :
    stageRow z delta continuation hmass hz_top none = continuation * z⁻¹ := by
  simp [stageRow, hz]

@[simp]
theorem stageRow_apply_some_of_ne_zero (z : ℝ≥0∞) (delta : E → ℝ≥0∞)
    (continuation : ℝ≥0∞) (hmass : (∑ e, delta e) + continuation = z)
    (hz_top : z ≠ ∞) (hz : z ≠ 0) (e : E) :
    stageRow z delta continuation hmass hz_top (some e) = delta e * z⁻¹ := by
  simp [stageRow, hz]

theorem zero_masses_of_zero_node (z : ℝ≥0∞) (delta : E → ℝ≥0∞)
    (continuation : ℝ≥0∞) (hmass : (∑ e, delta e) + continuation = z)
    (hz : z = 0) :
    (∀ e, delta e = 0) ∧ continuation = 0 := by
  have hzero : (∑ e, delta e) + continuation = 0 := by simpa [hz] using hmass
  have hparts : (∑ e, delta e = 0) ∧ continuation = 0 :=
    (add_eq_zero.mp hzero)
  refine ⟨?_, hparts.2⟩
  intro e
  exact congrFun (Fintype.sum_eq_zero_iff_of_nonneg (fun e => bot_le) |>.mp hparts.1) e

/-!
The central one-step fact: compatible absolute output masses determine one
single normalized row.  Multiplication by the reached mass recovers each
absolute output mass and the continuation mass.  The statement includes the
zero-node case, so no division by a zero mass is used by a caller.
-/
theorem compatible_stage_classification
    (z : ℝ≥0∞) (delta : E → ℝ≥0∞) (continuation : ℝ≥0∞)
    (hmass : (∑ e, delta e) + continuation = z) (hz_top : z ≠ ∞) :
    let row := stageRow z delta continuation hmass hz_top
    (∀ e, z * row (some e) = delta e) ∧ z * row none = continuation := by
  dsimp
  by_cases hz : z = 0
  · obtain ⟨hdelta, hcont⟩ := zero_masses_of_zero_node z delta continuation hmass hz
    refine ⟨fun e => ?_, ?_⟩
    · simp [stageRow, fallbackRow, hz, hdelta e]
    · simp [stageRow, fallbackRow, hz, hcont]
  · refine ⟨fun e => ?_, ?_⟩
    · rw [stageRow_apply_some_of_ne_zero z delta continuation hmass hz_top hz e]
      calc
        z * (delta e * z⁻¹) = delta e * (z * z⁻¹) := by ac_rfl
        _ = delta e := by rw [ENNReal.mul_inv_cancel hz hz_top, mul_one]
    · rw [stageRow_apply_none_of_ne_zero z delta continuation hmass hz_top hz]
      calc
        z * (continuation * z⁻¹) = continuation * (z * z⁻¹) := by ac_rfl
        _ = continuation := by rw [ENNReal.mul_inv_cancel hz hz_top, mul_one]

/-! A common table is chosen once for all parameters.  Its rows are indexed by
the batch level, rather than by the unknown Bernoulli rates. -/

def commonStageTable (z : ℕ → ℝ≥0∞) (delta : ℕ → E → ℝ≥0∞)
    (continuation : ℕ → ℝ≥0∞) (hmass : ∀ k, (∑ e, delta k e) + continuation k = z k)
    (hz_top : ∀ k, z k ≠ ∞) : ℕ → PMF (Option E) :=
  fun k => stageRow (z k) (delta k) (continuation k) (hmass k) (hz_top k)

theorem commonStageTable_classification
    (z : ℕ → ℝ≥0∞) (delta : ℕ → E → ℝ≥0∞)
    (continuation : ℕ → ℝ≥0∞)
    (hmass : ∀ k, (∑ e, delta k e) + continuation k = z k)
    (hz_top : ∀ k, z k ≠ ∞) :
    ∀ k, (∀ e, z k * commonStageTable z delta continuation hmass hz_top k (some e) = delta k e) ∧
      z k * commonStageTable z delta continuation hmass hz_top k none = continuation k := by
  intro k
  exact compatible_stage_classification (z k) (delta k) (continuation k)
    (hmass k) (hz_top k)

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinBatchExecution
