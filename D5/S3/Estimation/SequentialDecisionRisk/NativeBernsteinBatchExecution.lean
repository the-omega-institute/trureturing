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
open SeededBernoulliFactoryExecution MeasureTheory ProbabilityTheory Filter

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

/-! The stage rows are chosen once, before either source rate is supplied.  The
construction below is intentionally indexed by the level only: it cannot
inspect `p`, `q`, or a private seed.  This is the part of the common-table
argument that is useful even when the full acquired-history induction is still
being discharged. -/

def commonStageTable (z : ℕ → ℝ≥0∞) (delta : ℕ → E → ℝ≥0∞)
    (continuation : ℕ → ℝ≥0∞)
    (hmass : ∀ k, (∑ e, delta k e) + continuation k = z k)
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

/-! Source counters are taken from the actual acquired record.  In particular,
they are not an input field asserting a new-layer count law. -/

def sourceCount (source : Bool) (h : List (Bool × Bool)) : ℕ :=
  (h.filter (fun v => v.1 = source)).length

theorem sourceCount_partition (h : List (Bool × Bool)) :
    sourceCount true h + sourceCount false h = h.length := by
  have hcount := h.length_eq_length_filter_add (fun v : Bool × Bool => v.1)
  simpa [sourceCount] using hcount.symm

theorem acquiredHistory_sourceCount_partition
    {Seed Tape : Type} (π : Seed → Bool → List (Bool × Bool) → Bool ⊕ (Bool × Bool))
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (n : ℕ) (ω : Seed × Tape) :
    sourceCount true (acquiredHistory π S answer n ω) +
        sourceCount false (acquiredHistory π S answer n ω) =
      (acquiredHistory π S answer n ω).length := by
  exact sourceCount_partition _

theorem acquiredHistory_source_counts_sum_before_return
    {Seed Tape : Type} (π : Seed → Bool → List (Bool × Bool) → Bool ⊕ (Bool × Bool))
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape) (n : ℕ)
    (hn : (n : WithTop ℕ) ≤
      hittingAfter (fun m (_ : Seed × Tape) =>
          π ω.1 S (acquiredHistory π S answer m ω))
        (Set.range (fun cell : Bool × Bool => (Sum.inr cell : Bool ⊕ (Bool × Bool)))) 0 ω) :
    sourceCount true (acquiredHistory π S answer n ω) +
        sourceCount false (acquiredHistory π S answer n ω) = n := by
  rw [sourceCount_partition]
  exact acquired_history_length_before_return π S answer ω n hn

theorem acquiredHistory_source_counts_sum_at_return
    {Seed Tape : Type} (π : Seed → Bool → List (Bool × Bool) → Bool ⊕ (Bool × Bool))
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape) (n : ℕ)
    (hn : hittingAfter (fun m (_ : Seed × Tape) =>
        π ω.1 S (acquiredHistory π S answer m ω))
      (Set.range (fun cell : Bool × Bool => (Sum.inr cell : Bool ⊕ (Bool × Bool)))) 0 ω =
        (n : WithTop ℕ)) :
    sourceCount true (acquiredHistory π S answer n ω) +
        sourceCount false (acquiredHistory π S answer n ω) = n := by
  exact acquiredHistory_source_counts_sum_before_return π S answer ω n hn.ge

/-! A finite path through the one table has the corresponding absolute mass.
This packages the zero-node case for an entire finite history: no factor is
ever divided by `z k`, and the same table is used at every level. -/

def commonPathMass (z : ℕ → ℝ≥0∞) (delta : ℕ → E → ℝ≥0∞)
    (continuation : ℕ → ℝ≥0∞) (n : ℕ) (path : Fin n → Option E) : ℝ≥0∞ :=
  ∏ k : Fin n, match path k with
    | none => continuation k
    | some e => delta k e

theorem commonStageTable_path_mass
    (z : ℕ → ℝ≥0∞) (delta : ℕ → E → ℝ≥0∞)
    (continuation : ℕ → ℝ≥0∞)
    (hmass : ∀ k, (∑ e, delta k e) + continuation k = z k)
    (hz_top : ∀ k, z k ≠ ∞) (n : ℕ) (path : Fin n → Option E) :
    (∏ k : Fin n, z k) *
        (∏ k : Fin n, commonStageTable z delta continuation hmass hz_top k (path k)) =
      commonPathMass z delta continuation n path := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hclass := commonStageTable_classification z delta continuation hmass hz_top k
  cases hp : path k with
  | none =>
      simpa [commonPathMass, hp] using hclass.2
  | some e =>
      simpa [commonPathMass, hp] using hclass.1 e

/-! The finite path version of the B0 telescope.  The indicator is attached to
the stopping layer itself, so the identity does not replace the two actual
source counters by a total history length. -/

theorem finite_stopping_layer_telescope
    (D : ℕ → ℝ) (J K : ℕ) (hK : K ≤ J) :
    D K = D 0 + ∑ k ∈ Finset.range J, if k < K then D (k + 1) - D k else 0 := by
  have hprefix : ∀ n : ℕ,
      D n = D 0 + ∑ k ∈ Finset.range n, (D (k + 1) - D k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsum :
      (∑ k ∈ Finset.range J, if k < K then D (k + 1) - D k else 0) =
        ∑ k ∈ Finset.range K, (D (k + 1) - D k) := by
    have hs :
        (∑ k ∈ Finset.range K, if k < K then D (k + 1) - D k else 0) =
          ∑ k ∈ Finset.range J, if k < K then D (k + 1) - D k else 0 := by
      apply Finset.sum_subset ((Finset.range_subset_range).2 hK)
      intro k hkJ hkK
      have hkK' : ¬ k < K := by simpa using hkK
      simp [hkK']
    have hleft :
        (∑ k ∈ Finset.range K, if k < K then D (k + 1) - D k else 0) =
          ∑ k ∈ Finset.range K, (D (k + 1) - D k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]
    exact hs.symm.trans hleft
  rw [hprefix K, ← hsum]

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinBatchExecution
