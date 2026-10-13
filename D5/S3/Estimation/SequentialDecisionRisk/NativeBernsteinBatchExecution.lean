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
import Mathlib.Probability.Distributions.Binomial
import D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

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

private theorem acquiredHistory_source_counts_sum_before_return
    {Seed Tape : Type} (π : Seed → Bool → List (Bool × Bool) → Bool ⊕ (Bool × Bool))
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape) (n : ℕ)
    (hn : (n : WithTop ℕ) ≤
      hittingAfter (fun m (_ : Seed × Tape) =>
          π ω.1 S (acquiredHistory π S answer m ω))
        (Set.range (fun cell : Bool × Bool => (Sum.inr cell : Bool ⊕ (Bool × Bool)))) 0 ω) :
    sourceCount true (acquiredHistory π S answer n ω) +
        sourceCount false (acquiredHistory π S answer n ω) = n := by
  rw [acquiredHistory_sourceCount_partition]
  exact acquired_history_length_before_return π S answer ω n hn

private theorem acquiredHistory_source_counts_sum_at_return
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

/-- Actual records grow by at most one entry, remain prefixes of all later
records, and stay fixed after a return action. -/
theorem acquired_history_geometry
    {Seed Tape : Type} (π : Seed → Bool → List (Bool × Bool) → Bool ⊕ (Bool × Bool))
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape) :
    (∀ n, (acquiredHistory π S answer n ω).length ≤ n) ∧
    (∀ n m, n ≤ m → List.IsPrefix (acquiredHistory π S answer n ω)
      (acquiredHistory π S answer m ω)) ∧
    (∀ n cell, π ω.1 S (acquiredHistory π S answer n ω) = Sum.inr cell →
      ∀ r, acquiredHistory π S answer (n + r) ω = acquiredHistory π S answer n ω) := by
  have hstep (n : ℕ) : List.IsPrefix (acquiredHistory π S answer n ω)
      (acquiredHistory π S answer (n + 1) ω) := by
    rw [acquiredHistory]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨[], List.append_nil _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => simp [acquiredHistory]
    | succ n ih =>
      rw [acquiredHistory]
      split
      · simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right ih 1
      · exact ih.trans (Nat.le_succ n)
  · intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨[], List.append_nil _⟩
    | succ m hnm ih => exact ih.trans (hstep m)
  · intro n cell hreturn r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [Nat.add_succ, acquiredHistory, ih, hreturn]

abbrev Action := Bool ⊕ (Bool × Bool)
abbrev History := List (Bool × Bool)
abbrev Tape := ℕ → ℝ
abbrev RowSeed := (Bool × History) → Action

def sourceRead (p q : unitInterval) (source : Bool) (n : ℕ) (tape : Tape) : Bool :=
  decide (tape n ≤ ((if source then q else p) : unitInterval))

def nativeHistory {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (n : ℕ) : Seed × Tape → History :=
  acquiredHistory π S (sourceRead p q) n

def nativeAction {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (n : ℕ) (ω : Seed × Tape) : Action :=
  π ω.1 S (nativeHistory π S p q n ω)

def wordPrefix (t : ℕ → Bool × Bool) (n : ℕ) : History :=
  List.ofFn (fun i : Fin n => t i)

def nativeTrace {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) : Set (Seed × Tape) :=
  {ω | ∀ i < n, nativeAction π S p q i ω = .inl (t i).1 ∧
    sourceRead p q (t i).1 i ω.2 = (t i).2}

/-- A trace is exactly the event that the actual record has the specified full
length and ordered labels and answers. In particular, no early return is lost. -/
theorem trace_iff_exact_acquired_history
    {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) :
    nativeTrace π S p q t n = {ω | nativeHistory π S p q n ω = wordPrefix t n} := by
  ext ω
  constructor
  · exact NativeBernoulliFactoryCriticalMoment.history_of_trace π S p q t n ω
  · intro he
    induction n with
    | zero => exact fun i hi => False.elim (Nat.not_lt_zero i hi)
    | succ n ih =>
      have hlen := (acquired_history_geometry π S (sourceRead p q) ω).1 n
      change nativeHistory π S p q (n + 1) ω = wordPrefix t (n + 1) at he
      have hstep : nativeHistory π S p q (n + 1) ω =
          match π ω.1 S (nativeHistory π S p q n ω) with
          | .inl s => nativeHistory π S p q n ω ++ [(s, sourceRead p q s n ω.2)]
          | .inr _ => nativeHistory π S p q n ω := by
        simp only [nativeHistory, acquiredHistory]
        cases π ω.1 S (acquiredHistory π S (sourceRead p q) n ω) <;> rfl
      rw [hstep] at he
      cases ha : π ω.1 S (nativeHistory π S p q n ω) with
      | inl source =>
        rw [ha, wordPrefix, List.ofFn_succ'] at he
        have hparts : nativeHistory π S p q n ω = wordPrefix t n ∧
            (source, sourceRead p q source n ω.2) = t n := by
          apply List.concat_inj.mp
          simpa only [List.concat_eq_append, wordPrefix, Fin.val_castSucc,
            Fin.val_last] using he
        have hp := ih hparts.1
        intro i hi
        by_cases hin : i < n
        · exact hp i hin
        · have hie : i = n := by omega
          subst i
          have hs := congrArg Prod.fst hparts.2
          have hb := congrArg Prod.snd hparts.2
          exact ⟨by simpa only [nativeAction, ← hs] using ha,
            by simpa only [← hs] using hb⟩
      | inr cell =>
        rw [ha] at he
        have hlength := congrArg List.length he
        simp only [wordPrefix, List.length_ofFn] at hlength
        change (nativeHistory π S p q n ω).length ≤ n at hlen
        omega

def nativeCalls {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) : Seed × Tape → WithTop ℕ :=
  hittingAfter (nativeAction π S p q) (Set.range (fun c : Bool × Bool => (Sum.inr c : Action))) 0

/-- Measurability uses the actual uniform innovation tape for both sources. -/
theorem native_execution_measurable
    {Seed : Type} [MeasurableSpace Seed] (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool) (p q : unitInterval) :
    letI : MeasurableSpace History := ⊤
    (∀ n, Measurable (nativeHistory π S p q n)) ∧
    (∀ n, Measurable (nativeAction π S p q n)) ∧
    (∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < nativeCalls π S p q ω}) := by
  let : MeasurableSpace History := ⊤
  let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
  have hp : Measurable (fun z : Seed × History => π z.1 S z.2) :=
    measurable_from_prod_countable_left (hπ S)
  have hr (s : Bool) (n : ℕ) :
      Measurable (fun ω : Seed × Tape => sourceRead p q s n ω.2) :=
    (NativeBernoulliFactoryCriticalMoment.coin_measurable (if s then q else p)).comp
      ((measurable_pi_apply n).comp measurable_snd)
  have hh (n : ℕ) : Measurable (nativeHistory π S p q n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have ha := hp.comp (measurable_fst.prodMk ih)
      have hu : Measurable (fun z : History × Action × (Bool × Bool) =>
          match z.2.1 with
          | .inl s => z.1 ++ [(s, if s then z.2.2.2 else z.2.2.1)]
          | _ => z.1) := Measurable.of_discrete
      convert hu.comp (ih.prodMk (ha.prodMk ((hr false n).prodMk (hr true n)))) using 1
      funext ω
      simp only [nativeHistory, acquiredHistory, Function.comp_apply]
      cases π ω.1 S (acquiredHistory π S (sourceRead p q) n ω) with
      | inl s => cases s <;> rfl
      | inr c => rfl
  have ha (n : ℕ) : Measurable (nativeAction π S p q n) :=
    hp.comp (measurable_fst.prodMk (hh n))
  refine ⟨hh, ha, fun n => ?_⟩
  have hm : MeasurableSet {ω | nativeCalls π S p q ω ≤ (n : WithTop ℕ)} := by
    have he (ω : Seed × Tape) : nativeCalls π S p q ω ≤ (n : WithTop ℕ) ↔
        ∃ j ∈ Set.Icc 0 n, nativeAction π S p q j ω ∈
          Set.range (fun c : Bool × Bool => (Sum.inr c : Action)) :=
      hittingAfter_le_iff
    simp only [he, Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      ((ha i) measurableSet_range_inr))
  simpa only [Set.compl_ofPred, not_le] using hm.compl

def rawLaw {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) : Measure (Seed × Tape) :=
  ν.prod (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)))

def rowLaw (table : (Bool × History) → PMF Action) : Measure RowSeed :=
  Measure.infinitePi (fun row => (table row).toMeasure)

def tablePolicy (seed : RowSeed) (S : Bool) (h : History) : Action := seed (S, h)

def extendHistory (h : History) (i : ℕ) : Bool × Bool :=
  if hi : i < h.length then h[i] else (false, false)

private theorem prefix_extend_history (h : History) :
    wordPrefix (extendHistory h) h.length = h := by
  simp [wordPrefix, extendHistory]

def historyPathWeight (table : (Bool × History) → PMF Action) (S : Bool)
    (h : History) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range h.length,
    table (S, wordPrefix (extendHistory h) i) (.inl (extendHistory h i).1)

def historyLikelihood (p q : unitInterval) (h : History) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range h.length,
    (bernoulliMeasure true false (if (extendHistory h i).1 then q else p))
      {(extendHistory h i).2}

def reachedHistory {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (h : History) : Set (Seed × Tape) :=
  {ω | nativeHistory π S p q h.length ω = h}

/-- The ordered-history leaf law refers to the actual acquired record. -/
theorem actual_history_leaf_law (table : (Bool × History) → PMF Action) (S : Bool)
    (p q : unitInterval) (h : History) (a : Action) :
    rawLaw (rowLaw table) (reachedHistory tablePolicy S p q h ∩
      {ω | nativeAction tablePolicy S p q h.length ω = a}) =
      (historyPathWeight table S h * table (S, h) a) * historyLikelihood p q h := by
  have hb := NativeBernoulliFactoryCriticalMoment.native_policy_table_leaf_law
    table S p q (extendHistory h) h.length a
  change rawLaw (rowLaw table) (nativeTrace tablePolicy S p q (extendHistory h) h.length ∩
      {ω | nativeAction tablePolicy S p q h.length ω = a}) =
      (historyPathWeight table S h * table (S, wordPrefix (extendHistory h) h.length) a) *
        historyLikelihood p q h at hb
  simpa only [trace_iff_exact_acquired_history, prefix_extend_history, reachedHistory] using hb

/-- Summing the terminal action leaves recovers the arrival mass, including
zero-probability histories and endpoint source rates. -/
theorem actual_history_reach_law (table : (Bool × History) → PMF Action) (S : Bool)
    (p q : unitInterval) (h : History) :
    rawLaw (rowLaw table) (reachedHistory tablePolicy S p q h) =
      historyPathWeight table S h * historyLikelihood p q h := by
  classical
  have ha := (native_execution_measurable tablePolicy
    (fun S h => measurable_pi_apply (S, h)) S p q).2.1 h.length
  have hsum := sum_measure_preimage_singleton
    (μ := (rawLaw (rowLaw table)).restrict (reachedHistory tablePolicy S p q h))
    (f := nativeAction tablePolicy S p q h.length) (Finset.univ : Finset Action)
    (fun a _ => ha (action_singleton_measurable a))
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hsum
  calc
    rawLaw (rowLaw table) (reachedHistory tablePolicy S p q h) =
        ∑ a : Action, rawLaw (rowLaw table) (reachedHistory tablePolicy S p q h ∩
          {ω | nativeAction tablePolicy S p q h.length ω = a}) := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Measure.restrict_apply (ha (action_singleton_measurable a)), Set.inter_comm]
      rfl
    _ = ∑ a : Action, (historyPathWeight table S h * table (S, h) a) *
        historyLikelihood p q h := by
      apply Finset.sum_congr rfl
      intro a _
      exact actual_history_leaf_law table S p q h a
    _ = historyPathWeight table S h * historyLikelihood p q h := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      have hn : (∑ a : Action, table (S, h) a) = 1 := by
        simpa only [tsum_fintype] using (table (S, h)).tsum_coe
      rw [hn, mul_one]

def successCount (source : Bool) (h : History) : ℕ :=
  (h.filter (fun v => v.1 = source ∧ v.2 = true)).length

def countFiber (n N M i j : ℕ) : Finset (Fin n → Bool × Bool) :=
  Finset.univ.filter (fun w => sourceCount false (List.ofFn w) = N ∧
    sourceCount true (List.ofFn w) = M ∧ successCount false (List.ofFn w) = i ∧
    successCount true (List.ofFn w) = j)

private theorem measure_history_fibers {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → History) (hH : @Measurable Ω History _ ⊤ H)
    (n : ℕ) (F : Set History) [DecidablePred (· ∈ F)]
    (E : Set Ω) (hE : MeasurableSet E) :
    μ ({ω | (H ω).length = n ∧ H ω ∈ F} ∩ E) =
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → Bool × Bool => List.ofFn w ∈ F),
        μ ({ω | H ω = List.ofFn w} ∩ E) := by
  classical
  let : MeasurableSpace History := ⊤
  have he : {ω | (H ω).length = n ∧ H ω ∈ F} ∩ E =
      ⋃ w ∈ Finset.univ.filter (fun w : Fin n → Bool × Bool => List.ofFn w ∈ F),
        {ω | H ω = List.ofFn w} ∩ E := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hlen, hF⟩, hE⟩
      subst n
      exact ⟨(H ω).get, by simpa using hF, (List.ofFn_get _).symm, hE⟩
    · rintro ⟨w, hF, hw, hE⟩
      exact ⟨⟨by rw [hw, List.length_ofFn], by simpa only [hw] using hF⟩, hE⟩
  rw [he]
  apply measure_biUnion_finset
  · intro w _ v _ hne
    apply Set.disjoint_left.mpr
    intro ω hw hv
    exact hne (List.ofFn_injective (hw.1.symm.trans hv.1))
  · intro w _
    exact (hH (measurableSet_singleton _)).inter hE

/-- Each ordered labelled history keeps its own private policy weight in a
count fiber, even when source choices are adaptive. -/
theorem all_history_count_fiber_aggregation
    (table : (Bool × History) → PMF Action) (S : Bool) (p q : unitInterval)
    (n N M i j : ℕ) (a : Action) :
    rawLaw (rowLaw table) {ω |
      (nativeHistory tablePolicy S p q n ω).length = n ∧
      sourceCount false (nativeHistory tablePolicy S p q n ω) = N ∧
      sourceCount true (nativeHistory tablePolicy S p q n ω) = M ∧
      successCount false (nativeHistory tablePolicy S p q n ω) = i ∧
      successCount true (nativeHistory tablePolicy S p q n ω) = j ∧
      nativeAction tablePolicy S p q n ω = a} =
      ∑ w ∈ countFiber n N M i j,
        (historyPathWeight table S (List.ofFn w) * table (S, List.ofFn w) a) *
          historyLikelihood p q (List.ofFn w) := by
  classical
  have hm := native_execution_measurable tablePolicy
    (fun S h => measurable_pi_apply (S, h)) S p q
  have hf := measure_history_fibers (rawLaw (rowLaw table))
    (nativeHistory tablePolicy S p q n) (hm.1 n) n
    {h | sourceCount false h = N ∧ sourceCount true h = M ∧
      successCount false h = i ∧ successCount true h = j}
    {ω | nativeAction tablePolicy S p q n ω = a}
    ((hm.2.1 n) (action_singleton_measurable a))
  simp only [Set.mem_ofPred_eq, ← Set.ofPred_and, and_assoc] at hf
  rw [hf]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [reachedHistory, List.length_ofFn, ← Set.ofPred_and] using
    actual_history_leaf_law table S p q (List.ofFn w) a

/-- Arrival mass is the sum of the complete ordered-history weights in the
same count fiber. -/
theorem all_history_count_fiber_reach
    (table : (Bool × History) → PMF Action) (S : Bool) (p q : unitInterval)
    (n N M i j : ℕ) :
    rawLaw (rowLaw table) {ω |
      (nativeHistory tablePolicy S p q n ω).length = n ∧
      sourceCount false (nativeHistory tablePolicy S p q n ω) = N ∧
      sourceCount true (nativeHistory tablePolicy S p q n ω) = M ∧
      successCount false (nativeHistory tablePolicy S p q n ω) = i ∧
      successCount true (nativeHistory tablePolicy S p q n ω) = j} =
      ∑ w ∈ countFiber n N M i j,
        historyPathWeight table S (List.ofFn w) * historyLikelihood p q (List.ofFn w) := by
  classical
  have hm := native_execution_measurable tablePolicy
    (fun S h => measurable_pi_apply (S, h)) S p q
  have hf := measure_history_fibers (rawLaw (rowLaw table))
    (nativeHistory tablePolicy S p q n) (hm.1 n) n
    {h | sourceCount false h = N ∧ sourceCount true h = M ∧
      successCount false h = i ∧ successCount true h = j} Set.univ MeasurableSet.univ
  simp only [Set.mem_ofPred_eq, Set.inter_univ] at hf
  rw [hf]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [reachedHistory, List.length_ofFn] using
    actual_history_reach_law table S p q (List.ofFn w)

/-- Aggregating full acquired records preserves the next fresh-answer kernel;
the selected set can constrain both sources and both success counters. -/
theorem aggregate_native_next_answer_kernel
    {Seed : Type} [MeasurableSpace Seed] (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p q : unitInterval)
    (n : ℕ) (F : Set History) (source b : Bool) :
    let E := {ω | (nativeHistory π S p q n ω).length = n ∧
      nativeHistory π S p q n ω ∈ F ∧ nativeAction π S p q n ω = .inl source}
    rawLaw ν (E ∩ {ω | sourceRead p q source n ω.2 = b}) =
      rawLaw ν E * (bernoulliMeasure true false (if source then q else p)) {b} := by
  classical
  dsimp only
  let H := nativeHistory π S p q n
  let B : Set (Seed × Tape) := {ω | nativeAction π S p q n ω = .inl source}
  let R : Set (Seed × Tape) := {ω | sourceRead p q source n ω.2 = b}
  have hm := native_execution_measurable π hπ S p q
  have hB : MeasurableSet B := (hm.2.1 n) (action_singleton_measurable _)
  have hR : MeasurableSet R :=
    ((NativeBernoulliFactoryCriticalMoment.coin_measurable (if source then q else p)).comp
      ((measurable_pi_apply n).comp measurable_snd)) (measurableSet_singleton b)
  have he : {ω | (nativeHistory π S p q n ω).length = n ∧
      nativeHistory π S p q n ω ∈ F ∧ nativeAction π S p q n ω = .inl source} =
      {ω | (H ω).length = n ∧ H ω ∈ F} ∩ B := by
    ext ω
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ _
    tauto
  rw [he]
  change rawLaw ν (({ω | (H ω).length = n ∧ H ω ∈ F} ∩ B) ∩ R) = _
  rw [Set.inter_assoc, measure_history_fibers (rawLaw ν) H (hm.1 n) n F
    (B ∩ R) (hB.inter hR), measure_history_fibers (rawLaw ν) H (hm.1 n) n F B hB,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  have hk := NativeBernoulliFactoryCriticalMoment.native_source_conditional_kernel
    π hπ S ν p q (extendHistory (List.ofFn w)) n source b Set.univ MeasurableSet.univ
  have hpref : wordPrefix (extendHistory (List.ofFn w)) n = List.ofFn w := by
    simpa only [List.length_ofFn] using prefix_extend_history (List.ofFn w)
  change rawLaw ν (((nativeTrace π S p q (extendHistory (List.ofFn w)) n ∩ B) ∩
      Prod.fst ⁻¹' (Set.univ : Set Seed)) ∩ R) =
    rawLaw ν ((nativeTrace π S p q (extendHistory (List.ofFn w)) n ∩ B) ∩
      Prod.fst ⁻¹' (Set.univ : Set Seed)) * _ at hk
  simpa only [Set.preimage_univ, Set.inter_univ, trace_iff_exact_acquired_history,
    hpref, Set.inter_assoc] using hk

def binomialMass (n i : ℕ) (p : unitInterval) : ℝ≥0∞ := binomial n p {i}

def bernoulliMass (p : unitInterval) (b : Bool) : ℝ≥0∞ :=
  bernoulliMeasure true false p {b}

private theorem bernoulli_mass_eq (p : unitInterval) (b : Bool) :
    bernoulliMass p b = ENNReal.ofReal (if b then (p : ℝ) else 1 - p) := by
  cases b
  · rw [bernoulliMass, bernoulliMeasure_apply p (measurableSet_singleton false)]
    simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte]
    exact ENNReal.ofReal_coe_nnreal.symm
  · rw [bernoulliMass, bernoulliMeasure_apply p (measurableSet_singleton true)]
    simp only [Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte]
    exact ENNReal.ofReal_coe_nnreal.symm

/-- Binomial singleton masses have full finite support and Pascal recursion,
without excluding either endpoint source rate. -/
theorem binomial_mass_support_and_pascal (p : unitInterval) :
    (∀ n, ∑ i : Fin (n + 1), binomialMass n i.val p = 1) ∧
    (∀ n i, n < i → binomialMass n i p = 0) ∧
    (∀ n, binomialMass (n + 1) 0 p = binomialMass n 0 p * bernoulliMass p false) ∧
    (∀ n i, binomialMass (n + 1) (i + 1) p =
      binomialMass n (i + 1) p * bernoulliMass p false +
        binomialMass n i p * bernoulliMass p true) := by
  have hp : 0 ≤ (p : ℝ) := p.2.1
  have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [Fin.sum_univ_eq_sum_range (fun i => binomialMass n i p) (n + 1)]
    have h := congrArg (fun μ : Measure ℕ => μ Set.univ) (binomial_eq_sum_dirac n p)
    simpa [binomialMass, binomial_singleton,
      Nat.range_succ_eq_Iic, Measure.finsetSum_apply] using h.symm
  · intro n i hi
    simp [binomialMass, binomial_singleton, Nat.choose_eq_zero_of_lt hi]
  · intro n
    simp only [binomialMass, binomial_singleton, bernoulli_mass_eq, Bool.false_eq_true,
      ↓reduceIte, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
      Nat.sub_zero]
    rw [← ENNReal.ofReal_mul (pow_nonneg hq n), pow_succ]
  · intro n i
    simp only [binomialMass, binomial_singleton, bernoulli_mass_eq, Bool.false_eq_true,
      ↓reduceIte]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply congrArg ENNReal.ofReal
    rcases lt_trichotomy i n with hi | rfl | hi
    · have he : n - i = n - (i + 1) + 1 := by omega
      simp only [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right,
        he, pow_succ]
      ring
    · simp [pow_succ]
    · simp [Nat.choose_eq_zero_of_lt hi,
        Nat.choose_eq_zero_of_lt (by omega : n < i + 1),
        Nat.choose_eq_zero_of_lt (Nat.add_lt_add_right hi 1)]

def translatedBinomial (l i I : ℕ) (p : unitInterval) : ℝ≥0∞ :=
  if i ≤ I then binomialMass l (I - i) p else 0

private theorem translated_binomial_above_support (p : unitInterval)
    (l i I : ℕ) (h : i + l < I) : translatedBinomial l i I p = 0 := by
  have hi : i ≤ I := by omega
  simp only [translatedBinomial, if_pos hi]
  exact (binomial_mass_support_and_pascal p).2.1 l (I - i) (by omega)

/-- A finite old-count sum transports one actual Bernoulli answer, with only a
support bound on the old count and no bound on the proposed new count. -/
theorem bounded_one_coin_transport (p : unitInterval) (i l L I : ℕ)
    (h : i + l ≤ L) :
    (∑ x : Fin (L + 1), translatedBinomial l i x.val p *
      (∑ b : Bool, if x.val + (if b then 1 else 0) = I then bernoulliMass p b else 0)) =
        translatedBinomial (l + 1) i I p := by
  classical
  have select (t : ℕ) (c : ℝ≥0∞) :
      (∑ x : Fin (L + 1), if x.val = t then translatedBinomial l i x.val p * c else 0) =
        translatedBinomial l i t p * c := by
    by_cases ht : t ≤ L
    · let a : Fin (L + 1) := ⟨t, by omega⟩
      have he (x : Fin (L + 1)) : x.val = t ↔ x = a :=
        ⟨fun hx => Fin.ext hx, fun hx => congrArg Fin.val hx⟩
      simp_rw [he]
      simp [a]
    · have hz := translated_binomial_above_support p l i t (by omega)
      rw [hz, zero_mul]
      apply Finset.sum_eq_zero
      intro x _
      have hx : x.val ≠ t := by have := x.isLt; omega
      simp [hx]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  simp_rw [mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  cases I with
  | zero =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Finset.sum_const_zero, zero_add]
    rw [select 0]
    by_cases hi : i = 0
    · subst i
      simpa only [translatedBinomial, le_refl, ↓reduceIte, Nat.sub_self] using
        ((binomial_mass_support_and_pascal p).2.2.1 l).symm
    · have hi0 : ¬ i ≤ 0 := by omega
      simp [translatedBinomial, hi0]
  | succ I =>
    simp only [Nat.add_left_inj]
    rw [select I, select (I + 1)]
    by_cases hi : i ≤ I
    · have hi' : i ≤ I + 1 := by omega
      have he : I + 1 - i = (I - i) + 1 := by omega
      simp only [translatedBinomial, if_pos hi, if_pos hi', he]
      exact (add_comm _ _).trans ((binomial_mass_support_and_pascal p).2.2.2 l (I - i)).symm
    · by_cases he : i = I + 1
      · subst i
        simpa only [translatedBinomial, if_neg hi, le_refl, ↓reduceIte, Nat.sub_self,
          zero_mul, zero_add] using ((binomial_mass_support_and_pascal p).2.2.1 l).symm
      · have hi' : ¬ i ≤ I + 1 := by omega
        simp [translatedBinomial, hi, hi']

open D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
  (weight weight_nonneg weight_eq_zero weight_sum)

def hypergeometricWeight (N N' I i : ℕ) : ℝ :=
  if i ≤ I then weight N' N I i else 0

/-- Degree elevation averages over a stochastic row, including zero old
degree and target counts at either boundary. -/
theorem hypergeometric_stochastic_rows (N N' : ℕ) (hN : N ≤ N') (I : Fin (N' + 1)) :
    (∀ i : Fin (N + 1), 0 ≤ hypergeometricWeight N N' I.val i.val) ∧
      (∑ i : Fin (N + 1), hypergeometricWeight N N' I.val i.val) = 1 := by
  classical
  refine ⟨fun i => ?_, ?_⟩
  · unfold hypergeometricWeight
    split
    · exact weight_nonneg _ _ _ _
    · exact le_rfl
  · rw [Fin.sum_univ_eq_sum_range (hypergeometricWeight N N' I.val) (N + 1)]
    have hs : (∑ i ∈ Finset.range (I.val + 1), weight N' N I.val i) = 1 :=
      weight_sum hN (by omega)
    by_cases hi : I.val ≤ N
    · have hsub : Finset.range (I.val + 1) ⊆ Finset.range (N + 1) :=
        Finset.range_subset_range.mpr (by omega)
      calc
        _ = ∑ i ∈ Finset.range (I.val + 1), hypergeometricWeight N N' I.val i := by
          symm
          apply Finset.sum_subset hsub
          intro i _ hi'
          have hnot : ¬ i ≤ I.val := by simpa using hi'
          simp [hypergeometricWeight, hnot]
        _ = ∑ i ∈ Finset.range (I.val + 1), weight N' N I.val i := by
          apply Finset.sum_congr rfl
          intro i hi'
          simp [hypergeometricWeight, Nat.le_of_lt_succ (Finset.mem_range.mp hi')]
        _ = 1 := hs
    · calc
        _ = ∑ i ∈ Finset.range (N + 1), weight N' N I.val i := by
          apply Finset.sum_congr rfl
          intro i hi'
          have hle : i ≤ I.val := by have := Finset.mem_range.mp hi'; omega
          simp [hypergeometricWeight, hle]
        _ = ∑ i ∈ Finset.range (I.val + 1), weight N' N I.val i := by
          apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
          intro i _ hi'
          apply weight_eq_zero
          left
          have hni : ¬ i < N + 1 := by simpa only [Finset.mem_range] using hi'
          omega
        _ = 1 := hs

/-- The hypergeometric split is a multiplication identity even at zero
binomial masses. Only the positive combinatorial denominator is cancelled. -/
theorem zero_safe_binomial_split (N N' i I : ℕ) (hN : N ≤ N')
    (hi : i ≤ N) (hI : I ≤ N') (p : unitInterval) :
    binomialMass N i p * translatedBinomial (N' - N) i I p =
      ENNReal.ofReal (hypergeometricWeight N N' I i) * binomialMass N' I p := by
  by_cases hiI : i ≤ I
  · by_cases hdelta : I - i ≤ N' - N
    · have hp : 0 ≤ (p : ℝ) := p.2.1
      have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
      have hc : (N'.choose I : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hI
      have hpp : (p : ℝ) ^ I = (p : ℝ) ^ i * (p : ℝ) ^ (I - i) := by
        rw [← pow_add, Nat.add_sub_of_le hiI]
      have hqq : (1 - (p : ℝ)) ^ (N' - I) =
          (1 - (p : ℝ)) ^ (N - i) * (1 - (p : ℝ)) ^ (N' - N - (I - i)) := by
        rw [← pow_add]
        congr 1
        omega
      simp only [translatedBinomial, hypergeometricWeight, if_pos hiI,
        binomialMass, binomial_singleton]
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (weight_nonneg N' N I i)]
      apply congrArg ENNReal.ofReal
      rw [hpp, hqq]
      unfold weight
      field_simp
    · have hd : N' - N < I - i := by omega
      have hw : weight N' N I i = 0 := weight_eq_zero (Or.inr hd)
      simp [translatedBinomial, hypergeometricWeight, hiI, hw,
        (binomial_mass_support_and_pascal p).2.1 (N' - N) (I - i) hd]
  · simp [translatedBinomial, hypergeometricWeight, hiI]

def liftTwo (N M N' M' : ℕ) (f : Fin (N + 1) → Fin (M + 1) → ℝ)
    (I : Fin (N' + 1)) (J : Fin (M' + 1)) : ℝ :=
  ∑ i, ∑ j, f i j * hypergeometricWeight N N' I.val i.val *
    hypergeometricWeight M M' J.val j.val

/-- The two-source lift transports the joint count mass through both fresh
blocks; the coefficient array need not factor between the two old counts. -/
theorem two_source_hypergeometric_lift (N M N' M' : ℕ) (hN : N ≤ N') (hM : M ≤ M')
    (f : Fin (N + 1) → Fin (M + 1) → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (p q : unitInterval) (I : Fin (N' + 1)) (J : Fin (M' + 1)) :
    (∑ i, ∑ j, ENNReal.ofReal (f i j) * binomialMass N i.val p * binomialMass M j.val q *
      translatedBinomial (N' - N) i.val I.val p * translatedBinomial (M' - M) j.val J.val q) =
    ENNReal.ofReal (liftTwo N M N' M' f I J) * binomialMass N' I.val p *
      binomialMass M' J.val q := by
  have hGN := (hypergeometric_stochastic_rows N N' hN I).1
  have hGM := (hypergeometric_stochastic_rows M M' hM J).1
  have hcoef (i : Fin (N + 1)) (j : Fin (M + 1)) :
      0 ≤ f i j * hypergeometricWeight N N' I.val i.val *
        hypergeometricWeight M M' J.val j.val :=
    mul_nonneg (mul_nonneg (hf i j) (hGN i)) (hGM j)
  have hl : ENNReal.ofReal (liftTwo N M N' M' f I J) =
      ∑ i, ∑ j, ENNReal.ofReal (f i j * hypergeometricWeight N N' I.val i.val *
        hypergeometricWeight M M' J.val j.val) := by
    rw [liftTwo, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hcoef i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_sum_of_nonneg (fun j _ => hcoef i j)
  rw [hl]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (mul_nonneg (hf i j) (hGN i)), ENNReal.ofReal_mul (hf i j)]
  calc
    _ = ENNReal.ofReal (f i j) *
        (binomialMass N i.val p * translatedBinomial (N' - N) i.val I.val p) *
        (binomialMass M j.val q * translatedBinomial (M' - M) j.val J.val q) := by ac_rfl
    _ = _ := by
      rw [zero_safe_binomial_split N N' i.val I.val hN (by omega) (by omega) p,
        zero_safe_binomial_split M M' j.val J.val hM (by omega) (by omega) q]
      ac_rfl

private theorem translated_binomial_sum (p : unitInterval) (l i L : ℕ) (h : i + l ≤ L) :
    (∑ I : Fin (L + 1), translatedBinomial l i I.val p) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun I => translatedBinomial l i I p) (L + 1)]
  have hsplit : L + 1 = i + (L + 1 - i) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hz : (∑ x ∈ Finset.range i, translatedBinomial l i x p) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [translatedBinomial, not_le.mpr (Finset.mem_range.mp hx)]
  rw [hz, zero_add]
  simp only [translatedBinomial, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  have ht : (∑ x ∈ Finset.range (l + 1), binomialMass l x p) =
      ∑ x ∈ Finset.range (L + 1 - i), binomialMass l x p := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro x _ hx
    have hnx : ¬ x < l + 1 := by simpa only [Finset.mem_range] using hx
    exact (binomial_mass_support_and_pascal p).2.1 l x (by omega)
  rw [← ht, ← Fin.sum_univ_eq_sum_range (fun x => binomialMass l x p) (l + 1)]
  exact (binomial_mass_support_and_pascal p).1 l

def bernsteinEval (N M : ℕ) (f : Fin (N + 1) → Fin (M + 1) → ℝ)
    (p q : unitInterval) : ℝ≥0∞ :=
  ∑ i, ∑ j, ENNReal.ofReal (f i j) * binomialMass N i.val p * binomialMass M j.val q

/-- Elevation preserves evaluation. This algebraic statement does not add
source observations to an execution that has already returned. -/
theorem lift_preserves_bernstein_evaluation (N M N' M' : ℕ) (hN : N ≤ N') (hM : M ≤ M')
    (f : Fin (N + 1) → Fin (M + 1) → ℝ) (hf : ∀ i j, 0 ≤ f i j) (p q : unitInterval) :
    bernsteinEval N' M' (liftTwo N M N' M' f) p q = bernsteinEval N M f p q := by
  unfold bernsteinEval
  simp_rw [← two_source_hypergeometric_lift N M N' M' hN hM f hf p q]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (M' + 1))))
    (t := (Finset.univ : Finset (Fin (N + 1))))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (N' + 1))))
    (t := (Finset.univ : Finset (Fin (N + 1))))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (M' + 1))))
    (t := (Finset.univ : Finset (Fin (M + 1))))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (N' + 1))))
    (t := (Finset.univ : Finset (Fin (M + 1))))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hn := translated_binomial_sum p (N' - N) i.val N' (by omega)
  have hm := translated_binomial_sum q (M' - M) j.val M' (by omega)
  simp only [← Finset.mul_sum, hn, hm, mul_one]

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinBatchExecution
