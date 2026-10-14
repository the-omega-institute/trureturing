/- GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fresh uniform source innovations and the common-rate factory subfamily. -/

import D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliFactoryExecution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.List.OfFn

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryCriticalMoment
open SeededBernoulliFactoryExecution
variable {Seed : Type} [MeasurableSpace Seed]

local notation "Action" => Bool ⊕ (Bool × Bool)
local notation "History" => List (Bool × Bool)
local notation "Uniform" => (volume.restrict (Icc (0 : ℝ) 1) : Measure ℝ)
local notation "RawLaw" => fun {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => Uniform))
local notation "Law" => fun {Seed : Type} [MeasurableSpace Seed]
  (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p))
local notation "Coin" => fun (p : unitInterval) (u : ℝ) => decide (u ≤ (p : ℝ))
local notation "Read" => fun (p q : unitInterval) (source : Bool) (n : ℕ) (tape : ℕ → ℝ) =>
  Coin (if source then q else p) (tape n)
local notation "Returns" => Set.range (fun cell : Bool × Bool => (.inr cell : Action))
local notation "Act" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (n : ℕ) (ω : Seed × (ℕ → ℝ)) =>
  π ω.1 S (acquiredHistory π S (Read p q) n ω)
local notation "Calls" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) => hittingAfter (Act π S p q) Returns 0
local notation "CellAt" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (n : ℕ) (ω : Seed × (ℕ → ℝ)) =>
  match Act π S p q n ω with
  | .inr cell => cell
  | _ => (false, false)
local notation "RawCost" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (a : ℝ) (ω : Seed × (ℕ → ℝ)) =>
  if Calls π S p q ω = ⊤ then (⊤ : ℝ≥0∞) else
    ENNReal.ofReal (((acquiredHistory π S (Read p q)
      ((Calls π S p q ω).untopD 0) ω).length : ℝ) ^ a)
local notation "Bits" => fun {Seed : Type} (p : unitInterval) (ω : Seed × (ℕ → ℝ)) =>
  (ω.1, fun n : ℕ => Coin p (ω.2 n))

private lemma uniform_probability : IsProbabilityMeasure Uniform := by
  constructor
  simp [Real.volume_Icc]

private lemma coin_measurable (p : unitInterval) : Measurable (Coin p) := by
  apply measurable_to_bool
  convert (measurableSet_Iic : MeasurableSet (Iic (p : ℝ))) using 1
  ext u
  simp

private lemma uniform_coin_law (p : unitInterval) :
    (Uniform).map (Coin p) = bernoulliMeasure true false p := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (coin_measurable p) (measurableSet_singleton b),
    Measure.restrict_apply ((coin_measurable p) (measurableSet_singleton b))]
  cases b
  · have he : (Coin p) ⁻¹' {false} ∩ Icc (0 : ℝ) 1 = Ioc (p : ℝ) 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        decide_eq_false_iff_not,
        Set.mem_Icc, Set.mem_Ioc, not_le]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, ⟨p.2.1.trans h.1.le, h.2⟩⟩
    rw [he, Real.volume_Ioc]
    simp [unitInterval.toNNReal, ENNReal.ofReal,
      Real.toNNReal_of_nonneg (sub_nonneg.mpr p.2.2)]
    rfl
  · have he : (Coin p) ⁻¹' {true} ∩ Icc (0 : ℝ) 1 = Icc 0 (p : ℝ) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
        Set.mem_Icc]
      constructor
      · exact fun h => ⟨h.2.1, h.1⟩
      · exact fun h => ⟨h.2, ⟨h.1, h.2.trans p.2.2⟩⟩
    rw [he, Real.volume_Icc]
    simp [unitInterval.toNNReal, ENNReal.ofReal, Real.toNNReal_of_nonneg p.2.1]
    rfl

private lemma seeded_uniform_coin_law (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : unitInterval) : (RawLaw ν).map (Bits p) = Law ν p := by
  have := uniform_probability
  have hm : Measurable (fun tape : ℕ → ℝ => fun n : ℕ => Coin p (tape n)) :=
    Measurable.of_eval (fun n => (coin_measurable p).comp (measurable_pi_apply n))
  have hprod := Measure.map_prod_map ν (Measure.infinitePi (fun _ : ℕ => Uniform))
    measurable_id hm
  rw [Measure.map_id, Measure.infinitePi_map_pi (fun _ : ℕ => Uniform)
    (fun _ => coin_measurable p)] at hprod
  simp_rw [uniform_coin_law] at hprod
  exact hprod.symm

omit [MeasurableSpace Seed] in
private lemma common_rate_history (π : Seed → Bool → History → Action) (S : Bool)
    (p : unitInterval) (n : ℕ) (ω : Seed × (ℕ → ℝ)) :
    acquiredHistory π S (Read p p) n ω =
      acquiredHistory π S (fun _ i tape => tape i) n (Bits p ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [acquiredHistory, ih]
    split
    · rename_i source hs
      cases source <;> rfl
    · rfl

local notation "FlatAct" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  π ω.1 S (acquiredHistory π S (fun _ i tape => tape i) n ω)
local notation "FlatCalls" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool) =>
  hittingAfter (FlatAct π S) Returns 0
local notation "FlatCellAt" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  match FlatAct π S n ω with | .inr cell => cell | _ => (false, false)
local notation "FlatCost" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (a : ℝ) (ω : Seed × (ℕ → Bool)) =>
  if FlatCalls π S ω = ⊤ then (⊤ : ℝ≥0∞) else
    ENNReal.ofReal (((acquiredHistory π S (fun _ i tape => tape i)
      ((FlatCalls π S ω).untopD 0) ω).length : ℝ) ^ a)

omit [MeasurableSpace Seed] in
private lemma common_rate_calls (π : Seed → Bool → History → Action) (S : Bool)
    (p : unitInterval) (ω : Seed × (ℕ → ℝ)) :
    Calls π S p p ω = FlatCalls π S (Bits p ω) := by
  classical
  have he (n : ℕ) : Act π S p p n ω = FlatAct π S n (Bits p ω) :=
    congrArg (π ω.1 S) (common_rate_history π S p n ω)
  let f : ℕ → Prop := fun n => 0 ≤ n ∧ Act π S p p n ω ∈ Returns
  let g : ℕ → Prop := fun n => 0 ≤ n ∧ FlatAct π S n (Bits p ω) ∈ Returns
  have hfg : f = g := by
    funext n
    exact congrArg (fun act : Action => 0 ≤ n ∧ act ∈ Returns) (he n)
  change (if ∃ n, f n then (↑(sInf {n : ℕ | f n}) : WithTop ℕ) else ⊤) =
    (if ∃ n, g n then (↑(sInf {n : ℕ | g n}) : WithTop ℕ) else ⊤)
  rw [hfg]

omit [MeasurableSpace Seed] in
private lemma common_rate_output (π : Seed → Bool → History → Action) (S : Bool)
    (p : unitInterval) (ω : Seed × (ℕ → ℝ)) :
    stoppedValue (CellAt π S p p) (Calls π S p p) ω =
      stoppedValue (FlatCellAt π S) (FlatCalls π S) (Bits p ω) := by
  change (match Act π S p p ((Calls π S p p ω).untopA) ω with
    | .inr cell => cell | _ => (false, false)) = _
  rw [common_rate_calls π S p ω]
  have he := common_rate_history π S p ((FlatCalls π S (Bits p ω)).untopA) ω
  change (match π ω.1 S (acquiredHistory π S (Read p p)
    ((FlatCalls π S (Bits p ω)).untopA) ω) with
    | .inr cell => cell | _ => (false, false)) = _
  rw [he]
  rfl

omit [MeasurableSpace Seed] in
private lemma common_rate_cost (π : Seed → Bool → History → Action) (S : Bool)
    (p : unitInterval) (a : ℝ) (ω : Seed × (ℕ → ℝ)) :
    RawCost π S p p a ω = FlatCost π S a (Bits p ω) := by
  change (if Calls π S p p ω = ⊤ then (⊤ : ℝ≥0∞) else
    ENNReal.ofReal (((acquiredHistory π S (Read p p)
      ((Calls π S p p ω).untopD 0) ω).length : ℝ) ^ a)) = _
  have hc := common_rate_calls π S p ω
  simp only [hc]
  rw [common_rate_history π S p ((FlatCalls π S (Bits p ω)).untopD 0) ω]

private lemma common_rate_output_law (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p : unitInterval) (cell : Bool × Bool) :
    (RawLaw ν).real ((stoppedValue (CellAt π S p p) (Calls π S p p)) ⁻¹' {cell}) =
      (Law ν p).real ((stoppedValue (FlatCellAt π S) (FlatCalls π S)) ⁻¹' {cell}) := by
  have hm : Measurable (fun ω : Seed × (ℕ → ℝ) => Bits p ω) := measurable_fst.prodMk
    (Measurable.of_eval (fun n => (coin_measurable p).comp
      ((measurable_pi_apply n).comp measurable_snd)))
  have ho := (output_stopped_measurable π hπ S).mono
    (calls_stopping π hπ S).measurableSpace_le le_rfl
  have hmap := seeded_uniform_coin_law ν p
  calc
    _ = (RawLaw ν).real ((Bits p) ⁻¹'
        ((stoppedValue (FlatCellAt π S) (FlatCalls π S)) ⁻¹' {cell})) := by
      apply measureReal_congr
      exact ae_of_all _ (fun ω => by
        change (stoppedValue (CellAt π S p p) (Calls π S p p) ω = cell) =
          (stoppedValue (FlatCellAt π S) (FlatCalls π S) (Bits p ω) = cell)
        rw [common_rate_output π S p ω])
    _ = _ := by
      rw [← hmap]
      exact (map_measureReal_apply hm (ho (measurableSet_singleton cell))).symm


private lemma common_rate_cost_law (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p : unitInterval) (a : ℝ) :
    (∫⁻ ω, RawCost π S p p a ω ∂(RawLaw ν)) =
      ∫⁻ ω, FlatCost π S a ω ∂(Law ν p) := by
  have hm : Measurable (fun ω : Seed × (ℕ → ℝ) => Bits p ω) := measurable_fst.prodMk
    (Measurable.of_eval (fun n => (coin_measurable p).comp
      ((measurable_pi_apply n).comp measurable_snd)))
  have hM := (calls_stopping π hπ S).measurable.mono
    (calls_stopping π hπ S).measurableSpace_le le_rfl
  have hc : Measurable (FlatCost π S a) := by
    have he : FlatCost π S a = fun ω =>
        if FlatCalls π S ω = ⊤ then (⊤ : ℝ≥0∞) else
          ENNReal.ofReal ((((FlatCalls π S ω).untopD 0 : ℕ) : ℝ) ^ a) := by
      funext ω
      exact (cost_eq_record_cost π S a ω).symm
    rw [he]
    exact (Measurable.of_discrete : Measurable (fun t : WithTop ℕ =>
      if t = ⊤ then (⊤ : ℝ≥0∞) else ENNReal.ofReal (((t.untopD 0 : ℕ) : ℝ) ^ a))).comp hM
  rw [← seeded_uniform_coin_law ν p, lintegral_map hc hm]
  apply lintegral_congr
  intro ω
  exact common_rate_cost π S p a ω

local notation "Prefix" => fun (t : ℕ → Bool × Bool) (n : ℕ) =>
  List.ofFn (fun i : Fin n => t i)
local notation "SeedSection" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (t : ℕ → Bool × Bool) (n : ℕ) =>
  {seed | ∀ i < n, π seed S (Prefix t i) = .inl (t i).1}
local notation "TapeSection" => fun (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) =>
  Set.pi (Finset.range n) (fun i => (Coin (if (t i).1 then q else p)) ⁻¹' {(t i).2})
local notation "TraceEvent" => fun {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) =>
  {ω : Seed × (ℕ → ℝ) | ∀ i < n,
    Act π S p q i ω = .inl (t i).1 ∧ Read p q (t i).1 i ω.2 = (t i).2}

omit [MeasurableSpace Seed] in
private lemma history_of_trace (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) (ω : Seed × (ℕ → ℝ))
    (htrace : ω ∈ TraceEvent π S p q t n) :
    acquiredHistory π S (Read p q) n ω = Prefix t n := by
  induction n with
  | zero => simp [acquiredHistory]
  | succ n ih =>
    have hprev := ih (fun i hi => htrace i (Nat.lt_succ_of_lt hi))
    have hn := htrace n (Nat.lt_succ_self n)
    have ha : π ω.1 S (acquiredHistory π S (Read p q) n ω) = .inl (t n).1 := hn.1
    have hb : Read p q (t n).1 n ω.2 = (t n).2 := hn.2
    rw [acquiredHistory, ha]
    change acquiredHistory π S (Read p q) n ω ++
      [((t n).1, Read p q (t n).1 n ω.2)] = Prefix t (n + 1)
    rw [hb, hprev]
    simpa [List.concat_eq_append] using
      (List.ofFn_succ' (fun i : Fin (n + 1) => t i)).symm

omit [MeasurableSpace Seed] in
private lemma trace_event_sections (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) :
    TraceEvent π S p q t n = (SeedSection π S t n) ×ˢ (TapeSection p q t n) := by
  ext ω
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · intro i hi
      have hp := history_of_trace π S p q t i ω
        (fun j hj => ht j (hj.trans hi))
      have ha := (ht i hi).1
      change π ω.1 S (acquiredHistory π S (Read p q) i ω) = .inl (t i).1 at ha
      rwa [hp] at ha
    · intro i hi
      exact (ht i (Finset.mem_range.mp hi)).2
  · rintro ⟨hseed, hbits⟩
    have hh : ∀ k ≤ n, acquiredHistory π S (Read p q) k ω = Prefix t k := by
      intro k
      induction k with
      | zero => intro hk; simp [acquiredHistory]
      | succ k ih =>
        intro hk
        have hp := ih (by omega)
        have ha := hseed k (by omega)
        have hb : Read p q (t k).1 k ω.2 = (t k).2 :=
          hbits k (Finset.mem_range.mpr (by omega))
        simp only [acquiredHistory, hp, ha, hb]
        rw [List.ofFn_succ']
        simp
    intro i hi
    constructor
    · change π ω.1 S (acquiredHistory π S (Read p q) i ω) = .inl (t i).1
      rw [hh i hi.le]
      exact hseed i hi
    · exact hbits i (Finset.mem_range.mpr hi)

/-- A fixed labelled source trace has the prescribed independent Bernoulli
likelihood. Adaptive source choices and private memory stay in the same seed
section, which is independent of both unknown source rates. -/
theorem native_source_trace_law (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p q : unitInterval)
    (t : ℕ → Bool × Bool) (n : ℕ) (D : Set Seed) (hD : MeasurableSet D) :
    MeasurableSet ((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' D) ∧
    (RawLaw ν) ((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' D) =
      ν ((SeedSection π S t n) ∩ D) *
        ∏ i ∈ Finset.range n, (bernoulliMeasure true false
          (if (t i).1 then q else p)) {(t i).2} := by
  have := uniform_probability
  have hs : MeasurableSet (SeedSection π S t n) := by
    change MeasurableSet {seed | ∀ i, ∀ _ : i < n,
      π seed S (Prefix t i) = .inl (t i).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i : ℕ => MeasurableSet.iInter (fun hi : i < n =>
      (hπ S (Prefix t i)) (action_singleton_measurable (.inl (t i).1))))
  have he : (TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' D =
      ((SeedSection π S t n) ∩ D) ×ˢ (TapeSection p q t n) := by
    rw [trace_event_sections]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage]
    tauto
  rw [he]
  refine ⟨(hs.inter hD).prod (MeasurableSet.pi (Finset.countable_toSet _)
    (fun i hi => (coin_measurable _) (measurableSet_singleton _))), ?_⟩
  rw [Measure.prod_prod]
  rw [Measure.infinitePi_pi _ (fun i hi =>
    (coin_measurable _) (measurableSet_singleton _))]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [← uniform_coin_law, Measure.map_apply (coin_measurable _)
    (measurableSet_singleton _)]

local notation "RowLaw" => fun table : (Bool × History) → PMF Action =>
  Measure.infinitePi (fun row => (table row).toMeasure)
local notation "TablePolicy" => fun (seed : (Bool × History) → Action) S h => seed (S, h)

omit [MeasurableSpace Seed] in
private lemma trace_action_seed_event (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) (a : Action) :
    (TraceEvent π S p q t n) ∩ {ω | Act π S p q n ω = a} =
      (TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' {seed | π seed S (Prefix t n) = a} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor <;> rintro ⟨ht, ha⟩ <;> refine ⟨ht, ?_⟩
  · change π ω.1 S (Prefix t n) = a
    change π ω.1 S (acquiredHistory π S (Read p q) n ω) = a at ha
    rwa [history_of_trace π S p q t n ω ht] at ha
  · change π ω.1 S (acquiredHistory π S (Read p q) n ω) = a
    rwa [history_of_trace π S p q t n ω ht]

omit [MeasurableSpace Seed] in
private lemma trace_return_call_count (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) (cell : Bool × Bool)
    (ω : Seed × (ℕ → ℝ)) (ht : ω ∈ TraceEvent π S p q t n)
    (ha : Act π S p q n ω = .inr cell) : Calls π S p q ω = (n : WithTop ℕ) := by
  apply le_antisymm
  · exact hittingAfter_le_of_mem (Nat.zero_le n) ⟨cell, ha.symm⟩
  · apply le_of_not_gt
    intro hlt
    obtain ⟨i, hi, y, hy⟩ := hittingAfter_lt_iff.mp hlt
    have hc := (ht i hi.2).1
    rw [hc] at hy
    simp at hy

/-- On each reached labelled history, an actual next call has the declared
Bernoulli answer kernel even when its source is chosen adaptively from the
complete private seed and acquired record. The equality also covers null nodes. -/
theorem native_source_conditional_kernel (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p q : unitInterval)
    (t : ℕ → Bool × Bool) (n : ℕ) (source b : Bool)
    (D : Set Seed) (hD : MeasurableSet D) :
    (RawLaw ν) ((((TraceEvent π S p q t n) ∩ {ω | Act π S p q n ω = .inl source}) ∩
      Prod.fst ⁻¹' D) ∩ {ω | Read p q source n ω.2 = b}) =
      (RawLaw ν) (((TraceEvent π S p q t n) ∩ {ω | Act π S p q n ω = .inl source}) ∩
        Prod.fst ⁻¹' D) *
        (bernoulliMeasure true false (if source then q else p)) {b} := by
  have := uniform_probability
  let E : Set Seed := {seed | π seed S (Prefix t n) = .inl source} ∩ D
  have hE : MeasurableSet E :=
    ((hπ S (Prefix t n)) (action_singleton_measurable (.inl source))).inter hD
  have hbase := (native_source_trace_law π hπ S ν p q t n E hE).2
  rw [trace_action_seed_event π S p q t n (.inl source)]
  have hseed : ((TraceEvent π S p q t n) ∩
      Prod.fst ⁻¹' {seed | π seed S (Prefix t n) = .inl source}) ∩ Prod.fst ⁻¹' D =
      (TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' E := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, E]
    tauto
  rw [hseed]
  change (RawLaw ν) (((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' E) ∩
    {ω | Read p q source n ω.2 = b}) =
      (RawLaw ν) ((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' E) * _
  rw [hbase]
  have he : ((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' E) ∩
      {ω | Read p q source n ω.2 = b} =
      ((SeedSection π S t n) ∩ E) ×ˢ
        ((TapeSection p q t n) ∩ {tape | Coin (if source then q else p) (tape n) = b}) := by
    rw [trace_event_sections]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  change (RawLaw ν) (((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' E) ∩
    {ω | Read p q source n ω.2 = b}) = _
  rw [he, Measure.prod_prod]
  let regions : ℕ → Set ℝ := fun i =>
    if i = n then (Coin (if source then q else p)) ⁻¹' {b}
      else (Coin (if (t i).1 then q else p)) ⁻¹' {(t i).2}
  have hregions : (TapeSection p q t n) ∩
      {tape | Coin (if source then q else p) (tape n) = b} =
        Set.pi (Finset.range (n + 1)) regions := by
    ext tape
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ht, hb⟩ i hi
      by_cases hin : i = n
      · subst i; simpa [regions] using hb
      · have hii : i < n := by omega
        simpa [regions, hin] using ht i hii
    · intro ht
      constructor
      · intro i hi
        have hin : i ≠ n := by omega
        simpa [regions, hin] using ht i (Nat.lt_succ_of_lt hi)
      · simpa [regions] using ht n (Nat.lt_succ_self n)
  rw [hregions, Measure.infinitePi_pi _ (fun i hi => by
    dsimp [regions]
    split <;> exact (coin_measurable _) (measurableSet_singleton _)), Finset.prod_range_succ]
  have hp : (∏ i ∈ Finset.range n, Uniform (regions i)) =
      ∏ i ∈ Finset.range n,
        (bernoulliMeasure true false (if (t i).1 then q else p)) {(t i).2} := by
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i ≠ n := by have := Finset.mem_range.mp hi; omega
    simp only [regions, if_neg hin]
    rw [← uniform_coin_law, Measure.map_apply (coin_measurable _)
      (measurableSet_singleton _)]
  have hn : Uniform (regions n) =
      (bernoulliMeasure true false (if source then q else p)) {b} := by
    simp only [regions, if_pos rfl]
    rw [← uniform_coin_law, Measure.map_apply (coin_measurable _)
      (measurableSet_singleton _)]
  rw [hp, hn]
  simp only [mul_assoc]

/-- A reached word changes the private-seed posterior only through its seed
section; its nonzero source likelihood cancels exactly. -/
private lemma private_seed_posterior (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p q : unitInterval)
    (t : ℕ → Bool × Bool) (n : ℕ) (D : Set Seed) (hD : MeasurableSet D)
    (hL : (∏ i ∈ Finset.range n,
      (bernoulliMeasure true false (if (t i).1 then q else p)) {(t i).2}) ≠ 0) :
    (RawLaw ν) ((TraceEvent π S p q t n) ∩ Prod.fst ⁻¹' D) /
      (RawLaw ν) (TraceEvent π S p q t n) =
        ν ((SeedSection π S t n) ∩ D) / ν (SeedSection π S t n) := by
  have hnum := (native_source_trace_law π hπ S ν p q t n D hD).2
  have hden := (native_source_trace_law π hπ S ν p q t n Set.univ
    MeasurableSet.univ).2
  simp only [Set.preimage_univ, Set.inter_univ] at hden
  rw [hnum, hden]
  exact ENNReal.mul_div_mul_right _ _ hL
    (ENNReal.prod_ne_top (fun i hi => measure_ne_top _ _))

private lemma table_seed_section_law (table : (Bool × History) → PMF Action)
    (S : Bool) (t : ℕ → Bool × Bool) (n : ℕ) (a : Action) :
    (RowLaw table) ((SeedSection TablePolicy S t n) ∩
      {seed | seed (S, Prefix t n) = a}) =
      (∏ i ∈ Finset.range n, table (S, Prefix t i) (.inl (t i).1)) *
        table (S, Prefix t n) a := by
  let row : ℕ → Bool × History := fun i => (S, Prefix t i)
  have hi : Function.Injective row := by
    intro i j hij
    have hl := congrArg (fun r : Bool × History => r.2.length) hij
    simpa [row] using hl
  let act : ℕ → Action := fun i => if i < n then .inl (t i).1 else a
  let Q : Set (ℕ → Action) := Set.pi (Finset.range (n + 1)) (fun i => {act i})
  have hQ : MeasurableSet Q :=
    MeasurableSet.pi (Finset.countable_toSet _) (fun i hi => action_singleton_measurable _)
  have he : ((SeedSection TablePolicy S t n) ∩
      {seed | seed (S, Prefix t n) = a}) =
      (fun seed : (Bool × History) → Action => fun i => seed (row i)) ⁻¹' Q := by
    ext seed
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Q, Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, ha⟩ i hi
      by_cases hin : i < n
      · simpa [row, act, hin] using hp i hin
      · have heq : i = n := by omega
        subst i
        simpa [row, act] using ha
    · intro hp
      constructor
      · intro i hi
        simpa [row, act, hi] using hp i (Nat.lt_succ_of_lt hi)
      · simpa [row, act] using hp n (Nat.lt_succ_self n)
  rw [he, ← Measure.map_apply (by fun_prop) hQ,
    Measure.map_infinitePi_infinitePi_of_inj hi]
  rw [Measure.infinitePi_pi _ (fun i hi => action_singleton_measurable _),
    Finset.prod_range_succ]
  simp only [PMF.toMeasure_apply_singleton _ _ (action_singleton_measurable _)]
  have hp : (∏ i ∈ Finset.range n, table (row i) (act i)) =
      ∏ i ∈ Finset.range n, table (S, Prefix t i) (.inl (t i).1) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [row, act, Finset.mem_range.mp hi]
  simp [row, act, hp]

/-- Independent private action coordinates realize every finite labelled leaf
of an arbitrary real-probability policy table, with the exact source likelihood
and without a bound on the possible number of calls. -/
theorem native_policy_table_leaf_law (table : (Bool × History) → PMF Action)
    (S : Bool) (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) (a : Action) :
    (RawLaw (RowLaw table)) ((TraceEvent TablePolicy S p q t n) ∩
      {ω | Act TablePolicy S p q n ω = a}) =
      ((∏ i ∈ Finset.range n, table (S, Prefix t i) (.inl (t i).1)) *
        table (S, Prefix t n) a) *
      ∏ i ∈ Finset.range n,
        (bernoulliMeasure true false (if (t i).1 then q else p)) {(t i).2} := by
  have hD : MeasurableSet {seed : (Bool × History) → Action | seed (S, Prefix t n) = a} := by
    change MeasurableSet ((fun seed : (Bool × History) → Action => seed (S, Prefix t n)) ⁻¹' {a})
    exact (measurable_pi_apply (S, Prefix t n)) (action_singleton_measurable a)
  have hb := (native_source_trace_law TablePolicy (fun S h => measurable_pi_apply (S, h))
    S (RowLaw table) p q t n
      {seed : (Bool × History) → Action | seed (S, Prefix t n) = a}
      hD).2
  rw [trace_action_seed_event TablePolicy S p q t n a]
  rw [table_seed_section_law] at hb
  exact hb

local notation "IdentityRows" => fun table : (Bool × History) → PMF Action =>
  ∀ S h a, table (S, h) a ≠ 0 →
    (h = [] → a = .inl S) ∧
      ∀ cell : Bool × Bool, a = .inr cell → h.head? = some (S, cell.1)

omit [MeasurableSpace Seed] in
private lemma history_actual_first_answer (π : Seed → Bool → History → Action)
    (S : Bool) {Tape : Type} (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape)
    (hroot : π ω.1 S [] = .inl S) (n : ℕ) :
    (acquiredHistory π S answer (n + 1) ω).head? = some (S, answer S 0 ω.2) := by
  induction n with
  | zero => simp [acquiredHistory, hroot]
  | succ n ih =>
    rw [acquiredHistory]
    split
    · have hne : acquiredHistory π S answer (n + 1) ω ≠ [] := by
        intro he
        simp only [he, List.head?_nil, reduceCtorEq] at ih
      rw [List.head?_append_of_ne_nil _ hne]
      exact ih
    · exact ih

private lemma table_rows_supported (table : (Bool × History) → PMF Action) :
    ∀ᵐ seed ∂(RowLaw table), ∀ row : Bool × History, table row (seed row) ≠ 0 := by
  let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
  apply ae_all_iff.mpr
  intro row
  have hs : ∀ᵐ a ∂(table row).toMeasure, a ∈ (table row).support := by
    apply (ae_mem_iff_measure_eq (table row).support_countable.measurableSet.nullMeasurableSet).mpr
    simpa using ((table row).toMeasure_apply_eq_one_iff
      (table row).support_countable.measurableSet).mpr Set.Subset.rfl
  apply ae_of_ae_map (μ := RowLaw table) (p := fun a : Action => table row a ≠ 0)
    (measurable_pi_apply row).aemeasurable
  rw [Measure.infinitePi_map_eval]
  exact hs

/-- The identity face of a real policy table makes the first global call use
the requested source, and every finite return contains that actual first answer.
The same private-seed null set works for every pair of source rates. -/
theorem native_policy_table_identity (table : (Bool × History) → PMF Action)
    (hidentity : IdentityRows table) :
    ∀ᵐ seed ∂(RowLaw table), ∀ (S : Bool) (p q : unitInterval) (tape : ℕ → ℝ),
      Act TablePolicy S p q 0 (seed, tape) = .inl S ∧
      ∀ n (cell : Bool × Bool), Act TablePolicy S p q n (seed, tape) = .inr cell →
        cell.1 = Read p q S 0 tape := by
  filter_upwards [table_rows_supported table] with seed hseed
  intro S p q tape
  have hroot : seed (S, []) = .inl S :=
    (hidentity S [] _ (hseed (S, []))).1 rfl
  refine ⟨hroot, ?_⟩
  intro n cell ha
  have hh : (acquiredHistory TablePolicy S (Read p q) n (seed, tape)).head? =
      some (S, cell.1) :=
    (hidentity S _ _ (hseed (S, acquiredHistory TablePolicy S (Read p q) n
      (seed, tape)))).2 cell ha
  cases n with
  | zero => simp [acquiredHistory] at hh
  | succ n =>
    have hf := history_actual_first_answer TablePolicy S (Read p q) (seed, tape) hroot n
    have he : (S, cell.1) = (S, Read p q S 0 tape) := Option.some.inj (hh.symm.trans hf)
    exact congrArg Prod.snd he

private lemma finite_return_cell_law (π : Seed → Bool → History → Action) (S : Bool)
    (ν : Measure Seed) (p q : unitInterval)
    (hfinite : ∀ᵐ ω ∂(RawLaw ν), Calls π S p q ω ≠ ⊤) (cell : Bool × Bool) :
    (RawLaw ν).real {ω | ∃ n : ℕ,
      Calls π S p q ω = (n : WithTop ℕ) ∧ Act π S p q n ω = .inr cell} =
      (RawLaw ν).real ((stoppedValue (CellAt π S p q) (Calls π S p q)) ⁻¹' {cell}) := by
  apply measureReal_congr
  filter_upwards [hfinite] with ω hω
  cases ht : Calls π S p q ω with
  | top => exact False.elim (hω ht)
  | coe n =>
    have hm : Act π S p q n ω ∈ Returns := by
      simpa [ht] using
        (hittingAfter_mem_set_of_ne_top (u := Act π S p q) (s := Returns) (n := 0) hω)
    obtain ⟨y, hy⟩ := hm
    apply propext
    change (∃ j : ℕ, Calls π S p q ω = (j : WithTop ℕ) ∧
      Act π S p q j ω = .inr cell) ↔
        stoppedValue (CellAt π S p q) (Calls π S p q) ω = cell
    have hout : stoppedValue (CellAt π S p q) (Calls π S p q) ω = y := by
      change (match Act π S p q ((Calls π S p q ω).untopA) ω with
        | .inr cell => cell | _ => (false, false)) = y
      simp only [ht]
      change (match Act π S p q n ω with
        | .inr cell => cell | _ => (false, false)) = y
      rw [← hy]
    constructor
    · rintro ⟨j, hj, ha⟩
      have hjn : j = n := WithTop.coe_injective (hj.symm.trans ht)
      subst j
      exact hout.trans (Sum.inr.inj (hy.trans ha))
    · intro hc
      exact ⟨n, ht, hy.symm.trans (congrArg Sum.inr (hout.symm.trans hc))⟩

omit [MeasurableSpace Seed] in
private lemma raw_cost_eq_total_calls (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (a : ℝ) (ω : Seed × (ℕ → ℝ)) :
    RawCost π S p q a ω =
      if Calls π S p q ω = ⊤ then (⊤ : ℝ≥0∞) else
        ENNReal.ofReal (((Calls π S p q ω).untopD 0 : ℕ) ^ a : ℝ) := by
  cases ht : Calls π S p q ω with
  | top => simp [ht]
  | coe n =>
    have hlen := acquired_history_length_at_return π S (Read p q) ω n ht
    simp [ht, hlen]

/-- The fixed known parameters of the two-source factory. -/
structure FactoryParameters where
  B : ℝ
  C : ℝ
  κ : ℝ
  g : ℝ
  β : ℝ
  allowed_B : B = 2 ∨ B = 4
  C_bounds : 1 ≤ C ∧ C ≤ 1024 / 225
  κ_bounds : 0 < κ ∧ κ ≤ -Real.log (Real.sqrt (3 / 4))
  g_bounds : 0 < g ∧ g ≤ Real.exp (-κ) - Real.exp (-κ) ^ 2
  β_pos : 0 < β
  β_noninteger : ∀ j : ℕ, β ≠ j

/-- Every legal world retains its branch, coefficient and positive gain. -/
structure World (P : FactoryParameters) where
  j : Fin 2
  r : ℝ
  r_bounds : r ∈ Icc (Real.exp (-P.κ) ^ 2 + P.g) 1
  h : ℝ
  h_bounds : h ∈ Ioc 0 (1 / 4 : ℝ)

local notation "Rate" => fun (P : FactoryParameters) (w : World P) (source : Bool) =>
  Set.projIcc 0 1 zero_le_one
    ((1 - w.h * (if source then 1 else Real.exp (-P.κ) ^ (w.j : ℕ) * w.r) / P.C) / P.B)
local notation "Target" => fun (P : FactoryParameters) (w : World P) (S : Bool)
  (cell : Bool × Bool) =>
  (if cell.1 then (Rate P w S : ℝ) else 1 - (Rate P w S : ℝ)) / 2 +
    (w.h ^ P.β / 16) * (if cell.1 = cell.2 then 1 else -1)

private lemma source_rate_bounds_and_value (P : FactoryParameters) (w : World P)
    (source : Bool) :
    (Rate P w source : ℝ) ∈ Icc (3 / (4 * P.B)) (1 / P.B) ∧
    (Rate P w source : ℝ) =
      (1 - w.h * (if source then 1 else Real.exp (-P.κ) ^ (w.j : ℕ) * w.r) / P.C) / P.B := by
  let c := if source then 1 else Real.exp (-P.κ) ^ (w.j : ℕ) * w.r
  have he0 : 0 ≤ Real.exp (-P.κ) := (Real.exp_pos _).le
  have he1 : Real.exp (-P.κ) ≤ 1 :=
    (Real.exp_lt_one_iff.mpr (by linarith [P.κ_bounds.1])).le
  have hr0 : 0 ≤ w.r := (add_nonneg (sq_nonneg _) P.g_bounds.1.le).trans w.r_bounds.1
  have hc0 : 0 ≤ c := by
    cases source with
    | false => exact mul_nonneg (pow_nonneg he0 _) hr0
    | true => norm_num [c]
  have hc1 : c ≤ 1 := by
    cases source with
    | false => exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ he0 he1) hr0).trans_eq
        (one_mul w.r)).trans w.r_bounds.2
    | true => norm_num [c]
  have hC : 0 < P.C := lt_of_lt_of_le (by norm_num) P.C_bounds.1
  have hratio0 : 0 ≤ w.h * c / P.C := div_nonneg (mul_nonneg w.h_bounds.1.le hc0) hC.le
  have hratio1 : w.h * c / P.C ≤ 1 / 4 :=
    (div_le_self (mul_nonneg w.h_bounds.1.le hc0) P.C_bounds.1).trans
      ((mul_le_of_le_one_right w.h_bounds.1.le hc1).trans w.h_bounds.2)
  have hB : 1 ≤ P.B := by
    rcases P.allowed_B with hB | hB <;> rw [hB] <;> norm_num
  have hBp : 0 < P.B := lt_of_lt_of_le (by norm_num) hB
  have hv : (Rate P w source : ℝ) = (1 - w.h * c / P.C) / P.B := by
    apply congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one) ?_)
    exact ⟨div_nonneg (by linarith) hBp.le,
      (div_le_one hBp).mpr (by linarith)⟩
  refine ⟨?_, hv⟩
  rw [hv]
  constructor
  · have hl := div_le_div_of_nonneg_right (show (3 / 4 : ℝ) ≤ 1 - w.h * c / P.C by
      linarith) hBp.le
    convert hl using 1
    ring
  · exact div_le_div_of_nonneg_right (by linarith) hBp.le

private lemma coefficient_lower_le_one (P : FactoryParameters) :
    Real.exp (-P.κ) ^ 2 + P.g ≤ 1 := by
  have he : Real.exp (-P.κ) < 1 := Real.exp_lt_one_iff.mpr (by linarith [P.κ_bounds.1])
  linarith [P.g_bounds.2]

private lemma factory_target_probability (P : FactoryParameters) (w : World P) (S : Bool) :
    (∀ cell : Bool × Bool, (1 / 32 : ℝ) ≤ Target P w S cell) ∧
      (∑ cell : Bool × Bool, Target P w S cell) = 1 := by
  have hu := (source_rate_bounds_and_value P w S).1
  have hl : (3 / 16 : ℝ) ≤ 3 / (4 * P.B) := by
    rcases P.allowed_B with hb | hb <;> norm_num [hb]
  have hr : 1 / P.B ≤ (1 / 2 : ℝ) := by
    rcases P.allowed_B with hb | hb <;> norm_num [hb]
  have he0 : 0 ≤ w.h ^ P.β := Real.rpow_nonneg w.h_bounds.1.le _
  have he1 : w.h ^ P.β ≤ 1 :=
    Real.rpow_le_one w.h_bounds.1.le (by linarith [w.h_bounds.2]) P.β_pos.le
  refine ⟨?_, target_mass _ _ _⟩
  intro cell
  rcases cell with ⟨x, z⟩
  cases x <;> cases z <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    <;> linarith [hl.trans hu.1, hu.2.trans hr]

private lemma legal_source_word_ne_zero (P : FactoryParameters) (w : World P)
    (t : ℕ → Bool × Bool) (n : ℕ) :
    (∏ i ∈ Finset.range n, (bernoulliMeasure true false
      (if (t i).1 then Rate P w true else Rate P w false)) {(t i).2}) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  let u : unitInterval := if (t i).1 then Rate P w true else Rate P w false
  have hu : (u : ℝ) ∈ Icc (3 / (4 * P.B)) (1 / P.B) := by
    cases hb : (t i).1 <;> simpa [u, hb] using
      (source_rate_bounds_and_value P w (t i).1).1
  have hB : 0 < P.B := by
    rcases P.allowed_B with hb | hb <;> norm_num [hb]
  have hu0 : 0 < (u : ℝ) :=
    (div_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (by norm_num) hB)).trans_le hu.1
  have hu1 : (u : ℝ) < 1 := hu.2.trans_lt (by
    rcases P.allowed_B with hb | hb <;> norm_num [hb])
  apply (measureReal_ne_zero_iff (measure_ne_top _ _)).mp
  cases hb : (t i).2
  · change (bernoulliMeasure true false u).real {false} ≠ 0
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem u (measurableSet_singleton false)
      (by simp) (by simp)]
    exact (sub_pos.mpr hu1).ne'
  · change (bernoulliMeasure true false u).real {true} ≠ 0
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem u (measurableSet_singleton true)
      (by simp) (by simp)]
    exact hu0.ne'

local notation "CommonWorld" => fun (P : FactoryParameters)
  (h : {h : ℝ // h ∈ Ioc 0 (1 / 4 : ℝ)}) =>
  (⟨0, 1, ⟨coefficient_lower_le_one P, le_rfl⟩, h.1, h.2⟩ : World P)

set_option maxHeartbeats 800000 in
-- The complete fixed-parameter, world and policy telescope contains the full execution terms.
/-- Complete-output accuracy for every legal world forces a logarithmic lower
bound on the maximum total-call fractional cost. Both sources use fresh uniform
innovations in actual acquisition order, and all calls remain in the record. -/
theorem native_factory_logarithmic_total_call_cost (P : FactoryParameters) (m : ℕ)
    (hm : P.β / 2 < (m : ℝ)) :
    ∃ k : ℝ, 0 < k ∧ ∃ δ₀ : ℝ, δ₀ ∈ Ioo 0 1 ∧
      ∀ (ν : Measure Seed), IsProbabilityMeasure ν →
      ∀ (π : Seed → Bool → History → Action),
      (∀ S h, Measurable (fun seed => π seed S h)) →
      ∀ δ : ℝ, δ ∈ Ioo 0 δ₀ →
      (∀ (w : World P) (S : Bool), D5.S3.TotalVariation.Pinsker.totalVariation
        (fun cell : Bool × Bool => (RawLaw ν).real
          ((stoppedValue (CellAt π S (Rate P w false) (Rate P w true))
            (Calls π S (Rate P w false) (Rate P w true))) ⁻¹' {cell}))
        (Target P w S) ≤ δ) →
      ENNReal.ofReal (k * Real.log δ⁻¹) ≤
        ⨆ S : Bool, ⨆ w : World P,
          ∫⁻ ω, RawCost π S (Rate P w false) (Rate P w true) (P.β / 2) ω ∂(RawLaw ν) := by
  obtain ⟨k, hk, δ₀, hδ₀, hbound⟩ := seeded_policy_logarithmic_total_call_cost
    (Seed := Seed) P.B P.C P.β P.allowed_B P.C_bounds.1 P.β_pos P.β_noninteger m hm
  refine ⟨k, hk, δ₀, hδ₀, ?_⟩
  intro ν hν π hπ δ hδ htv
  have := hν
  have hflat : ∀ S h, h ∈ Ioc 0 (1 / 4 : ℝ) →
      D5.S3.TotalVariation.Pinsker.totalVariation
        (fun cell : Bool × Bool =>
          (Law ν (Set.projIcc 0 1 zero_le_one ((1 - h / P.C) / P.B))).real
            ((stoppedValue (FlatCellAt π S) (FlatCalls π S)) ⁻¹' {cell}))
        (fun cell : Bool × Bool =>
          (if cell.1 then (1 - h / P.C) / P.B else 1 - (1 - h / P.C) / P.B) / 2 +
            (h ^ P.β / 16) * (if cell.1 = cell.2 then 1 else -1)) ≤ δ := by
    intro S h hh
    let w := CommonWorld P (⟨h, hh⟩ : {h : ℝ // h ∈ Ioc 0 (1 / 4 : ℝ)})
    have ht := htv w S
    dsimp [w] at ht
    simp only [pow_zero, mul_one, ite_self] at ht
    let q := Set.projIcc 0 1 zero_le_one ((1 - h / P.C) / P.B)
    have hout : (fun cell : Bool × Bool => (RawLaw ν).real
        ((stoppedValue (CellAt π S q q) (Calls π S q q)) ⁻¹' {cell})) =
      (fun cell : Bool × Bool => (Law ν q).real
        ((stoppedValue (FlatCellAt π S) (FlatCalls π S)) ⁻¹' {cell})) := by
      funext cell
      exact common_rate_output_law π hπ S ν q cell
    simp only [ite_self] at hout
    rw [hout] at ht
    have hrate : (Set.projIcc 0 1 zero_le_one ((1 - h / P.C) / P.B) : ℝ) =
        (1 - h / P.C) / P.B := by
      simpa [w] using (source_rate_bounds_and_value P w S).2
    simpa only [hrate] using ht
  have hb := hbound ν hν π hπ δ hδ hflat
  apply hb.trans
  apply iSup_le
  intro S
  apply iSup_le
  intro h
  have hcost := common_rate_cost_law π hπ S ν
    (Set.projIcc 0 1 zero_le_one ((1 - h.1 / P.C) / P.B)) (P.β / 2)
  rw [← hcost]
  apply le_iSup_of_le S
  apply le_iSup_of_le (CommonWorld P h)
  simp

set_option maxHeartbeats 800000 in
-- The complete table law, identity and infinite-cost telescope is elaborated together.
/-- Arbitrary real-probability tables have the exact native finite-leaf law.
Their identity face preserves the actual first source answer, and complete
finite-return TV accuracy forces the logarithmic total-call cost bound. -/
theorem real_policy_factory_logarithmic_total_call_cost (P : FactoryParameters) (m : ℕ)
    (hm : P.β / 2 < (m : ℝ)) :
    ∃ k : ℝ, 0 < k ∧ ∃ δ₀ : ℝ, δ₀ ∈ Ioo 0 1 ∧
      (∀ (w : World P) (S : Bool),
        (∀ cell : Bool × Bool, (1 / 32 : ℝ) ≤ Target P w S cell) ∧
          (∑ cell : Bool × Bool, Target P w S cell) = 1) ∧
      ∀ table : (Bool × History) → PMF Action,
      (∀ (S : Bool) (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ) (a : Action),
        (RawLaw (RowLaw table)) ((TraceEvent TablePolicy S p q t n) ∩
          {ω | Act TablePolicy S p q n ω = a}) =
          ((∏ i ∈ Finset.range n, table (S, Prefix t i) (.inl (t i).1)) *
            table (S, Prefix t n) a) *
          ∏ i ∈ Finset.range n,
            (bernoulliMeasure true false (if (t i).1 then q else p)) {(t i).2}) ∧
      (∀ (S : Bool) (p q : unitInterval) (t : ℕ → Bool × Bool)
        (n : ℕ) (source b : Bool) (D : Set ((Bool × History) → Action)), MeasurableSet D →
        (RawLaw (RowLaw table)) ((((TraceEvent TablePolicy S p q t n) ∩
          {ω | Act TablePolicy S p q n ω = .inl source}) ∩ Prod.fst ⁻¹' D) ∩
            {ω | Read p q source n ω.2 = b}) =
          (RawLaw (RowLaw table)) (((TraceEvent TablePolicy S p q t n) ∩
            {ω | Act TablePolicy S p q n ω = .inl source}) ∩ Prod.fst ⁻¹' D) *
            (bernoulliMeasure true false (if source then q else p)) {b}) ∧
      (∀ (S : Bool) (w : World P) (t : ℕ → Bool × Bool) (n : ℕ)
        (D : Set ((Bool × History) → Action)), MeasurableSet D →
        (RawLaw (RowLaw table)) ((TraceEvent TablePolicy S
          (Rate P w false) (Rate P w true) t n) ∩ Prod.fst ⁻¹' D) /
          (RawLaw (RowLaw table)) (TraceEvent TablePolicy S
            (Rate P w false) (Rate P w true) t n) =
            (RowLaw table) ((SeedSection TablePolicy S t n) ∩ D) /
              (RowLaw table) (SeedSection TablePolicy S t n)) ∧
      (∀ (S : Bool) (p q : unitInterval) (ω) (n : ℕ),
        (n : WithTop ℕ) ≤ Calls TablePolicy S p q ω →
        ((acquiredHistory TablePolicy S (Read p q) n ω).filter (fun v => v.1)).length +
          ((acquiredHistory TablePolicy S (Read p q) n ω).filter (fun v => !v.1)).length = n) ∧
      (∀ (S : Bool) (p q : unitInterval) (t : ℕ → Bool × Bool) (n : ℕ)
        (cell : Bool × Bool) (ω), ω ∈ TraceEvent TablePolicy S p q t n →
        Act TablePolicy S p q n ω = .inr cell →
          Calls TablePolicy S p q ω = (n : WithTop ℕ)) ∧
      (IdentityRows table → ∀ᵐ seed ∂(RowLaw table),
        ∀ (S : Bool) (p q : unitInterval) (tape : ℕ → ℝ),
          Act TablePolicy S p q 0 (seed, tape) = .inl S ∧
          ∀ n (cell : Bool × Bool), Act TablePolicy S p q n (seed, tape) = .inr cell →
            cell.1 = Read p q S 0 tape) ∧
      ∀ δ : ℝ, δ ∈ Ioo 0 δ₀ →
      (∀ (w : World P) (S : Bool), ∀ᵐ ω ∂(RawLaw (RowLaw table)),
        Calls TablePolicy S (Rate P w false) (Rate P w true) ω ≠ ⊤) →
      (∀ (w : World P) (S : Bool), D5.S3.TotalVariation.Pinsker.totalVariation
        (fun cell : Bool × Bool => (RawLaw (RowLaw table)).real {ω | ∃ n : ℕ,
          Calls TablePolicy S (Rate P w false) (Rate P w true) ω = (n : WithTop ℕ) ∧
          Act TablePolicy S (Rate P w false) (Rate P w true) n ω = .inr cell})
        (Target P w S) ≤ δ) →
      ENNReal.ofReal (k * Real.log δ⁻¹) ≤
        ⨆ S : Bool, ⨆ w : World P,
          ∫⁻ ω, (if Calls TablePolicy S (Rate P w false) (Rate P w true) ω = ⊤ then ⊤ else
            ENNReal.ofReal (((Calls TablePolicy S (Rate P w false) (Rate P w true) ω).untopD 0
              : ℕ) ^ (P.β / 2) : ℝ))
            ∂(RawLaw (RowLaw table)) := by
  obtain ⟨k, hk, δ₀, hδ₀, hbound⟩ := native_factory_logarithmic_total_call_cost
    (Seed := (Bool × History) → Action) P m hm
  refine ⟨k, hk, δ₀, hδ₀, factory_target_probability P, ?_⟩
  intro table
  refine ⟨native_policy_table_leaf_law table, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    exact native_source_conditional_kernel TablePolicy
      (fun S h => measurable_pi_apply (S, h)) S (RowLaw table)
  · intro S w t n D hD
    exact private_seed_posterior TablePolicy
      (fun S h => measurable_pi_apply (S, h)) S (RowLaw table)
      (Rate P w false) (Rate P w true) t n D hD (legal_source_word_ne_zero P w t n)
  · intro S p q ω n hn
    have he := List.length_eq_length_filter_add
      (l := acquiredHistory TablePolicy S (Read p q) n ω) (fun v => v.1)
    rw [acquired_history_length_before_return TablePolicy S (Read p q) ω n hn] at he
    exact he.symm
  · exact trace_return_call_count TablePolicy
  · exact fun hi => native_policy_table_identity table hi
  intro δ hδ hfinite htv
  simp_rw [← raw_cost_eq_total_calls TablePolicy]
  apply hbound (RowLaw table) inferInstance TablePolicy
    (fun S h => measurable_pi_apply (S, h)) δ hδ
  intro w S
  have he : (fun cell : Bool × Bool => (RawLaw (RowLaw table)).real {ω | ∃ n : ℕ,
      Calls TablePolicy S (Rate P w false) (Rate P w true) ω = (n : WithTop ℕ) ∧
      Act TablePolicy S (Rate P w false) (Rate P w true) n ω = .inr cell}) =
      (fun cell : Bool × Bool => (RawLaw (RowLaw table)).real
        ((stoppedValue (CellAt TablePolicy S (Rate P w false) (Rate P w true))
          (Calls TablePolicy S (Rate P w false) (Rate P w true))) ⁻¹' {cell})) := by
    funext cell
    exact finite_return_cell_law TablePolicy S (RowLaw table)
      (Rate P w false) (Rate P w true) (hfinite w S) cell
  have ht := htv w S
  rwa [he] at ht



end D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryCriticalMoment
