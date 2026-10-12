/- GID: D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/SeededBernoulliFactoryExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labelled seeded factory execution and logarithmic total-call cost. -/

import D5.S3.Estimation.SequentialDecisionRisk.BernoulliCommonEndpointCharge
import D5.S3.TotalVariation.Metric
import Mathlib.Probability.Process.HittingTime

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliFactoryExecution
open SeededBernoulliStoppedMoment BernoulliCommonEndpointCharge
variable {Seed : Type*} [MeasurableSpace Seed]

local notation "Action" => (Unit ⊕ Bool) ⊕ (Bool × Bool)
local notation "History" => List (Bool × Bool)
local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p))
local notation "Rate" => fun (p₀ : unitInterval) (C h : ℝ) =>
  Set.projIcc 0 1 zero_le_one ((p₀ : ℝ) + h * (-(p₀ : ℝ) / C))
local notation "Cost" => fun (a : ℝ) (t : WithTop ℕ) =>
  if t = ⊤ then (⊤ : ℝ≥0∞) else ENNReal.ofReal (((t.untopD 0 : ℕ) : ℝ) ^ a)

/-- A policy acts on the complete labelled record and the private seed.
`inl (inl ())` means that no further visible action occurs. Each source action appends
one actually acquired source answer; `.inr` returns the complete output cell. -/
def acquiredHistory (π : Seed → Bool → History → Action) (S : Bool) :
    ℕ → Seed × (ℕ → Bool) → History
  | 0, _ => []
  | n + 1, ω =>
    let h := acquiredHistory π S n ω
    match π ω.1 S h with
    | .inl (.inr source) => h ++ [(source, ω.2 n)]
    | _ => h

local notation "Act" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) => π ω.1 S (acquiredHistory π S n ω)
local notation "Returns" => Set.range (fun cell : Bool × Bool => (.inr cell : Action))
local notation "Calls" => fun (π : Seed → Bool → History → Action) (S : Bool) =>
  hittingAfter (Act π S) Returns 0
local notation "CellAt" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  match Act π S n ω with
  | .inr cell => cell
  | _ => (false, false)

local notation "RecordCost" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (a : ℝ) (ω : Seed × (ℕ → Bool)) =>
  if Calls π S ω = ⊤ then (⊤ : ℝ≥0∞) else
    ENNReal.ofReal (((acquiredHistory π S ((Calls π S ω).untopD 0) ω).length : ℝ) ^ a)

private lemma action_singleton_measurable (a : Action) : MeasurableSet {a} := by
  cases a with
  | inl a =>
    have hi : MeasurableSet ({a} : Set (Unit ⊕ Bool)) := by
      cases a with
      | inl u =>
        simpa only [Set.image_singleton] using
          ((measurableSet_singleton u).inl_image (β := Bool))
      | inr source =>
        simpa only [Set.image_singleton] using
          ((measurableSet_singleton source).inr_image (α := Unit))
    simpa only [Set.image_singleton] using (hi.inl_image (β := Bool × Bool))
  | inr cell =>
    simpa only [Set.image_singleton] using
      ((measurableSet_singleton cell).inr_image (α := Unit ⊕ Bool))

private lemma actions_adapted (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool) :
    Adapted seededFiltration (Act π S) := by
  let : MeasurableSpace History := ⊤
  let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
  have hseed (n : ℕ) : Measurable[seededFiltration n]
      (fun ω : Seed × (ℕ → Bool) => ω.1) :=
    (measurable_fst : Measurable (fun z : Seed × ((k : range n) → Bool) => z.1)).comp
      (comap_measurable (fun ω : Seed × (ℕ → Bool) =>
      (ω.1, (range n).restrict ω.2)))
  have hbit (n : ℕ) : Measurable[seededFiltration (n + 1)]
      (fun ω : Seed × (ℕ → Bool) => ω.2 n) :=
    ((measurable_pi_apply (⟨n, mem_range.mpr (by omega)⟩ : range (n + 1))).comp
      (measurable_snd : Measurable (fun z : Seed × ((k : range (n + 1)) → Bool) => z.2))).comp
      (comap_measurable (fun ω : Seed × (ℕ → Bool) =>
        (ω.1, (range (n + 1)).restrict ω.2)))
  have hpolicy : Measurable (fun z : Seed × History => π z.1 S z.2) :=
    measurable_from_prod_countable_left (hπ S)
  have hhist (n : ℕ) : Measurable[seededFiltration n] (acquiredHistory π S n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have hprev := ih.mono (seededFiltration.mono (Nat.le_succ n)) le_rfl
      have hact := hpolicy.comp ((hseed (n + 1)).prodMk hprev)
      have hupdate : Measurable (fun z : History × Action × Bool =>
          match z.2.1 with
          | .inl (.inr source) => z.1 ++ [(source, z.2.2)]
          | _ => z.1) := Measurable.of_discrete
      exact hupdate.comp (hprev.prodMk (hact.prodMk (hbit n)))
  exact fun n => hpolicy.comp ((hseed n).prodMk (hhist n))

private lemma calls_stopping (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool) :
    IsStoppingTime seededFiltration (Calls π S) :=
  (actions_adapted π hπ S).isStoppingTime_hittingAfter measurableSet_range_inr

private lemma output_stopped_measurable (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool) :
    Measurable[(calls_stopping π hπ S).measurableSpace]
      (stoppedValue (CellAt π S) (Calls π S)) := by
  have hcell : Measurable (fun a : Action =>
      match a with | .inr cell => cell | _ => (false, false)) :=
    measurable_fun_sum measurable_const measurable_id
  have hu : Adapted seededFiltration (CellAt π S) := fun n =>
    hcell.comp (actions_adapted π hπ S n)
  exact measurable_stoppedValue hu.stronglyAdapted.isStronglyProgressive_of_discrete
    (calls_stopping π hπ S)

omit [MeasurableSpace Seed] in
private lemma history_terminal (π : Seed → Bool → History → Action) (S : Bool)
    (ω : Seed × (ℕ → Bool)) (n : ℕ)
    (hterminal : ∀ source : Bool, Act π S n ω ≠ .inl (.inr source)) (k : ℕ) :
    acquiredHistory π S (n + k) ω = acquiredHistory π S n ω := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, acquiredHistory, ih]
    cases ha : Act π S n ω with
    | inl a =>
      cases a with
      | inl u => simp only [ha]
      | inr source => exact False.elim (hterminal source ha)
    | inr cell => simp only [ha]

omit [MeasurableSpace Seed] in
private lemma call_before_return (π : Seed → Bool → History → Action) (S : Bool)
    (ω : Seed × (ℕ → Bool)) (n : ℕ) (hn : (n : WithTop ℕ) < Calls π S ω)
    (hfinite : Calls π S ω ≠ ⊤) : ∃ source : Bool, Act π S n ω = .inl (.inr source) := by
  classical
  by_contra hc
  have hterminal : ∀ source : Bool, Act π S n ω ≠ .inl (.inr source) := by
    simpa only [not_exists] using hc
  have hnot : Act π S n ω ∉ Returns :=
    notMem_of_lt_hittingAfter (u := Act π S) (s := Returns) (n := 0) hn (Nat.zero_le n)
  have hret := hittingAfter_mem_set_of_ne_top (u := Act π S) (s := Returns) (n := 0) hfinite
  have hle : n ≤ (Calls π S ω).untopA := by
    lift Calls π S ω to ℕ using hfinite with r
    simpa using hn.le
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have he : Act π S (Calls π S ω).untopA ω = Act π S n ω := by
    dsimp
    rw [hk, history_terminal π S ω n hterminal k]
  exact hnot (he ▸ hret)

omit [MeasurableSpace Seed] in
/-- At every finite return, the charged number is exactly the length of the
complete record. Both source labels contribute one call per acquired answer. -/
theorem acquired_history_length_at_return (π : Seed → Bool → History → Action)
    (S : Bool) (ω : Seed × (ℕ → Bool)) (n : ℕ) (hn : Calls π S ω = (n : WithTop ℕ)) :
    (acquiredHistory π S n ω).length = n := by
  have hfinite : Calls π S ω ≠ ⊤ := by rw [hn]; exact WithTop.coe_ne_top
  have hlen : ∀ i : ℕ, i ≤ n → (acquiredHistory π S i ω).length = i := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      obtain ⟨source, hs⟩ := call_before_return π S ω i
        (by rw [hn]; exact_mod_cast (by omega : i < n)) hfinite
      change π ω.1 S (acquiredHistory π S i ω) = .inl (.inr source) at hs
      simp only [acquiredHistory, hs, List.length_append, ih (by omega)]
      simp
  exact hlen n le_rfl

omit [MeasurableSpace Seed] in
private lemma cost_eq_record_cost (π : Seed → Bool → History → Action) (S : Bool)
    (a : ℝ) (ω : Seed × (ℕ → Bool)) :
    Cost a (Calls π S ω) = RecordCost π S a ω := by
  cases hM : Calls π S ω with
  | top => simp [hM]
  | coe n =>
    simp only [hM, WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
    rw [acquired_history_length_at_return π S ω n hM]

/-- The four-cell noninteger perturbation is normalized. -/
private lemma target_mass (u h β : ℝ) :
    (∑ cell : Bool × Bool,
      ((if cell.1 then u else 1 - u) / 2 +
        (h ^ β / 16) * (if cell.1 = cell.2 then 1 else -1))) = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte]
  ring

/-- TV accuracy of the complete output supplies the required single-cell
accuracy, through the public event-gap characterization. -/
private lemma tv_output_accuracy (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p : unitInterval)
    (u h β δ : ℝ)
    (htv : D5.S3.TotalVariation.Pinsker.totalVariation
      (fun cell : Bool × Bool => (Law ν p).real
        ((stoppedValue (CellAt π S) (Calls π S)) ⁻¹' {cell}))
      (fun cell : Bool × Bool => (if cell.1 then u else 1 - u) / 2 +
        (h ^ β / 16) * (if cell.1 = cell.2 then 1 else -1)) ≤ δ) :
    |(u / 2 - h ^ β / 16) - (Law ν p).real
      ((stoppedValue (CellAt π S) (Calls π S)) ⁻¹' {(true, false)})| ≤ δ := by
  classical
  have ho := (output_stopped_measurable π hπ S).mono
    (calls_stopping π hπ S).measurableSpace_le le_rfl
  have hm : (∑ cell : Bool × Bool, (Law ν p).real
      ((stoppedValue (CellAt π S) (Calls π S)) ⁻¹' {cell})) = 1 := by
    simpa using sum_measureReal_preimage_singleton (μ := Law ν p)
      (univ : Finset (Bool × Bool)) (fun cell hc => ho (measurableSet_singleton cell))
  have hg := (D5.S3.TotalVariation.Metric.total_variation_eq_sup_event_gap _ _
    (hm.trans (target_mass u h β).symm)).2 ⟨{(true, false)}, rfl⟩
  simpa only [sum_singleton, Bool.true_eq_false, ↓reduceIte, mul_neg, mul_one,
    ← sub_eq_add_neg, abs_sub_comm] using hg.trans htv

set_option maxHeartbeats 600000 in
-- Elaborating the complete policy and extended-cost telescope requires this limit.
/-- Any measurable parameter-independent seeded policy with complete-output TV
accuracy has logarithmic worst-world cost. Its execution can make arbitrarily
many calls, and nonreturn has infinite cost. -/
theorem seeded_policy_logarithmic_total_call_cost
    (B C β : ℝ) (hB : B = 2 ∨ B = 4) (hC : 1 ≤ C)
    (hβ : 0 < β) (hβint : ∀ j : ℕ, β ≠ j) (m : ℕ) (hm : β / 2 < (m : ℝ)) :
    ∃ k : ℝ, 0 < k ∧ ∃ δ₀ : ℝ, δ₀ ∈ Set.Ioo 0 1 ∧
      ∀ (ν : Measure Seed), IsProbabilityMeasure ν →
      ∀ (π : Seed → Bool → History → Action),
      (∀ S h, Measurable (fun seed => π seed S h)) →
      ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      (∀ (S : Bool) (h : ℝ), h ∈ Set.Ioc 0 (1 / 4 : ℝ) →
        D5.S3.TotalVariation.Pinsker.totalVariation
          (fun cell : Bool × Bool => (Law ν (Set.projIcc 0 1 zero_le_one ((1 - h / C) / B))).real
            ((stoppedValue (CellAt π S) (Calls π S)) ⁻¹' {cell}))
          (fun cell : Bool × Bool =>
            (if cell.1 then (1 - h / C) / B else 1 - (1 - h / C) / B) / 2 +
              (h ^ β / 16) * (if cell.1 = cell.2 then 1 else -1)) ≤ δ) →
      ENNReal.ofReal (k * Real.log δ⁻¹) ≤
        ⨆ S : Bool, ⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
          ∫⁻ ω, RecordCost π S (β / 2) ω
            ∂Law ν (Set.projIcc 0 1 zero_le_one ((1 - h.1 / C) / B)) := by
  have hBp : 1 / B ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases hB with rfl | rfl <;> norm_num
  let p₀ : unitInterval := ⟨1 / B, hBp.1.le, hBp.2.le⟩
  obtain ⟨k, hk, δ₀, hδ₀, hbound⟩ :=
    bernoulli_power_target_logarithmic_uniform_cost (Seed := Seed) p₀ hBp.1 hBp.2
      B C β m hβ hβint hm hC
  refine ⟨k, hk, δ₀, hδ₀, ?_⟩
  intro ν hν π hπ δ hδ htv
  have := hν
  have hrate (h : ℝ) : Rate p₀ C h = Set.projIcc 0 1 zero_le_one ((1 - h / C) / B) := by
    apply congrArg (Set.projIcc 0 1 zero_le_one)
    dsimp [p₀]
    ring
  have hs := (output_stopped_measurable π hπ false) (measurableSet_singleton (true, false))
  have ha : ∀ h ∈ Set.Ioc 0 (1 / 4 : ℝ),
      |((1 - h / C) / (2 * B) - h ^ β / 16) -
        (Law ν (Rate p₀ C h)).real
          ((stoppedValue (CellAt π false) (Calls π false)) ⁻¹' {(true, false)})| ≤ δ := by
    intro h hh
    rw [hrate]
    have he : ((1 - h / C) / B) / 2 = (1 - h / C) / (2 * B) := by ring
    simpa only [he] using tv_output_accuracy π hπ false ν _ ((1 - h / C) / B) h β δ
      (htv false h hh)
  have hb := hbound ν hν δ hδ (Calls π false) (calls_stopping π hπ false) _ hs ha
  simp_rw [hrate] at hb
  have hc : (⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
      ∫⁻ ω, Cost (β / 2) (Calls π false ω)
        ∂Law ν (Set.projIcc 0 1 zero_le_one ((1 - h.1 / C) / B))) =
      ⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
        ∫⁻ ω, RecordCost π false (β / 2) ω
          ∂Law ν (Set.projIcc 0 1 zero_le_one ((1 - h.1 / C) / B)) := by
    simp_rw [cost_eq_record_cost]
  rw [hc] at hb
  exact hb.trans (le_iSup (fun S : Bool =>
    ⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
      ∫⁻ ω, RecordCost π S (β / 2) ω
        ∂Law ν (Set.projIcc 0 1 zero_le_one ((1 - h.1 / C) / B))) false)

end D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliFactoryExecution
