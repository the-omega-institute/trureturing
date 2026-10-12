/- GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryCriticalMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fresh uniform source innovations and the common-rate factory subfamily. -/

import D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliFactoryExecution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

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
local notation "RawLaw" => fun ν : Measure Seed =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => Uniform))
local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p))
local notation "Coin" => fun (p : unitInterval) (u : ℝ) => decide (u ≤ (p : ℝ))
local notation "Read" => fun (p q : unitInterval) (source : Bool) (n : ℕ) (tape : ℕ → ℝ) =>
  Coin (if source then q else p) (tape n)
local notation "Returns" => Set.range (fun cell : Bool × Bool => (.inr cell : Action))
local notation "Act" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (n : ℕ) (ω : Seed × (ℕ → ℝ)) =>
  π ω.1 S (acquiredHistory π S (Read p q) n ω)
local notation "Calls" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) => hittingAfter (Act π S p q) Returns 0
local notation "CellAt" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (n : ℕ) (ω : Seed × (ℕ → ℝ)) =>
  match Act π S p q n ω with
  | .inr cell => cell
  | _ => (false, false)
local notation "RawCost" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (p q : unitInterval) (a : ℝ) (ω : Seed × (ℕ → ℝ)) =>
  if Calls π S p q ω = ⊤ then (⊤ : ℝ≥0∞) else
    ENNReal.ofReal (((acquiredHistory π S (Read p q)
      ((Calls π S p q ω).untopD 0) ω).length : ℝ) ^ a)
local notation "Bits" => fun (p : unitInterval) (ω : Seed × (ℕ → ℝ)) =>
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
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not,
        Set.mem_Icc, Set.mem_Ioc, not_le]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, ⟨p.2.1.trans h.1.le, h.2⟩⟩
    rw [he, Real.volume_Ioc]
    simp [bernoulliMeasure_apply, unitInterval.toNNReal, ENNReal.ofReal,
      Real.toNNReal_of_nonneg p.2.1, Real.toNNReal_of_nonneg (sub_nonneg.mpr p.2.2)]
    rfl
  · have he : (Coin p) ⁻¹' {true} ∩ Icc (0 : ℝ) 1 = Icc 0 (p : ℝ) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
        Set.mem_Icc]
      constructor
      · exact fun h => ⟨h.2.1, h.1⟩
      · exact fun h => ⟨h.2, ⟨h.1, h.2.trans p.2.2⟩⟩
    rw [he, Real.volume_Icc]
    simp [bernoulliMeasure_apply, unitInterval.toNNReal, ENNReal.ofReal,
      Real.toNNReal_of_nonneg p.2.1, Real.toNNReal_of_nonneg (sub_nonneg.mpr p.2.2)]
    rfl

private lemma seeded_uniform_coin_law (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : unitInterval) : (RawLaw ν).map (Bits p) = Law ν p := by
  have := uniform_probability
  have hm : Measurable (fun tape : ℕ → ℝ => fun n : ℕ => Coin p (tape n)) :=
    measurable_pi_lambda _ (fun n => (coin_measurable p).comp (measurable_pi_apply n))
  have hprod := Measure.map_prod_map ν (Measure.infinitePi (fun _ : ℕ => Uniform))
    measurable_id hm
  rw [Measure.map_id, Measure.infinitePi_map_pi (fun _ : ℕ => Uniform) (fun _ => coin_measurable p)] at hprod
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

local notation "FlatAct" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  π ω.1 S (acquiredHistory π S (fun _ i tape => tape i) n ω)
local notation "FlatCalls" => fun (π : Seed → Bool → History → Action) (S : Bool) =>
  hittingAfter (FlatAct π S) Returns 0
local notation "FlatCellAt" => fun (π : Seed → Bool → History → Action) (S : Bool)
  (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  match FlatAct π S n ω with | .inr cell => cell | _ => (false, false)
local notation "FlatCost" => fun (π : Seed → Bool → History → Action) (S : Bool)
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
  have hm : Measurable (Bits p) := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun n => (coin_measurable p).comp
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
  have hm : Measurable (Bits p) := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun n => (coin_measurable p).comp
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

private lemma coefficient_lower_le_one (P : FactoryParameters) :
    Real.exp (-P.κ) ^ 2 + P.g ≤ 1 := by
  have he : Real.exp (-P.κ) < 1 := Real.exp_lt_one_iff.mpr (by linarith [P.κ_bounds.1])
  linarith [P.g_bounds.2]

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
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one, if_true, Bool.false_eq_true, ite_self,
      ↓reduceIte] at ht
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
      apply congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one) ?_)
      have hC : 0 < P.C := lt_of_lt_of_le (by norm_num) P.C_bounds.1
      have hr0 : 0 ≤ h / P.C := div_nonneg hh.1.le hC.le
      have hr1 : h / P.C ≤ 1 / 4 := (div_le_self hh.1.le P.C_bounds.1).trans hh.2
      have hB : 1 ≤ P.B := by
        rcases P.allowed_B with hB | hB <;> rw [hB] <;> norm_num
      have hBp : 0 < P.B := lt_of_lt_of_le (by norm_num) hB
      exact ⟨div_nonneg (by linarith) hBp.le,
        (div_le_one hBp).mpr (by linarith)⟩
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

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryCriticalMoment
