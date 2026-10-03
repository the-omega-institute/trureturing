/- GID: D5/S3/Observer/ProbabilisticClosure/SingleDeflectionOptimalController
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/SingleDeflectionOptimalController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An internally updated single-deflection controller attains the true stopping minimum. -/

import D5.S3.Observer.ProbabilisticClosure.BeneficialMarkerDeflection
import D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
import Mathlib.Data.Bool.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.SingleDeflectionOptimalController

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
open D5.S3.Observer.ProbabilisticClosure.BeneficialMarkerDeflection
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass

open D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
  (machineEncode machineUpdate machineReadout delayed_pulse_memory_gap)

/-- A marker controller stores only its finite memory between replies. -/
structure MarkerController where
  Memory : Type
  finite : Fintype Memory
  initial : Memory
  update : Memory → Bool → Memory
  action : Memory → Option Side

/-- The counter's silent terminal state continues left; none halts on a marker. -/
def finiteController (N : ℕ) : MarkerController where
  Memory := Option (Fin (2 * N - 1 + 2))
  finite := inferInstance
  initial := some (machineEncode (2 * N - 1) 0)
  update := fun state reply =>
    match state with
    | none => none
    | some q => if reply then none else some (machineUpdate (2 * N - 1) q)
  action := fun state => state.map (fun q => decide (q.val = 2 * N - 1))

/-- The infinite-threshold branch needs one active state and the marker sink. -/
def leftController : MarkerController where
  Memory := Option Unit
  finite := inferInstance
  initial := some ()
  update := fun state reply => if reply then none else state
  action := fun state => state.map (fun _ => false)

/-- The fixed prior's threshold selects a finite machine; it is not a synthesis algorithm. -/
def controller (N : WithTop ℕ) : MarkerController :=
  WithTop.recTopCoe leftController finiteController N

/-- Histories are newest first, so replies must be folded in reverse order. -/
def controllerPolicy {Seed : Type*} [MeasurableSpace Seed]
    (C : MarkerController) : Policy Seed where
  choose := fun _ _ replies => (C.action (replies.reverse.foldl C.update C.initial)).getD false
  measurable_section := fun _ _ => measurable_const

/-- The environment supplies the next fresh-arm reply; the controller uses only memory. -/
def controlledRun (C : MarkerController) (source : Source) : ℕ → C.Memory × State
  | 0 => (C.initial, ⟨[], [], false⟩)
  | n + 1 =>
    let previous := controlledRun C source n
    match C.action previous.1 with
    | none => previous
    | some side =>
      let reply := markerResponse source side (sideCount previous.2.actions side)
      (C.update previous.1 reply,
        ⟨side :: previous.2.actions, reply :: previous.2.replies, reply⟩)

/-- The reference schedule uses one-based query indices. -/
def plannedSide (N : WithTop ℕ) (n : ℕ) : Side :=
  WithTop.recTopCoe false (fun k => decide (n + 1 = 2 * k)) N

universe u
set_option maxHeartbeats 2400000 in
-- Arbitrary-depth execution and probability-cost elaboration share one proof.
/-- Every fixed finite-mean prior admits the internally maintained single-deflection minimum. -/
theorem single_deflection_optimal_controller (alpha : unitInterval)
    (ha : 0 < (alpha : ℝ) ∧ (alpha : ℝ) < 1)
    (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hQ : ∀ᵐ (q : unitInterval) ∂μ, 0 < (q : ℝ) ∧ (q : ℝ) < 1)
    (hI : reciprocalMoment μ ≠ ⊤) :
    let N := firstNegative alpha μ
    let C := controller N
    (N = ⊤ ↔ ∀ m, 1 ≤ m → 0 ≤ coefficient alpha μ m) ∧
    (∀ k : ℕ, N = (k : WithTop ℕ) → 1 ≤ k ∧
      (∀ m, 1 ≤ m → (coefficient alpha μ m < 0 ↔ k ≤ m)) ∧
      @Fintype.card C.Memory C.finite = 2 * k + 2) ∧
    (N = ⊤ → @Fintype.card C.Memory C.finite = 2) ∧
    (∀ state reply, C.action state = none → C.update state reply = state) ∧
    (∀ state, C.action (C.update state true) = none) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) (source : Source) n,
      (controlledRun C source n).2 = actualRun (controllerPolicy C) seed source n ∧
      (controlledRun C source n).1 =
        (actualRun (controllerPolicy C) seed source n).replies.reverse.foldl C.update C.initial ∧
      (C.action (controlledRun C source n).1 =
        if (actualRun (controllerPolicy C) seed source n).stopped then none
        else some (plannedSide N n)) ∧
      (C.action (controlledRun C source n).1 = none →
        controlledRun C source (n + 1) = controlledRun C source n)) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) m, 1 ≤ m →
      (sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) false,
        sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) true) =
        if N ≤ (m : WithTop ℕ) then (2 * m - 1, 1) else (2 * m, 0)) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν],
      (∀ m, 1 ≤ m → lambda (controllerPolicy C) ν m =
        if N ≤ (m : WithTop ℕ) then 1 else 0) ∧
      expectedCost (controllerPolicy C) ν alpha μ ≠ ⊤ ∧
      (expectedCost (controllerPolicy C) ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) +
        ∑' n : ℕ, min 0 (coefficient alpha μ (n + 1)) ∧
      (∀ {Other : Type u} [MeasurableSpace Other] (policy : Policy Other)
        (ρ : Measure Other) [IsProbabilityMeasure ρ],
        expectedCost (controllerPolicy C) ν alpha μ ≤ expectedCost policy ρ alpha μ)) := by
  classical
  let N := firstNegative alpha μ
  let C := controller N
  have hpoly (f : unitInterval → ℝ) (hf : Continuous f) : Integrable f μ := by
    simpa using hf.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  have hsuccessor (m : ℕ) (hm : 1 ≤ m) :
      (alpha : ℝ) * coefficient alpha μ m -
        (1 - (alpha : ℝ)) * coefficient alpha μ (m + 1) ≥ 0 := by
    let f : unitInterval → ℝ := fun q =>
      (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ (m - 1)
    let g : unitInterval → ℝ := fun q =>
      (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ m
    have hf : Integrable f μ := hpoly f (by fun_prop)
    have hg : Integrable g μ := hpoly g (by fun_prop)
    have he : (fun q => (alpha : ℝ) * f q - (1 - (alpha : ℝ)) * g q) =
        (fun q : unitInterval => (1 - (q : ℝ)) * (q : ℝ) ^ (m - 1) *
          ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) ^ 2) := by
      funext q
      dsimp [f, g]
      have hp : (q : ℝ) ^ m = (q : ℝ) ^ (m - 1) * (q : ℝ) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [pow_succ]
      rw [hp]
      ring
    have hnonneg : 0 ≤ ∫ q, (alpha : ℝ) * f q - (1 - (alpha : ℝ)) * g q ∂μ := by
      rw [he]
      exact integral_nonneg (fun q => mul_nonneg
        (mul_nonneg (unitInterval.one_minus_nonneg q) (pow_nonneg (unitInterval.nonneg q) _))
        (sq_nonneg _))
    rw [integral_sub (hf.const_mul _) (hg.const_mul _), integral_const_mul,
      integral_const_mul] at hnonneg
    simpa [f, g, coefficient] using hnonneg
  have htail (m k : ℕ) (hm : 1 ≤ m) (hv : coefficient alpha μ m < 0) (hmk : m ≤ k) :
      coefficient alpha μ k < 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    clear hmk
    induction j with
    | zero => simpa using hv
    | succ j ih =>
      have hs := hsuccessor (m + j) (by omega)
      have ha0 : 0 < 1 - (alpha : ℝ) := sub_pos.mpr ha.2
      have hb : (alpha : ℝ) * coefficient alpha μ (m + j) < 0 := mul_neg_of_pos_of_neg ha.1 ih
      have hn : (1 - (alpha : ℝ)) * coefficient alpha μ (m + j + 1) < 0 := by linarith
      have hvnext : coefficient alpha μ (m + j + 1) < 0 := by
        by_contra h
        have := mul_nonneg ha0.le (le_of_not_gt h)
        linarith
      simpa [Nat.add_assoc] using hvnext
  have hthreshold :
      (N = ⊤ ↔ ∀ m, 1 ≤ m → 0 ≤ coefficient alpha μ m) ∧
      (∀ k : ℕ, N = (k : WithTop ℕ) → 1 ≤ k ∧
        ∀ m, 1 ≤ m → (coefficient alpha μ m < 0 ↔ k ≤ m)) := by
    by_cases hex : ∃ m, 1 ≤ m ∧ coefficient alpha μ m < 0
    · let k := Nat.find hex
      have hk := Nat.find_spec hex
      have hleast (m : ℕ) (hm : 1 ≤ m ∧ coefficient alpha μ m < 0) : k ≤ m :=
        Nat.find_min' hex hm
      have he : N = (k : WithTop ℕ) := by
        apply le_antisymm
        · exact sInf_le ⟨k, hk, rfl⟩
        · apply le_sInf
          rintro _ ⟨m, hm, rfl⟩
          change (k : WithTop ℕ) ≤ (m : WithTop ℕ)
          exact WithTop.coe_le_coe.mpr (hleast m hm)
      refine ⟨?_, ?_⟩
      · constructor
        · intro hn
          rw [he] at hn
          simp at hn
        · intro h
          exact False.elim ((not_lt_of_ge (h k hk.1)) hk.2)
      · intro j hj
        have hjk : j = k := by exact_mod_cast (hj.symm.trans he)
        subst j
        refine ⟨hk.1, ?_⟩
        intro m hm
        exact ⟨fun hv => hleast m ⟨hm, hv⟩, fun hkm => htail k m hk.1 hk.2 hkm⟩
    · have hnonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ coefficient alpha μ m := by
        by_contra h
        exact hex ⟨m, hm, lt_of_not_ge h⟩
      have he : N = ⊤ := by
        change sInf ((fun m : ℕ => (m : WithTop ℕ)) ''
          {m | 1 ≤ m ∧ coefficient alpha μ m < 0}) = ⊤
        have hs : {m | 1 ≤ m ∧ coefficient alpha μ m < 0} = ∅ := by
          ext m
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => hex ⟨m, h⟩
        simp [hs]
      exact ⟨⟨fun _ => hnonneg, fun _ => he⟩, fun k hk => by simp [he] at hk⟩
  have hpositive (k : ℕ) (hk : N = (k : WithTop ℕ)) : 1 ≤ k := (hthreshold.2 k hk).1
  have hproperties (T : WithTop ℕ) :
      (controller T).action (controller T).initial ≠ none ∧
      (∀ state reply, (controller T).action state = none →
        (controller T).update state reply = state) ∧
      (∀ state, (controller T).action ((controller T).update state true) = none) ∧
      (∀ state, (controller T).action state ≠ none →
        (controller T).action ((controller T).update state false) ≠ none) := by
    induction T using WithTop.recTopCoe with
    | top =>
      simp only [controller, WithTop.recTopCoe_top]
      constructor
      · simp [leftController]
      constructor
      · intro state reply hs
        cases state <;> cases reply <;> simp_all [leftController]
      constructor
      · intro state
        simp [leftController]
      · intro state hs
        simpa [leftController] using hs
    | coe k =>
      simp only [controller, WithTop.recTopCoe_coe]
      constructor
      · simp [finiteController]
      constructor
      · intro state reply hs
        cases state <;> cases reply <;> simp_all [finiteController]
      constructor
      · intro state
        cases state <;> simp [finiteController]
      · intro state hs
        cases state <;> simp_all [finiteController]
  have hprops := hproperties N
  have hrun {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) (source : Source) :
      ∀ n,
      (controlledRun C source n).2 = actualRun (controllerPolicy C) seed source n ∧
      (controlledRun C source n).1 =
        (actualRun (controllerPolicy C) seed source n).replies.reverse.foldl C.update C.initial ∧
      (C.action (controlledRun C source n).1 = none ↔
        (actualRun (controllerPolicy C) seed source n).stopped = true) := by
    intro n
    induction n with
    | zero =>
      refine ⟨rfl, rfl, ?_⟩
      simp only [controlledRun, actualRun, Bool.false_eq_true, iff_false]
      exact hprops.1
    | succ n ih =>
      by_cases hs : (actualRun (controllerPolicy C) seed source n).stopped = true
      · have hnone := ih.2.2.mpr hs
        simpa [controlledRun, hnone, actualRun, hs] using ih
      · have hfalse : (actualRun (controllerPolicy C) seed source n).stopped = false :=
          Bool.eq_false_iff.mpr hs
        have hsome : C.action (controlledRun C source n).1 ≠ none :=
          fun h => hs (ih.2.2.mp h)
        obtain ⟨side, hside⟩ := Option.ne_none_iff_exists'.mp hsome
        have hchoose : (controllerPolicy C).choose seed
            (actualRun (controllerPolicy C) seed source n).actions
            (actualRun (controllerPolicy C) seed source n).replies = side := by
          change (C.action ((actualRun (controllerPolicy C) seed source n).replies.reverse.foldl
            C.update C.initial)).getD false = side
          rw [← ih.2.1, hside]
          rfl
        simp only [controlledRun, hside, actualRun, hfalse, Bool.false_eq_true, ↓reduceIte,
          hchoose, ih.1]
        refine ⟨trivial, ?_, ?_⟩
        · simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [← ih.2.1]
        · cases hr : markerResponse source side
              (sideCount (actualRun (controllerPolicy C) seed source n).actions side) with
          | false =>
            simp only [Bool.false_eq_true, iff_false]
            exact hprops.2.2.2 _ hsome
          | true =>
            simp only [iff_true]
            exact hprops.2.2.1 _
  have hfold (T : WithTop ℕ) (hT : ∀ k : ℕ, T = (k : WithTop ℕ) → 1 ≤ k) : ∀ n,
      (controller T).action
        ((List.replicate n false).reverse.foldl (controller T).update (controller T).initial) =
        some (plannedSide T n) := by
    induction T using WithTop.recTopCoe with
    | top =>
      intro n
      have h : (List.replicate n false).reverse.foldl leftController.update leftController.initial =
          some () := by
        induction n with
        | zero => rfl
        | succ n ih => simpa [List.replicate_succ, List.reverse_cons, List.foldl_append,
            leftController] using ih
      change leftController.action ((List.replicate n false).reverse.foldl
        leftController.update leftController.initial) = some false
      rw [h]
      rfl
    | coe k =>
      intro n
      have h : (List.replicate n false).reverse.foldl (finiteController k).update
          (finiteController k).initial = some ((machineUpdate (2 * k - 1))^[n]
            (machineEncode (2 * k - 1) 0)) := by
        induction n with
        | zero => rfl
        | succ n ih =>
          simp only [List.replicate_succ, List.reverse_cons, List.foldl_append,
            List.foldl_cons, List.foldl_nil]
          rw [ih, Function.iterate_succ_apply']
          rfl
      have hc := (delayed_pulse_memory_gap (2 * k - 1) 0 0 (by norm_num) (by norm_num)).2.1 0 n
      have he : machineReadout (2 * k - 1)
          ((machineUpdate (2 * k - 1))^[n] (machineEncode (2 * k - 1) 0)) =
            D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.pulse (2 * k - 1) n := by
        have := abs_nonpos_iff.mp hc
        simpa using sub_eq_zero.mp this
      have hread : ∀ q : Fin (2 * k - 1 + 2),
          decide (q.val = 2 * k - 1) = decide (machineReadout (2 * k - 1) q = 1) := by
        intro q
        simp [machineReadout, D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.pulse]
      change (finiteController k).action ((List.replicate n false).reverse.foldl
        (finiteController k).update (finiteController k).initial) = some (decide (n + 1 = 2 * k))
      rw [h]
      change some (decide (((machineUpdate (2 * k - 1))^[n]
        (machineEncode (2 * k - 1) 0)).val = 2 * k - 1)) = _
      rw [hread, he]
      have hk := hT k rfl
      have hkn : n = 2 * k - 1 ↔ n + 1 = 2 * k := by omega
      simp [D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap.pulse, hkn]
  have hschedule {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) (source : Source) (n : ℕ) :
      C.action (controlledRun C source n).1 =
        if (actualRun (controllerPolicy C) seed source n).stopped then none
        else some (plannedSide N n) := by
    cases hs : (actualRun (controllerPolicy C) seed source n).stopped with
    | true => simpa [hs] using (hrun seed source n).2.2.mpr hs
    | false =>
      have hr := ((stopped_execution_replay_bridge (controllerPolicy C) seed source n).2.2.1 hs).2.1
      rw [(hrun seed source n).2.1, hr]
      simpa [hs] using hfold N hpositive n
  let source₀ : Source := (true, (fun _ => true, fun _ => true))
  have hresponse (side : Side) (j : ℕ) : markerResponse source₀ side j = false := by
    cases side <;> cases j <;> simp [markerResponse, endpoint, arm, source₀]
  have hnever : ∀ n, (controlledRun C source₀ n).2.stopped = false := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      cases ho : C.action (controlledRun C source₀ n).1 with
      | none => simpa [controlledRun, ho] using ih
      | some side => simp [controlledRun, ho, hresponse]
  have htrace {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) (n : ℕ) :
      (controlledRun C source₀ n).2.actions = zeroReplay (controllerPolicy C) seed n := by
    have hf : (actualRun (controllerPolicy C) seed source₀ n).stopped = false := by
      rw [← (hrun seed source₀ n).1]
      exact hnever n
    exact (congrArg State.actions (hrun seed source₀ n).1).trans
      ((stopped_execution_replay_bridge (controllerPolicy C) seed source₀ n).2.2.1 hf).1
  have hcounts {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) : ∀ n,
      (controlledRun C source₀ n).2.actions.length = n ∧
      sideCount (controlledRun C source₀ n).2.actions true =
        if ∃ k : ℕ, N = (k : WithTop ℕ) ∧ 2 * k ≤ n then 1 else 0 := by
    intro n
    induction n with
    | zero =>
      have hn : ¬ ∃ k : ℕ, N = (k : WithTop ℕ) ∧ 2 * k ≤ 0 := by
        rintro ⟨k, hk, hkn⟩
        have := hpositive k hk
        omega
      simp only [controlledRun, sideCount, List.count_nil, List.length_nil, if_neg hn,
        and_self]
    | succ n ih =>
      have hs : (actualRun (controllerPolicy C) seed source₀ n).stopped = false := by
        rw [← (hrun seed source₀ n).1]
        exact hnever n
      have ho : C.action (controlledRun C source₀ n).1 = some (plannedSide N n) := by
        simpa [hs] using hschedule seed source₀ n
      simp only [controlledRun, ho, hresponse, List.length_cons, sideCount, List.count_cons]
      refine ⟨by omega, ?_⟩
      simp only [beq_iff_eq]
      change sideCount (controlledRun C source₀ n).2.actions true +
        (if plannedSide N n = true then 1 else 0) = _
      rw [ih.2]
      by_cases hex : ∃ k : ℕ, N = (k : WithTop ℕ)
      · obtain ⟨k, hk⟩ := hex
        have hsingle (t : ℕ) :
            (∃ j : ℕ, N = (j : WithTop ℕ) ∧ 2 * j ≤ t) ↔ 2 * k ≤ t := by
          constructor
          · rintro ⟨j, hj, hbound⟩
            have hkj : k = j := WithTop.coe_injective (hk.symm.trans hj)
            simpa [hkj] using hbound
          · intro h
            exact ⟨k, hk, h⟩
        have hside : plannedSide N n = decide (n + 1 = 2 * k) := by
          rw [hk]
          rfl
        rw [hsingle n, hsingle (n + 1), hside]
        simp only [decide_eq_true_eq]
        split_ifs <;> omega
      · have hnone (t : ℕ) : ¬ ∃ j : ℕ, N = (j : WithTop ℕ) ∧ 2 * j ≤ t := by
          rintro ⟨j, hj, _⟩
          exact hex ⟨j, hj⟩
        have htop : N = ⊤ := by
          cases hN : N using WithTop.recTopCoe with
          | top => rfl
          | coe k => exact False.elim (hex ⟨k, hN⟩)
        rw [if_neg (hnone n), if_neg (hnone (n + 1))]
        rw [htop]
        simp [plannedSide]
  have hreplay {Seed : Type u} [MeasurableSpace Seed] (seed : Seed) (m : ℕ) (hm : 1 ≤ m) :
      (sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) false,
        sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) true) =
        if N ≤ (m : WithTop ℕ) then (2 * m - 1, 1) else (2 * m, 0) := by
    rw [← htrace seed (2 * m)]
    have hc := hcounts seed (2 * m)
    have ht := List.count_false_add_count_true (controlledRun C source₀ (2 * m)).2.actions
    change sideCount (controlledRun C source₀ (2 * m)).2.actions false +
      sideCount (controlledRun C source₀ (2 * m)).2.actions true = _ at ht
    have he (T : WithTop ℕ) :
        (∃ k : ℕ, T = (k : WithTop ℕ) ∧ 2 * k ≤ 2 * m) ↔ T ≤ (m : WithTop ℕ) := by
      induction T using WithTop.recTopCoe with
      | top => simp
      | coe k =>
        constructor
        · rintro ⟨j, hj, hbound⟩
          have hkj : k = j := WithTop.coe_injective hj
          exact (WithTop.coe_le_coe (α := ℕ) (a := m) (b := k)).mpr (by omega)
        · intro h
          have hkm : k ≤ m := (WithTop.coe_le_coe (α := ℕ) (a := m) (b := k)).mp h
          exact ⟨k, rfl, by omega⟩
    rw [he N] at hc
    split_ifs with h <;> simp only [h, ↓reduceIte] at hc <;>
      apply Prod.ext <;> dsimp <;> omega
  have hlambda {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed)
      [IsProbabilityMeasure ν] (m : ℕ) (hm : 1 ≤ m) :
      lambda (controllerPolicy C) ν m = if N ≤ (m : WithTop ℕ) then 1 else 0 := by
    have he (seed : Seed) :
        (sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) false % 2 = 1 ∧
          sideCount (zeroReplay (controllerPolicy C) seed (2 * m)) true % 2 = 1) ↔
        N ≤ (m : WithTop ℕ) := by
      have hc := hreplay seed m hm
      by_cases h : N ≤ (m : WithTop ℕ)
      · simp only [h, ↓reduceIte, Prod.mk.injEq] at hc
        rw [hc.1, hc.2]
        simp [h, show (2 * m - 1) % 2 = 1 by omega]
      · simp only [h, ↓reduceIte, Prod.mk.injEq] at hc
        rw [hc.1, hc.2]
        simp [h]
    unfold lambda
    simp only [he]
    by_cases h : N ≤ (m : WithTop ℕ) <;> simp [h]
  have hmin (m : ℕ) (hm : 1 ≤ m) :
      (if N ≤ (m : WithTop ℕ) then (1 : ℝ) else 0) * coefficient alpha μ m =
        min 0 (coefficient alpha μ m) := by
    cases hN : N using WithTop.recTopCoe with
    | top =>
      have hv := hthreshold.1.mp hN m hm
      simp [min_eq_left hv]
    | coe k =>
      have he := (hthreshold.2 k hN).2 m hm
      by_cases h : k ≤ m
      · have hv := he.mpr h
        simp [h, min_eq_right hv.le]
      · have hv : 0 ≤ coefficient alpha μ m := le_of_not_gt (fun hv => h (he.mp hv))
        simp [h, min_eq_left hv]
  have hbase := beneficial_marker_deflection alpha ha μ hQ
  have hcost {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed)
      [IsProbabilityMeasure ν] :
      (∀ m, 1 ≤ m → lambda (controllerPolicy C) ν m =
        if N ≤ (m : WithTop ℕ) then 1 else 0) ∧
      expectedCost (controllerPolicy C) ν alpha μ ≠ ⊤ ∧
      (expectedCost (controllerPolicy C) ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) +
        ∑' n : ℕ, min 0 (coefficient alpha μ (n + 1)) ∧
      (∀ {Other : Type u} [MeasurableSpace Other] (policy : Policy Other)
        (ρ : Measure Other) [IsProbabilityMeasure ρ],
        expectedCost (controllerPolicy C) ν alpha μ ≤ expectedCost policy ρ alpha μ) := by
    have hc := hbase.2.2.1 (controllerPolicy C : Policy Seed) ν
    have hfinite := hc.2.2.1.mpr hI
    have hexp := hc.2.2.2 hI
    have hterm (n : ℕ) : lambda (controllerPolicy C) ν (n + 1) * coefficient alpha μ (n + 1) =
        min 0 (coefficient alpha μ (n + 1)) := by
      rw [hlambda ν (n + 1) (by omega)]
      exact hmin (n + 1) (by omega)
    simp only [hterm] at hexp
    refine ⟨hlambda ν, hfinite, hexp, ?_⟩
    intro Other _ policy ρ _
    have hp := hbase.2.2.1 policy ρ
    have hpfinite := hp.2.2.1.mpr hI
    apply (ENNReal.toReal_le_toReal hfinite hpfinite).mp
    rw [hexp, hp.2.2.2 hI]
    apply add_le_add_right
    have hsmin : Summable (fun n : ℕ => min 0 (coefficient alpha μ (n + 1))) := by
      simpa only [hterm] using hbase.2.1.2.2 (controllerPolicy C : Policy Seed) ν
    have hsp := hbase.2.1.2.2 policy ρ
    apply hsmin.tsum_le_tsum _ hsp
    intro n
    have hb := (adaptive_marker_stopping_tails policy ρ alpha (0 : unitInterval)).2.2 (n + 1)
    by_cases hv : 0 ≤ coefficient alpha μ (n + 1)
    · rw [min_eq_left hv]
      exact mul_nonneg hb.1 hv
    · rw [min_eq_right (le_of_not_ge hv)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (neg_nonneg.mpr (le_of_not_ge hv))]
  refine ⟨hthreshold.1, ?_, ?_, hprops.2.1, hprops.2.2.1, ?_, hreplay, hcost⟩
  · intro k hk
    change N = (k : WithTop ℕ) at hk
    refine ⟨(hthreshold.2 k hk).1, (hthreshold.2 k hk).2, ?_⟩
    change @Fintype.card (controller N).Memory (controller N).finite = 2 * k + 2
    rw [hk]
    change Fintype.card (Option (Fin (2 * k - 1 + 2))) = 2 * k + 2
    rw [Fintype.card_option, Fintype.card_fin]
    have := hpositive k hk
    omega
  · intro hn
    change N = ⊤ at hn
    change @Fintype.card (controller N).Memory (controller N).finite = 2
    rw [hn]
    change Fintype.card (Option Unit) = 2
    decide
  · intro Seed _ seed source n
    refine ⟨(hrun seed source n).1, (hrun seed source n).2.1,
      hschedule seed source n, ?_⟩
    intro hn
    simp [controlledRun, hn]

#print axioms single_deflection_optimal_controller

end D5.S3.Observer.ProbabilisticClosure.SingleDeflectionOptimalController
