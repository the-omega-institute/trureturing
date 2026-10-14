/- GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernsteinScheduledExecution
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NativeBernsteinScheduledExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed source schedules and actual return landmarks for Bernstein batches. -/

import D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinBatchExecution

noncomputable section
open scoped BigOperators ENNReal

namespace D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution
open NativeBernsteinBatchExecution SeededBernoulliFactoryExecution MeasureTheory ProbabilityTheory

def block (D d : ℕ → ℕ) : ℕ → List Bool
  | 0 => List.replicate (D 0) false ++ List.replicate (d 0) true
  | k + 1 => List.replicate (D (k + 1) - D k) false ++
    List.replicate (d (k + 1) - d k) true

def stageWord (D d : ℕ → ℕ) (k : ℕ) : List Bool :=
  (List.range (k + 1)).flatMap (block D d)

private theorem stageWord_succ (D d : ℕ → ℕ) (k : ℕ) :
    stageWord D d (k + 1) = stageWord D d k ++ block D d (k + 1) := by
  simp [stageWord, List.range_succ, List.flatMap_append]

private theorem stageWord_geometry (D d : ℕ → ℕ) (hD : StrictMono D) (hd : StrictMono d) :
    (∀ k, (stageWord D d k).length = D k + d k) ∧
    (∀ k l, k ≤ l → List.IsPrefix (stageWord D d k) (stageWord D d l)) := by
  refine ⟨?_, ?_⟩
  · intro k
    induction k with
    | zero => simp [stageWord, block]
    | succ k ih =>
      rw [stageWord_succ, List.length_append, ih]
      simp only [block, List.length_append, List.length_replicate]
      have hDk : D k ≤ D (k + 1) := hD.monotone (Nat.le_succ k)
      have hdk : d k ≤ d (k + 1) := hd.monotone (Nat.le_succ k)
      omega
  · intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact ⟨[], List.append_nil _⟩
    | succ l _ ih => exact ih.trans ⟨_, (stageWord_succ D d l).symm⟩

/-- Strictly increasing cumulative degrees determine one infinite source
schedule whose every milestone prefix is the prescribed concatenation. -/
theorem construct_fixed_block_schedule (D d : ℕ → ℕ) (hD : StrictMono D) (hd : StrictMono d) :
    ∃ σ : ℕ → Bool, ∀ k,
      List.ofFn (fun r : Fin (D k + d k) => σ r.val) = stageWord D d k := by
  obtain ⟨hlen, hpref⟩ := stageWord_geometry D d hD hd
  have hb (n : ℕ) : n < (stageWord D d (n + 1)).length := by
    rw [hlen]
    have hDn : n + 1 ≤ D (n + 1) := hD.id_le (n + 1)
    omega
  let σ := fun n => (stageWord D d (n + 1))[n]'(hb n)
  refine ⟨σ, fun k => ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro n _ hn
    simp only [List.getElem_ofFn]
    change (stageWord D d (n + 1))[n]'(hb n) = (stageWord D d k)[n]'hn
    by_cases hk : n + 1 ≤ k
    · exact (hpref (n + 1) k hk).getElem (hb n)
    · exact ((hpref k (n + 1) (by omega)).getElem hn).symm

def fixedSchedule (D d : ℕ → ℕ) (hD : StrictMono D) (hd : StrictMono d) : ℕ → Bool :=
  Classical.choose (construct_fixed_block_schedule D d hD hd)


def Legal (σ : ℕ → Bool) (h : History) : Prop :=
  h.map Prod.fst = List.ofFn (fun i : Fin h.length => σ i.val)

def encodeStage (σ : ℕ → Bool) (n : ℕ) : Option Bool → Action
  | none => .inl (σ n)
  | some e => .inr (false, e)

section Table
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)

def batchTable : (Bool × History) → PMF Action := by
  classical
  let σ := fixedSchedule D d hD hd
  exact fun row => if Legal σ row.2 then
    if hk : ∃ k, row.2.length = D k + d k then
      (rowNat D d a hD.monotone hd.monotone hc (Nat.find hk)
        (successCount false row.2) (successCount true row.2)).map (encodeStage σ row.2.length)
    else PMF.pure (.inl (σ row.2.length))
  else PMF.pure (.inl (σ row.2.length))

/-- One rate-independent table only calls the scheduled source and returns
only at a batch landmark, with the first output coordinate fixed to false. -/
theorem batchTable_supported_actions (S : Bool) (h : History) (a' : Action)
    (ha : batchTable D d a hD hd hc (S, h) a' ≠ 0) :
    (∀ s, a' = Sum.inl s → s = fixedSchedule D d hD hd h.length) ∧
    (∀ cell, a' = Sum.inr cell → ∃ k, h.length = D k + d k ∧ cell.1 = false) := by
  classical
  unfold batchTable at ha
  split_ifs at ha with hlegal hk
  · obtain ⟨out, _, hout⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    cases out with
    | none =>
      simp only [encodeStage] at hout
      subst a'
      exact ⟨fun s hs => (Sum.inl.inj hs).symm, fun cell he => by cases he⟩
    | some e =>
      simp only [encodeStage] at hout
      subst a'
      refine ⟨(fun s he => by cases he), fun cell he => ?_⟩
      cases he
      exact ⟨Nat.find hk, Nat.find_spec hk, rfl⟩
  · have he := (PMF.mem_support_pure_iff _ _).mp ha
    subst a'
    exact ⟨fun s hs => (Sum.inl.inj hs).symm, fun cell he => by cases he⟩
  · have he := (PMF.mem_support_pure_iff _ _).mp ha
    subst a'
    exact ⟨fun s hs => (Sum.inl.inj hs).symm, fun cell he => by cases he⟩

end Table


def safePolicy (σ : ℕ → Bool) (table : (Bool × History) → PMF Action)
    (seed : RowSeed) (S : Bool) (h : History) : Action :=
  if table (S, h) (seed (S, h)) = 0 then .inl (σ h.length) else seed (S, h)

/-- The support repair is measurable and changes no execution on a common
full-measure set of private seeds, uniformly in rates and innovation tapes. -/
theorem supported_realization (σ : ℕ → Bool) (table : (Bool × History) → PMF Action) :
    (∀ S h, Measurable (fun seed => safePolicy σ table seed S h)) ∧
    (∀ᵐ seed ∂rowLaw table,
      (∀ S h, safePolicy σ table seed S h = tablePolicy seed S h) ∧
      ∀ (S : Bool) (p q : unitInterval) (tape : Tape),
        (∀ n, nativeHistory (safePolicy σ table) S p q n (seed, tape) =
          nativeHistory tablePolicy S p q n (seed, tape)) ∧
        (∀ n, nativeAction (safePolicy σ table) S p q n (seed, tape) =
          nativeAction tablePolicy S p q n (seed, tape)) ∧
        nativeCalls (safePolicy σ table) S p q (seed, tape) =
          nativeCalls tablePolicy S p q (seed, tape)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro S h
    let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
    exact (Measurable.of_discrete (f := fun x : Action =>
      if table (S, h) x = 0 then Sum.inl (σ h.length) else x)).comp
      (measurable_pi_apply (S, h))
  · filter_upwards [NativeBernoulliFactoryCriticalMoment.table_rows_supported table] with seed hs
    have he (S h) : safePolicy σ table seed S h = tablePolicy seed S h := by
      simp [safePolicy, tablePolicy, hs (S, h)]
    refine ⟨he, fun S p q tape => ?_⟩
    have hh (n) : nativeHistory (safePolicy σ table) S p q n (seed, tape) =
        nativeHistory tablePolicy S p q n (seed, tape) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change acquiredHistory (safePolicy σ table) S (sourceRead p q) (n + 1) (seed, tape) =
          acquiredHistory tablePolicy S (sourceRead p q) (n + 1) (seed, tape)
        change acquiredHistory (safePolicy σ table) S (sourceRead p q) n (seed, tape) =
          acquiredHistory tablePolicy S (sourceRead p q) n (seed, tape) at ih
        simp only [acquiredHistory, ih, he]
    have ha (n) : nativeAction (safePolicy σ table) S p q n (seed, tape) =
        nativeAction tablePolicy S p q n (seed, tape) := by
      simp only [nativeAction, hh, he]
    refine ⟨hh, ha, ?_⟩
    simp only [nativeCalls, hittingAfter, ha]


private theorem stageWord_counts (D d : ℕ → ℕ) (hD : StrictMono D) (hd : StrictMono d)
    (k : ℕ) (source : Bool) :
    (stageWord D d k).count source = if source then d k else D k := by
  induction k with
  | zero => cases source <;> simp [stageWord, block, List.count_replicate]
  | succ k ih =>
    rw [stageWord_succ, List.count_append, ih]
    have hDk : D k ≤ D (k + 1) := hD.monotone (Nat.le_succ k)
    have hdk : d k ≤ d (k + 1) := hd.monotone (Nat.le_succ k)
    cases source <;> simp [block, List.count_replicate] <;> omega

private theorem sourceCount_labels (h : History) (source : Bool) :
    sourceCount source h = (h.map Prod.fst).count source := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  unfold sourceCount
  congr 2

section Landmarks
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)

private theorem safe_supported_actions (seed : RowSeed) (S : Bool) (h : History) :
    (∀ s, π seed S h = Sum.inl s → s = σ h.length) ∧
    (∀ cell, π seed S h = Sum.inr cell → ∃ k, h.length = D k + d k ∧ cell.1 = false) := by
  classical
  unfold safePolicy
  split_ifs with hz
  · exact ⟨fun s hs => (Sum.inl.inj hs).symm, fun cell he => by cases he⟩
  · exact batchTable_supported_actions D d a hD hd hc S h _ hz

/-- Every seed and tape follows the same source schedule. Reached landmarks
have the actual prescribed source counts, and all finite returns are landmarks. -/
theorem actual_schedule_and_return_landmarks (S : Bool) (p q : unitInterval) (ω : RowSeed × Tape) :
    (∀ n, Legal σ (nativeHistory π S p q n ω)) ∧
    ((D 0 + d 0 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
    (∀ k, ((D k + d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω →
      sourceCount false (nativeHistory π S p q (D k + d k) ω) = D k ∧
      sourceCount true (nativeHistory π S p q (D k + d k) ω) = d k) ∧
    (∀ n : ℕ, nativeCalls π S p q ω = (n : WithTop ℕ) → ∃ k, n = D k + d k) := by
  have hlegal (n) : Legal σ (nativeHistory π S p q n ω) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Legal σ (acquiredHistory π S (sourceRead p q) (n + 1) ω)
      rw [acquiredHistory]
      cases ha : π ω.1 S (acquiredHistory π S (sourceRead p q) n ω) with
      | inl source =>
        have hs := (safe_supported_actions D d a hD hd hc ω.1 S
          (acquiredHistory π S (sourceRead p q) n ω)).1 source ha
        change Legal σ (acquiredHistory π S (sourceRead p q) n ω ++
          [(source, sourceRead p q source n ω.2)])
        change (acquiredHistory π S (sourceRead p q) n ω).map Prod.fst = _ at ih
        simp only [Legal, List.map_append, List.map_cons, List.map_nil,
          List.length_append, List.length_singleton, List.ofFn_succ', List.concat_eq_append,
          Fin.val_cast, Fin.val_castSucc, Fin.val_last]
        rw [ih, hs]
        rfl
      | inr cell => exact ih
  have hreturn (n : ℕ) (hn : nativeCalls π S p q ω = (n : WithTop ℕ)) :
      ∃ k, n = D k + d k := by
    have hmem := hittingAfter_mem_set_of_ne_top
      (u := nativeAction π S p q) (s := Set.range (fun c : Bool × Bool => (Sum.inr c : Action)))
      (n := 0) (ω := ω) (show nativeCalls π S p q ω ≠ ⊤ by rw [hn]; simp)
    change nativeAction π S p q (nativeCalls π S p q ω).untopA ω ∈ _ at hmem
    rw [hn] at hmem
    change nativeAction π S p q n ω ∈ _ at hmem
    obtain ⟨cell, hcell⟩ := hmem
    have hlen := acquired_history_length_at_return π S (sourceRead p q) ω n hn
    obtain ⟨k, hk, _⟩ := (safe_supported_actions D d a hD hd hc ω.1 S
      (nativeHistory π S p q n ω)).2 cell hcell.symm
    exact ⟨k, hlen ▸ hk⟩
  refine ⟨hlegal, ?_, ?_, hreturn⟩
  · cases ht : nativeCalls π S p q ω with
    | top => exact le_top
    | coe n =>
      obtain ⟨k, hk⟩ := hreturn n ht
      apply WithTop.coe_le_coe.mpr
      rw [hk]
      exact Nat.add_le_add (hD.monotone (Nat.zero_le k)) (hd.monotone (Nat.zero_le k))
  · intro k hk
    have hlen := acquired_history_length_before_return π S (sourceRead p q) ω (D k + d k) hk
    change (nativeHistory π S p q (D k + d k) ω).length = D k + d k at hlen
    have hm : (nativeHistory π S p q (D k + d k) ω).map Prod.fst = stageWord D d k := by
      calc
        _ = List.ofFn (fun r : Fin (D k + d k) => σ r.val) := by
          simpa only [Legal, hlen, Fin.val_cast] using hlegal (D k + d k)
        _ = stageWord D d k := Classical.choose_spec (construct_fixed_block_schedule D d hD hd) k
    rw [sourceCount_labels, sourceCount_labels, hm,
      stageWord_counts D d hD hd k false, stageWord_counts D d hD hd k true]
    exact ⟨rfl, rfl⟩

end Landmarks


def countPair (h : History) : ℕ × ℕ := (successCount false h, successCount true h)

def incrementCounts (source b : Bool) (ij : ℕ × ℕ) : ℕ × ℕ :=
  if source then (ij.1, ij.2 + if b then 1 else 0)
  else (ij.1 + if b then 1 else 0, ij.2)

private theorem countPair_append (h : History) (s b : Bool) :
    countPair (h ++ [(s, b)]) = incrementCounts s b (countPair h) := by
  cases s <;> cases b <;>
    simp [countPair, successCount, incrementCounts, List.filter_append]

section OneCall
variable {Seed : Type} [MeasurableSpace Seed]
  (π : Seed → Bool → History → Action) (S : Bool) (p q : unitInterval)

omit [MeasurableSpace Seed] in
private theorem native_history_call_step (n : ℕ) (ω : Seed × Tape) (s : Bool)
    (ha : nativeAction π S p q n ω = .inl s) :
    nativeHistory π S p q (n + 1) ω = nativeHistory π S p q n ω ++
      [(s, sourceRead p q s n ω.2)] := by
  change π ω.1 S (acquiredHistory π S (sourceRead p q) n ω) = .inl s at ha
  simp only [nativeHistory, acquiredHistory, ha]

omit [MeasurableSpace Seed] in
private theorem native_full_history_iff (n : ℕ) (ω : Seed × Tape) :
    (nativeHistory π S p q n ω).length = n ↔
      (n : WithTop ℕ) ≤ nativeCalls π S p q ω := by
  constructor
  · intro hlen
    by_contra hle
    have ht : nativeCalls π S p q ω < (n : WithTop ℕ) := lt_of_not_ge hle
    obtain ⟨m, hm, cell, hcell⟩ := (hittingAfter_lt_iff
      (u := nativeAction π S p q) (s := Set.range (fun c : Bool × Bool => (Sum.inr c : Action)))
      (n := 0) (i := n) (ω := ω)).mp ht
    have hf := (acquired_history_geometry π S (sourceRead p q) ω).2.2 m cell hcell.symm (n - m)
    have he : nativeHistory π S p q n ω = nativeHistory π S p q m ω := by
      simpa only [nativeHistory, Nat.add_sub_of_le hm.2.le] using hf
    have hbound := (acquired_history_geometry π S (sourceRead p q) ω).1 m
    change (nativeHistory π S p q m ω).length ≤ m at hbound
    rw [he] at hlen
    exact (Nat.not_lt_of_ge (hlen ▸ hbound)) hm.2
  · exact acquired_history_length_before_return π S (sourceRead p q) ω n

/-- The actual joint count law advances by one charged call and one fresh
answer, without assuming that the two old success counters are independent. -/
theorem actual_one_call_count_recursion
    (hπ : ∀ S h, Measurable (fun seed => π seed S h))
    (ν : Measure Seed) [IsProbabilityMeasure ν] (n I J : ℕ) :
    rawLaw ν {ω | ((n + 1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (n + 1) ω) = (I, J)} =
      ∑ s : Bool, ∑ b : Bool, ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if (I, J) = incrementCounts s b (i.val, j.val) then
          rawLaw ν {ω | (n : WithTop ℕ) < nativeCalls π S p q ω ∧
            countPair (nativeHistory π S p q n ω) = (i.val, j.val) ∧
            nativeAction π S p q n ω = .inl s} * bernoulliMass (if s then q else p) b
        else 0 := by
  classical
  let : MeasurableSpace History := ⊤
  let Tag := Bool × Bool × Fin (n + 1) × Fin (n + 1)
  let A (t : Tag) : Set (Seed × Tape) := {ω |
    (nativeHistory π S p q n ω).length = n ∧
    countPair (nativeHistory π S p q n ω) = (t.2.2.1.val, t.2.2.2.val) ∧
    nativeAction π S p q n ω = .inl t.1}
  let E (t : Tag) : Set (Seed × Tape) := A t ∩ {ω | sourceRead p q t.1 n ω.2 = t.2.1}
  let K : Finset Tag := Finset.univ.filter (fun t =>
    (I, J) = incrementCounts t.1 t.2.1 (t.2.2.1.val, t.2.2.2.val))
  have hm := native_execution_measurable π hπ S p q
  have hA (t : Tag) : MeasurableSet (A t) := by
    have hhist := (hm.1 n) (show MeasurableSet
      {h : History | h.length = n ∧ countPair h = (t.2.2.1.val, t.2.2.2.val)} from .of_discrete)
    have hact := (hm.2.1 n) (action_singleton_measurable (.inl t.1))
    convert hhist.inter hact using 1
    ext ω
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
    tauto
  have hE (t : Tag) : MeasurableSet (E t) :=
    (hA t).inter (((NativeBernoulliFactoryCriticalMoment.coin_measurable
      (if t.1 then q else p)).comp ((measurable_pi_apply n).comp measurable_snd))
        (measurableSet_singleton t.2.1))
  have hsurvive (t : Tag) : A t = {ω | (n : WithTop ℕ) < nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q n ω) = (t.2.2.1.val, t.2.2.2.val) ∧
      nativeAction π S p q n ω = .inl t.1} := by
    ext ω
    constructor
    · rintro ⟨hlen, hc, ha⟩
      have hnext : (nativeHistory π S p q (n + 1) ω).length = n + 1 := by
        rw [native_history_call_step π S p q n ω t.1 ha, List.length_append,
          List.length_singleton, hlen]
      exact ⟨(WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)).trans_le
        ((native_full_history_iff π S p q (n + 1) ω).mp hnext), hc, ha⟩
    · rintro ⟨ht, hc, ha⟩
      exact ⟨(native_full_history_iff π S p q n ω).mpr ht.le, hc, ha⟩
  have hevent : {ω | ((n + 1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (n + 1) ω) = (I, J)} = ⋃ t ∈ K, E t := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨ht, hc⟩
      have hlt : (n : WithTop ℕ) < nativeCalls π S p q ω :=
        (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)).trans_le ht
      obtain ⟨s, ha⟩ := call_before_return π S (sourceRead p q) ω n hlt
      change nativeAction π S p q n ω = .inl s at ha
      have hlen := (native_full_history_iff π S p q n ω).mpr hlt.le
      have hb (s : Bool) : successCount s (nativeHistory π S p q n ω) < n + 1 := by
        have hh := List.length_filter_le
          (fun v : Bool × Bool => decide (v.1 = s ∧ v.2 = true)) (nativeHistory π S p q n ω)
        change successCount s (nativeHistory π S p q n ω) ≤ _ at hh
        omega
      let i : Fin (n + 1) := ⟨successCount false (nativeHistory π S p q n ω), hb false⟩
      let j : Fin (n + 1) := ⟨successCount true (nativeHistory π S p q n ω), hb true⟩
      let b := sourceRead p q s n ω.2
      refine ⟨(s, b, i, j), ?_, ⟨hlen, rfl, ha⟩, rfl⟩
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [native_history_call_step π S p q n ω s ha, countPair_append] at hc
      exact hc.symm
    · rintro ⟨t, ht, hω⟩
      obtain ⟨hlen, hc, ha⟩ := hω.1
      have hstep := native_history_call_step π S p q n ω t.1 ha
      have hlen' : (nativeHistory π S p q (n + 1) ω).length = n + 1 := by
        rw [hstep, List.length_append, List.length_singleton, hlen]
      refine ⟨(native_full_history_iff π S p q (n + 1) ω).mp hlen', ?_⟩
      rw [hstep, countPair_append, hω.2, hc]
      exact (Finset.mem_filter.mp ht).2.symm
  have hd : Set.PairwiseDisjoint (↑K : Set Tag) E := by
    intro t _ u _ hne
    apply Set.disjoint_left.mpr
    intro ω ht hu
    have hs : t.1 = u.1 := Sum.inl.inj (ht.1.2.2.symm.trans hu.1.2.2)
    have hb : t.2.1 = u.2.1 := ht.2.symm.trans (by simpa only [Set.mem_ofPred_eq, hs] using hu.2)
    have hc := ht.1.2.1.symm.trans hu.1.2.1
    exact hne (Prod.ext hs (Prod.ext hb (Prod.ext
      (Fin.ext (congrArg Prod.fst hc)) (Fin.ext (congrArg Prod.snd hc)))))
  rw [hevent, measure_biUnion_finset hd (fun t _ => hE t)]
  have hmass (t : Tag) : rawLaw ν (E t) = rawLaw ν (A t) *
      bernoulliMass (if t.1 then q else p) t.2.1 :=
    aggregate_native_next_answer_kernel π hπ S ν p q n
      {h | countPair h = (t.2.2.1.val, t.2.2.2.val)} t.1 t.2.1
  simp_rw [hmass, hsurvive]
  simp only [K, Finset.sum_filter]
  dsimp only [Tag] at *
  simp only [Fintype.sum_prod_type]

end OneCall


private theorem translated_zero (p : unitInterval) (i I : ℕ) :
    translatedBinomial 0 i I p = if I = i then 1 else 0 := by
  by_cases h : I = i
  · subst I
    simp [translatedBinomial, binomialMass, binomial_singleton]
  · by_cases hi : i ≤ I
    · have hlt : 0 < I - i := by omega
      simp [translatedBinomial, hi, h, (binomial_mass_support_and_pascal p).2.1 0 (I-i) hlt]
    · simp [translatedBinomial, hi, h]

private theorem translated_select (p : unitInterval) (i l L I : ℕ) (h : i + l ≤ L) :
    (∑ x : Fin (L + 1), if x.val = I then translatedBinomial l i x.val p else 0) =
      translatedBinomial l i I p := by
  classical
  by_cases hI : I ≤ L
  · let t : Fin (L+1) := ⟨I, by omega⟩
    have he (x : Fin (L+1)) : x.val = I ↔ x = t := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [he]
    simp [t]
  · have hi : i ≤ I := by omega
    have hz := (binomial_mass_support_and_pascal p).2.1 l (I-i) (by omega)
    rw [translatedBinomial, if_pos hi, hz]
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.val ≠ I := by have := x.isLt; omega
    simp [hx]

private theorem tensor_one_coin (p q : unitInterval) (i j l m L I J : ℕ)
    (hl : i + l ≤ L) (hm : j + m ≤ L) (s : Bool) :
    (∑ b : Bool, ∑ x : Fin (L+1), ∑ y : Fin (L+1),
      if (I,J) = incrementCounts s b (x.val,y.val) then
        translatedBinomial l i x.val p * translatedBinomial m j y.val q *
          bernoulliMass (if s then q else p) b else 0) =
      translatedBinomial (l + if s then 0 else 1) i I p *
        translatedBinomial (m + if s then 1 else 0) j J q := by
  classical
  cases s
  · have he (b : Bool) (x y : Fin (L+1)) :
        (if (I,J) = incrementCounts false b (x.val,y.val) then
          translatedBinomial l i x.val p * translatedBinomial m j y.val q *
            bernoulliMass p b else 0) =
        (translatedBinomial l i x.val p *
          (if x.val + (if b then 1 else 0) = I then bernoulliMass p b else 0)) *
          (if y.val = J then translatedBinomial m j y.val q else 0) := by
      simp only [incrementCounts, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
      by_cases hx : x.val + (if b then 1 else 0) = I <;>
        by_cases hy : y.val = J <;> simp [hx, hy, eq_comm, mul_assoc, mul_comm] <;> aesop
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simp_rw [he, ← Finset.mul_sum, translated_select q j m L J hm, ← Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [bounded_one_coin_transport p i l L I hl]
  · have he (b : Bool) (x y : Fin (L+1)) :
        (if (I,J) = incrementCounts true b (x.val,y.val) then
          translatedBinomial l i x.val p * translatedBinomial m j y.val q *
            bernoulliMass q b else 0) =
        (if x.val = I then translatedBinomial l i x.val p else 0) *
          (translatedBinomial m j y.val q *
            (if y.val + (if b then 1 else 0) = J then bernoulliMass q b else 0)) := by
      simp only [incrementCounts, ↓reduceIte, Prod.mk.injEq]
      by_cases hx : x.val = I <;>
        by_cases hy : y.val + (if b then 1 else 0) = J <;>
          simp [hx, hy, eq_comm, mul_assoc] <;> aesop
    simp only [↓reduceIte, Nat.add_zero]
    simp_rw [he, ← Finset.mul_sum, ← Finset.sum_mul, translated_select p i l L I hl]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [bounded_one_coin_transport q j m L J hm]

private theorem mixture_one_coin (p q : unitInterval) (N l m L I J : ℕ)
    (hl : N + l ≤ L) (hm : N + m ≤ L) (s : Bool)
    (w : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞) :
    (∑ b : Bool, ∑ x : Fin (L+1), ∑ y : Fin (L+1),
      if (I,J) = incrementCounts s b (x.val,y.val) then
        (∑ i : Fin (N+1), ∑ j : Fin (N+1),
          w i j * translatedBinomial l i.val x.val p * translatedBinomial m j.val y.val q) *
          bernoulliMass (if s then q else p) b else 0) =
      ∑ i : Fin (N+1), ∑ j : Fin (N+1),
        w i j * translatedBinomial (l + if s then 0 else 1) i.val I p *
          translatedBinomial (m + if s then 1 else 0) j.val J q := by
  classical
  simp_rw [Finset.sum_mul, Finset.ite_sum_zero]
  calc
    _ = ∑ i : Fin (N+1), ∑ j : Fin (N+1), ∑ b : Bool,
        ∑ x : Fin (L+1), ∑ y : Fin (L+1),
        if (I,J) = incrementCounts s b (x.val,y.val) then
          w i j * translatedBinomial l i.val x.val p * translatedBinomial m j.val y.val q *
            bernoulliMass (if s then q else p) b else 0 := by
      conv_lhs =>
        arg 2; ext b
        arg 2; ext x
        rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext b
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext i
        arg 2; ext b
        arg 2; ext x
        rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext i
        arg 2; ext b
        rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext i
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have he (b : Bool) (x y : Fin (L+1)) :
          (if (I,J) = incrementCounts s b (x.val,y.val) then
            w i j * translatedBinomial l i.val x.val p * translatedBinomial m j.val y.val q *
              bernoulliMass (if s then q else p) b else 0) =
          w i j * (if (I,J) = incrementCounts s b (x.val,y.val) then
            translatedBinomial l i.val x.val p * translatedBinomial m j.val y.val q *
              bernoulliMass (if s then q else p) b else 0) := by
        split_ifs <;> simp only [mul_assoc, mul_zero]
      simp_rw [he, ← Finset.mul_sum]
      rw [tensor_one_coin p q i.val j.val l m L I J
        (by have := i.isLt; omega) (by have := j.isLt; omega) s]
      simp only [mul_assoc]

section BetweenLandmarks
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)

private theorem fixedSchedule_between (k n : ℕ) (hlo : D k + d k ≤ n)
    (hhi : n < D (k + 1) + d (k + 1)) :
    σ n = if n < D (k + 1) + d k then false else true := by
  have hlen := (stageWord_geometry D d hD hd).1 k
  have he : some (σ n) = (stageWord D d (k + 1))[n]? := by
    simpa only [fixedSchedule, List.getElem?_ofFn, dif_pos hhi] using congrArg
      (fun l : List Bool => l[n]?)
      (Classical.choose_spec (construct_fixed_block_schedule D d hD hd) (k + 1))
  rw [stageWord_succ, List.getElem?_append_right (by rw [hlen]; exact hlo)] at he
  rw [hlen] at he
  have hDk : D k ≤ D (k + 1) := hD.monotone (Nat.le_succ k)
  have hdk : d k ≤ d (k + 1) := hd.monotone (Nat.le_succ k)
  by_cases hn : n < D (k + 1) + d k
  · have hleft : n - (D k + d k) < D (k + 1) - D k := by omega
    simpa only [block, List.getElem?_append, List.length_replicate,
      List.getElem?_replicate, if_pos hleft, Option.some.injEq, if_pos hn] using he
  · have hleft : ¬ n - (D k + d k) < D (k + 1) - D k := by omega
    have hright : n - (D k + d k) - (D (k + 1) - D k) < d (k + 1) - d k := by omega
    simpa only [block, List.getElem?_append, List.length_replicate,
      List.getElem?_replicate, if_neg hleft, if_pos hright, Option.some.injEq, if_neg hn] using he

private theorem actual_between_landmarks (S : Bool) (p q : unitInterval) (ω : RowSeed × Tape)
    (k n : ℕ) (hlo : D k + d k ≤ n) (hhi : n < D (k + 1) + d (k + 1)) :
    (((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ↔
      (n : WithTop ℕ) < nativeCalls π S p q ω) ∧
    (((n + 1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ↔
      ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω) ∧
    (((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω →
      nativeAction π S p q n ω = .inl (if n < D (k + 1) + d k then false else true)) := by
  have hN : StrictMono (fun k => D k + d k) := fun k l hkl => Nat.add_lt_add (hD hkl) (hd hkl)
  have hsurv : ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ↔
      (n : WithTop ℕ) < nativeCalls π S p q ω := by
    constructor
    · intro ht
      cases hτ : nativeCalls π S p q ω with
      | top => exact WithTop.coe_lt_top n
      | coe m =>
        obtain ⟨l, hl⟩ := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.2 m hτ
        rw [hτ] at ht
        have hkl : k < l := hN.lt_iff_lt.mp (by
          simpa only [hl, Nat.cast_id] using WithTop.coe_lt_coe.mp ht)
        have hnm : n < m := by rw [hl]; exact hhi.trans_le (hN.monotone (by omega))
        exact WithTop.coe_lt_coe.mpr hnm
    · exact fun ht => (WithTop.coe_le_coe.mpr hlo).trans_lt ht
  have hnext : ((n + 1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ↔
      (n : WithTop ℕ) < nativeCalls π S p q ω := by
    cases hτ : nativeCalls π S p q ω with
    | top => simp
    | coe m =>
      rw [← WithTop.coe_natCast, ← WithTop.coe_natCast]
      simp only [WithTop.coe_le_coe, WithTop.coe_lt_coe, Nat.cast_id, Nat.succ_le_iff]
  refine ⟨hsurv, hnext.trans hsurv.symm, fun ht => ?_⟩
  have hlt := hsurv.mp ht
  obtain ⟨source, ha⟩ := call_before_return π S (sourceRead p q) ω n hlt
  have hlen := acquired_history_length_before_return π S (sourceRead p q) ω n hlt.le
  have hs := (safe_supported_actions D d a hD hd hc ω.1 S
    (acquiredHistory π S (sourceRead p q) n ω)).1 source ha
  rw [hlen, fixedSchedule_between D d hD hd k n hlo hhi] at hs
  change nativeAction π S p q n ω = .inl source at ha
  simpa only [hs] using ha

/-- Within the two actual call blocks, every count transition uses the same
boundary-survival event; only the scheduled source receives a Bernoulli increment. -/
theorem actual_between_landmark_count_recursion (S : Bool) (p q : unitInterval)
    (k n I J : ℕ) (hlo : D k + d k ≤ n) (hhi : n < D (k + 1) + d (k + 1)) :
    let s := if n < D (k + 1) + d k then false else true
    rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
      ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (n + 1) ω) = (I, J)} =
    ∑ b : Bool, ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if (I, J) = incrementCounts s b (i.val, j.val) then
        rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
          ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
          countPair (nativeHistory π S p q n ω) = (i.val, j.val)} *
            bernoulliMass (if s then q else p) b
      else 0 := by
  classical
  dsimp only
  let s := if n < D (k + 1) + d k then false else true
  let : IsProbabilityMeasure (rowLaw (batchTable D d a hD hd hc)) := by
    unfold rowLaw
    infer_instance
  have hb (ω : RowSeed × Tape) := actual_between_landmarks D d a hD hd hc S p q ω k n hlo hhi
  have hleft : {ω | ((n + 1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (n + 1) ω) = (I, J)} =
      {ω | ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q (n + 1) ω) = (I, J)} := by
    ext ω
    exact and_congr_left (fun _ => (hb ω).2.1)
  have he (s' : Bool) (i j : Fin (n + 1)) :
      {ω | (n : WithTop ℕ) < nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q n ω) = (i.val, j.val) ∧
        nativeAction π S p q n ω = .inl s'} =
      if s' = s then {ω | ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q n ω) = (i.val, j.val)} else ∅ := by
    split_ifs with hs
    · subst s'
      ext ω
      constructor
      · exact fun h => ⟨(hb ω).1.mpr h.1, h.2.1⟩
      · exact fun h => ⟨(hb ω).1.mp h.1, h.2, (hb ω).2.2 h.1⟩
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hs (Sum.inl.inj (hω.2.2.symm.trans ((hb ω).2.2 ((hb ω).1.mpr hω.1))))
  have hrec := actual_one_call_count_recursion π S p q
    (supported_realization σ (batchTable D d a hD hd hc)).1
    (rowLaw (batchTable D d a hD hd hc)) n I J
  rw [hleft] at hrec
  rw [hrec]
  rw [Finset.sum_eq_single s]
  · simp only [he, ↓reduceIte]
    rfl
  · intro s' _ hs
    simp only [he, if_neg hs, measure_empty, zero_mul, ite_self, Finset.sum_const_zero]
  · simp

/-- The joint law of the actual acquired counts at the next batch is the
previous unresolved count law convolved with the two prescribed independent
binomial increments. The unresolved event belongs to this same execution. -/
theorem actual_two_block_count_transport (S : Bool) (p q : unitInterval) (k I J : ℕ) :
    rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
      ((D (k+1) + d (k+1) : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (D (k+1) + d (k+1)) ω) = (I,J)} =
    ∑ i : Fin (D k + d k + 1), ∑ j : Fin (D k + d k + 1),
      rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
        ((D k + d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q (D k + d k) ω) = (i.val,j.val)} *
      translatedBinomial (D (k+1) - D k) i.val I p *
      translatedBinomial (d (k+1) - d k) j.val J q := by
  classical
  let N := D k + d k
  let X := D (k+1) - D k
  let Y := d (k+1) - d k
  let F (n I J : ℕ) := rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
    (N : WithTop ℕ) < nativeCalls π S p q ω ∧
    countPair (nativeHistory π S p q n ω) = (I,J)}
  have hDk : D k < D (k+1) := hD (Nat.lt_succ_self k)
  have hdk : d k < d (k+1) := hd (Nat.lt_succ_self k)
  have hn : N + (X+Y) = D (k+1) + d (k+1) := by dsimp [N,X,Y]; omega
  have hz (I J : ℕ) (hij : N < I ∨ N < J) : F N I J = 0 := by
    apply measure_mono_null (t := ∅) _ measure_empty
    intro ω hω
    have hlen := acquired_history_length_before_return π S (sourceRead p q) ω N hω.1.le
    have hb (s : Bool) : successCount s (nativeHistory π S p q N ω) ≤ N := by
      have hh := List.length_filter_le
        (fun v : Bool × Bool => decide (v.1 = s ∧ v.2 = true)) (nativeHistory π S p q N ω)
      change successCount s (nativeHistory π S p q N ω) ≤ _ at hh
      change (nativeHistory π S p q N ω).length = N at hlen
      omega
    have he : countPair (nativeHistory π S p q N ω) = (I,J) := hω.2
    have hi := hb false
    have hj := hb true
    have hi' := congrArg Prod.fst he
    have hj' := congrArg Prod.snd he
    simp only [countPair] at hi' hj'
    rcases hij with hij | hij <;> omega
  have hbase (I J : ℕ) : F N I J =
      ∑ i : Fin (N+1), ∑ j : Fin (N+1), F N i.val j.val *
        translatedBinomial 0 i.val I p * translatedBinomial 0 j.val J q := by
    simp_rw [translated_zero]
    by_cases hi : I ≤ N
    · let i : Fin (N+1) := ⟨I, by omega⟩
      have hei (x : Fin (N+1)) : I = x.val ↔ x = i :=
        ⟨fun h => Fin.ext h.symm, fun h => (congrArg Fin.val h).symm⟩
      by_cases hj : J ≤ N
      · let j : Fin (N+1) := ⟨J, by omega⟩
        have hej (x : Fin (N+1)) : J = x.val ↔ x = j :=
          ⟨fun h => Fin.ext h.symm, fun h => (congrArg Fin.val h).symm⟩
        simp [hei, hej, i, j]
      · rw [hz I J (Or.inr (by omega))]
        symm
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro y _
        have he : J ≠ y.val := by have := y.isLt; omega
        simp [he]
    · rw [hz I J (Or.inl (by omega))]
      symm
      apply Finset.sum_eq_zero
      intro x _
      have he : I ≠ x.val := by have := x.isLt; omega
      simp [he]
  have hind (r : ℕ) (hr : r ≤ X+Y) (I J : ℕ) :
      F (N+r) I J = ∑ i : Fin (N+1), ∑ j : Fin (N+1), F N i.val j.val *
        translatedBinomial (min r X) i.val I p * translatedBinomial (r-X) j.val J q := by
    induction r generalizing I J with
    | zero => simpa only [Nat.add_zero, Nat.zero_min, Nat.zero_sub] using hbase I J
    | succ r ih =>
      have hlo : D k + d k ≤ N+r := by dsimp [N]; omega
      have hhi : N+r < D (k+1) + d (k+1) := by omega
      have he := actual_between_landmark_count_recursion D d a hD hd hc S p q k (N+r) I J hlo hhi
      change F (N+r+1) I J = _ at he
      rw [show N+(r+1) = N+r+1 by omega, he]
      change (∑ b : Bool, ∑ x : Fin (N+r+1), ∑ y : Fin (N+r+1),
        if (I,J) = incrementCounts (if N+r < D (k+1)+d k then false else true) b (x.val,y.val)
        then F (N+r) x.val y.val *
          bernoulliMass (if (if N+r < D (k+1)+d k then false else true) then q else p) b
        else 0) = _
      simp_rw [ih (by omega)]
      rw [mixture_one_coin p q N (min r X) (r-X) (N+r) I J
        (by omega) (by omega) (if N+r < D (k+1)+d k then false else true)
        (fun i j => F N i.val j.val)]
      by_cases hx : r < X
      · have hs : N+r < D (k+1)+d k := by dsimp [N,X] at *; omega
        have hmin : min (r+1) X = min r X + 1 := by omega
        have hsub : r+1-X = r-X := by omega
        simp only [if_pos hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hmin, hsub]
      · have hs : ¬ N+r < D (k+1)+d k := by dsimp [N,X] at *; omega
        have hmin : min (r+1) X = min r X := by omega
        have hsub : r+1-X = r-X+1 := by omega
        simp only [if_neg hs, ↓reduceIte, Nat.add_zero, hmin, hsub]
  have hevent : {ω | ((D (k+1)+d (k+1) : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (D (k+1)+d (k+1)) ω) = (I,J)} =
      {ω | (N : WithTop ℕ) < nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q (N+(X+Y)) ω) = (I,J)} := by
    ext ω
    rw [hn]
    have ht := (actual_between_landmarks D d a hD hd hc S p q ω k
      (D (k+1)+d (k+1)-1) (by omega) (by omega)).2.1
    have hp : D (k+1)+d (k+1)-1+1 = D (k+1)+d (k+1) := by omega
    simpa only [hp, N, Set.mem_ofPred_eq] using and_congr_left (fun _ => ht)
  rw [hevent]
  exact (hind (X+Y) le_rfl I J).trans (by
    simp only [Nat.min_eq_right (Nat.le_add_right X Y), Nat.add_sub_cancel_left]
    rfl)

end BetweenLandmarks

section InitialBatch
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)

private theorem fixedSchedule_initial (n : ℕ) (hn : n < D 0 + d 0) :
    σ n = if n < D 0 then false else true := by
  have he : some (σ n) = (stageWord D d 0)[n]? := by
    simpa only [fixedSchedule, List.getElem?_ofFn, dif_pos hn] using congrArg
      (fun l : List Bool => l[n]?)
      (Classical.choose_spec (construct_fixed_block_schedule D d hD hd) 0)
  have hz : stageWord D d 0 = List.replicate (D 0) false ++ List.replicate (d 0) true := by
    simp [stageWord, block]
  rw [hz] at he
  simp only [List.getElem?_append, List.length_replicate, List.getElem?_replicate] at he
  by_cases h : n < D 0
  · simpa only [if_pos h, Option.some.injEq] using he
  · have ht : n - D 0 < d 0 := by omega
    simpa only [if_pos ht, if_neg h, Option.some.injEq] using he

/-- The initial actual batch has the two binomial count laws, also when one
or both initial degrees vanish and either source rate is an endpoint. -/
theorem initial_actual_batch_mass (S : Bool) (p q : unitInterval) (I J : ℕ) :
    rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
      ((D 0+d 0 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (D 0+d 0) ω) = (I,J)} =
        binomialMass (D 0) I p * binomialMass (d 0) J q := by
  classical
  let μ := rawLaw (rowLaw (batchTable D d a hD hd hc))
  let F (n I J : ℕ) := μ {ω | countPair (nativeHistory π S p q n ω) = (I,J)}
  have := NativeBernoulliFactoryCriticalMoment.uniform_probability
  let hprob : IsProbabilityMeasure μ := by
    dsimp [μ, rawLaw, rowLaw]
    infer_instance
  let : IsProbabilityMeasure (rowLaw (batchTable D d a hD hd hc)) := by
    unfold rowLaw
    infer_instance
  have hbound (ω : RowSeed × Tape) :=
    (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.1
  have hind (n : ℕ) (hn : n ≤ D 0+d 0) (I J : ℕ) :
      F n I J = translatedBinomial (min n (D 0)) 0 I p *
        translatedBinomial (n-D 0) 0 J q := by
    induction n generalizing I J with
    | zero =>
      simp only [Nat.zero_min, Nat.zero_sub, translated_zero]
      change μ {ω | (0,0) = (I,J)} = (if I = 0 then 1 else 0) * (if J = 0 then 1 else 0)
      by_cases hI : I = 0 <;> by_cases hJ : J = 0 <;> simp [hI, hJ, eq_comm]
    | succ n ih =>
      let s := if n < D 0 then false else true
      have ha (ω : RowSeed × Tape) : nativeAction π S p q n ω = .inl s := by
        have hlt : (n : WithTop ℕ) < nativeCalls π S p q ω :=
          (WithTop.coe_lt_coe.mpr (by omega : n < D 0+d 0)).trans_le (hbound ω)
        obtain ⟨source, hs⟩ := call_before_return π S (sourceRead p q) ω n hlt
        have hlen := acquired_history_length_before_return π S (sourceRead p q) ω n hlt.le
        have hh := (safe_supported_actions D d a hD hd hc ω.1 S
          (nativeHistory π S p q n ω)).1 source hs
        change (nativeHistory π S p q n ω).length = n at hlen
        rw [hlen, fixedSchedule_initial D d hD hd n (by omega)] at hh
        change nativeAction π S p q n ω = .inl source at hs
        simpa only [hh, s] using hs
      have he := actual_one_call_count_recursion π S p q
        (supported_realization σ (batchTable D d a hD hd hc)).1
        (rowLaw (batchTable D d a hD hd hc)) n I J
      have ht (ω : RowSeed × Tape) : ((n+1 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω :=
        (WithTop.coe_le_coe.mpr hn).trans (hbound ω)
      have hl (ω : RowSeed × Tape) : (n : WithTop ℕ) < nativeCalls π S p q ω :=
        (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)).trans_le (ht ω)
      simp only [ht, hl, true_and, ha, Sum.inl.injEq] at he
      change F (n+1) I J = _ at he
      rw [he, Finset.sum_eq_single s]
      · simp only [eq_self, and_true]
        change (∑ b : Bool, ∑ i : Fin (n+1), ∑ j : Fin (n+1),
          if (I,J) = incrementCounts s b (i.val,j.val) then F n i.val j.val *
            bernoulliMass (if s then q else p) b else 0) = _
        simp_rw [ih (by omega)]
        rw [tensor_one_coin p q 0 0 (min n (D 0)) (n-D 0) n I J (by omega) (by omega) s]
        by_cases hs : n < D 0
        · have hm : min (n+1) (D 0) = min n (D 0)+1 := by omega
          have hd' : n+1-D 0 = n-D 0 := by omega
          simp only [s, if_pos hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hm, hd']
        · have hm : min (n+1) (D 0) = min n (D 0) := by omega
          have hd' : n+1-D 0 = n-D 0+1 := by omega
          simp only [s, if_neg hs, ↓reduceIte, Nat.add_zero, hm, hd']
      · intro s' _ hs
        have hs' : s ≠ s' := Ne.symm hs
        simp only [hs', and_false, Set.ofPred_false, measure_empty, zero_mul,
          ite_self, Finset.sum_const_zero]
      · simp
  simp only [hbound, true_and]
  exact (hind (D 0+d 0) le_rfl I J).trans (by
    simp only [Nat.min_eq_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      translatedBinomial, Nat.zero_le, ↓reduceIte, Nat.sub_zero])

end InitialBatch

section CountClassification
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)

private theorem batchTable_at_landmark (S : Bool) (h : History) (k : ℕ)
    (hl : Legal σ h) (hn : h.length = D k + d k)
    (i : Fin (D k+1)) (j : Fin (d k+1))
    (hi : successCount false h = i.val) (hj : successCount true h = j.val)
    (r : Option Bool) :
    batchTable D d a hD hd hc (S,h) (encodeStage σ (D k+d k) r) =
      fiberRow D d a hD.monotone hd.monotone hc k i j r := by
  classical
  have hk : ∃ l, h.length = D l+d l := ⟨k,hn⟩
  have hN : StrictMono (fun k => D k+d k) := fun x y h => Nat.add_lt_add (hD h) (hd h)
  have hf : Nat.find hk = k := hN.injective ((Nat.find_spec hk).symm.trans hn)
  unfold batchTable
  dsimp only
  rw [if_pos hl, dif_pos hk, hf]
  simp only [hi, hj, rowNat, dif_pos i.isLt, dif_pos j.isLt, hn]
  have hinj : Function.Injective (encodeStage σ (D k+d k)) := by
    intro r s h
    cases r <;> cases s <;> simpa [encodeStage] using h
  simp only [PMF.map_apply, hinj.eq_iff, tsum_ite_eq']

/-- A count fiber at an actually reached landmark uses its prescribed row
of the single table. This is joint mass classification, including zero incoming
mass, without conditioning on a positive-probability count fiber. -/
theorem actual_count_fiber_classification (S : Bool) (p q : unitInterval)
    (k : ℕ) (i : Fin (D k+1)) (j : Fin (d k+1)) (r : Option Bool) :
    rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
      ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (D k+d k) ω) = (i.val,j.val) ∧
      nativeAction π S p q (D k+d k) ω = encodeStage σ (D k+d k) r} =
    rawLaw (rowLaw (batchTable D d a hD hd hc)) {ω |
      ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q (D k+d k) ω) = (i.val,j.val)} *
        fiberRow D d a hD.monotone hd.monotone hc k i j r := by
  classical
  let N := D k+d k
  let table := batchTable D d a hD hd hc
  let μ := rawLaw (rowLaw table)
  let act := encodeStage σ N r
  let C (π' : RowSeed → Bool → History → Action) (ω : RowSeed × Tape) :=
    (nativeHistory π' S p q N ω).length = N ∧
    sourceCount false (nativeHistory π' S p q N ω) = D k ∧
    sourceCount true (nativeHistory π' S p q N ω) = d k ∧
    successCount false (nativeHistory π' S p q N ω) = i.val ∧
    successCount true (nativeHistory π' S p q N ω) = j.val
  have heq : ∀ᵐ ω ∂μ,
      nativeHistory π S p q N ω = nativeHistory tablePolicy S p q N ω ∧
      nativeAction π S p q N ω = nativeAction tablePolicy S p q N ω := by
    have h := (Measure.quasiMeasurePreserving_fst
      (μ := rowLaw table) (ν := Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)))).ae
      (supported_realization σ table).2
    filter_upwards [h] with ω hω
    exact ⟨(hω.2 S p q ω.2).1 N, (hω.2 S p q ω.2).2.1 N⟩
  have hC (ω : RowSeed × Tape) :
      ((N : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
        countPair (nativeHistory π S p q N ω) = (i.val,j.val)) ↔ C π ω := by
    constructor
    · rintro ⟨ht,hij⟩
      have hs := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 k ht
      exact ⟨(native_full_history_iff π S p q N ω).mpr ht, hs.1, hs.2,
        congrArg Prod.fst hij, congrArg Prod.snd hij⟩
    · rintro ⟨hlen,_,_,hi,hj⟩
      exact ⟨(native_full_history_iff π S p q N ω).mp hlen, Prod.ext hi hj⟩
  have hleft : μ {ω | (N : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q N ω) = (i.val,j.val) ∧
      nativeAction π S p q N ω = act} =
      μ {ω | C tablePolicy ω ∧ nativeAction tablePolicy S p q N ω = act} := by
    apply measure_congr
    filter_upwards [heq] with ω hω
    apply propext
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
    rw [← and_assoc, hC]
    simp only [C, hω.1, hω.2]
  have hright : μ {ω | (N : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      countPair (nativeHistory π S p q N ω) = (i.val,j.val)} = μ {ω | C tablePolicy ω} := by
    apply measure_congr
    filter_upwards [heq] with ω hω
    apply propext
    change (_ ∧ _) ↔ _
    rw [hC]
    simp only [C, hω.1]
    rfl
  change μ _ = μ _ * _
  rw [hleft, hright]
  have hagg := all_history_count_fiber_aggregation table S p q N (D k) (d k) i.val j.val act
  have hreach := all_history_count_fiber_reach table S p q N (D k) (d k) i.val j.val
  simp only [C, and_assoc]
  rw [hagg, hreach, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hw' := (Finset.mem_filter.mp hw).2
  have hwi : successCount false (List.ofFn w) = i.val := hw'.2.2.1
  have hwj : successCount true (List.ofFn w) = j.val := hw'.2.2.2
  by_cases hl : Legal σ (List.ofFn w)
  · rw [batchTable_at_landmark D d a hD hd hc S (List.ofFn w) k hl
      List.length_ofFn i j hwi hwj r]
    ac_rfl
  · have hz : historyPathWeight table S (List.ofFn w) * historyLikelihood p q (List.ofFn w) = 0 := by
      rw [← actual_history_reach_law table S p q (List.ofFn w)]
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [heq] with ω hω
      intro hh
      have hg := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).1 N
      have hw : nativeHistory tablePolicy S p q N ω = List.ofFn w := by
        simpa only [reachedHistory, List.length_ofFn, Set.mem_ofPred_eq] using hh
      rw [hω.1, hw] at hg
      exact hl hg
    calc
      _ = (historyPathWeight table S (List.ofFn w) * historyLikelihood p q (List.ofFn w)) *
          table (S,List.ofFn w) act := by ac_rfl
      _ = _ := by rw [hz, zero_mul, zero_mul]

end CountClassification

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution
