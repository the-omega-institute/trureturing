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

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution
