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

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution
