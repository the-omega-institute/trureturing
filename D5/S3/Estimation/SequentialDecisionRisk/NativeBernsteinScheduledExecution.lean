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

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution
