/- GID: D5/S3/Combinatorics/Dice/EaslickCycleSeeds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/EaslickCycleSeeds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Chain]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Dice/EaslickPaddedCycles.longer_cycle; instance=D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed_check
   digest: Fixed simple cycles supply the finite seeds for minimal-advantage padding. -/

import D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
import Mathlib.Data.List.Chain

/-! The seven- through ten-face cycle data are by Terry Easlick,
arXiv:2610.40321v1, Appendices G--J, https://arxiv.org/html/2610.40321v1,
CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
The six-face cycle is an exact count construction. The eleven-face cycle is derived
from the seven-face source cycle by shifting labels and adding nested extremes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.EaslickCycleSeeds
open EaslickMinimalAdvantage

/-- Six fixed seed cycles, each without a duplicated closure row. -/
def sourceSeed : ℕ → List (List ℕ)
  | 6 => [
    [1, 1, 2, 5, 5, 5],
    [1, 3, 4, 4, 4, 4],
    [2, 2, 2, 3, 6, 6],
    [1, 1, 2, 5, 5, 6],
    [1, 3, 3, 4, 4, 4],
    [2, 2, 3, 3, 3, 6]]
  | 7 => [
    [1, 1, 1, 3, 3, 4, 7],
    [2, 2, 2, 2, 2, 2, 6],
    [1, 1, 1, 3, 5, 5, 5],
    [1, 1, 2, 2, 4, 4, 4],
    [1, 1, 3, 3, 3, 3, 3],
    [1, 2, 2, 2, 2, 5, 6],
    [1, 1, 1, 4, 4, 4, 5],
    [1, 1, 3, 3, 3, 3, 4],
    [1, 2, 2, 2, 2, 5, 7],
    [1, 1, 1, 4, 4, 4, 6],
    [1, 1, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 3, 5, 5, 6],
    [2, 2, 2, 2, 3, 4, 4]]
  | 8 => [
    [1, 1, 1, 2, 4, 6, 6, 6],
    [1, 1, 3, 3, 3, 3, 3, 5],
    [2, 2, 2, 2, 2, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 7, 8],
    [2, 2, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 2, 5, 5, 5, 6],
    [1, 2, 3, 3, 3, 4, 4, 4],
    [2, 2, 2, 2, 2, 3, 6, 6],
    [1, 1, 1, 2, 5, 5, 5, 7],
    [1, 2, 3, 3, 4, 4, 4, 4],
    [1, 2, 2, 2, 3, 3, 6, 6],
    [1, 1, 1, 2, 5, 5, 5, 5],
    [1, 2, 3, 4, 4, 4, 4, 4],
    [1, 2, 3, 3, 3, 3, 4, 6],
    [2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 3, 4, 4, 8, 8],
    [2, 2, 2, 2, 2, 3, 6, 7],
    [1, 1, 1, 2, 5, 5, 5, 8],
    [1, 2, 4, 4, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 6, 7, 7],
    [2, 2, 2, 2, 2, 5, 5, 6],
    [1, 1, 1, 4, 4, 4, 6, 7],
    [1, 1, 3, 3, 3, 3, 5, 6],
    [2, 2, 2, 2, 2, 4, 5, 8],
    [1, 1, 1, 3, 3, 7, 7, 7],
    [2, 2, 2, 2, 2, 2, 6, 8],
    [1, 1, 1, 3, 5, 5, 5, 6],
    [1, 3, 3, 3, 3, 4, 4, 4],
    [2, 2, 2, 3, 3, 3, 3, 7]]
  | 9 => [
    [1, 1, 1, 1, 3, 3, 3, 3, 7],
    [2, 2, 2, 2, 2, 2, 2, 2, 6],
    [1, 1, 1, 1, 3, 5, 5, 5, 5],
    [1, 1, 2, 2, 2, 4, 4, 4, 4],
    [1, 1, 1, 2, 3, 3, 3, 3, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 7],
    [1, 1, 1, 1, 3, 3, 6, 6, 6],
    [2, 2, 2, 2, 2, 2, 2, 4, 5],
    [1, 1, 1, 1, 3, 3, 4, 5, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 8]]
  | 10 => [
    [1, 1, 1, 1, 2, 4, 4, 4, 4, 4],
    [1, 2, 2, 3, 3, 3, 3, 3, 3, 3],
    [1, 2, 2, 2, 2, 2, 2, 4, 7, 7],
    [1, 1, 1, 1, 3, 3, 3, 6, 6, 6],
    [1, 2, 2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 1, 2, 4, 4, 4, 4, 5],
    [1, 2, 3, 3, 3, 3, 3, 3, 3, 3],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 7],
    [1, 1, 1, 1, 2, 4, 5, 5, 5, 6],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 4],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 6],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 6],
    [1, 2, 2, 2, 2, 2, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 5],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 7],
    [1, 1, 1, 1, 3, 3, 3, 6, 6, 7],
    [2, 2, 2, 2, 2, 2, 2, 4, 5, 5],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 1, 3, 4, 4, 5, 5, 6],
    [1, 2, 2, 3, 3, 3, 3, 3, 3, 4],
    [1, 2, 2, 2, 2, 2, 2, 4, 8, 8],
    [1, 1, 1, 1, 3, 3, 3, 6, 7, 7],
    [2, 2, 2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 2, 2, 4, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 6],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 8],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 8],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 7],
    [1, 2, 2, 2, 2, 3, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 7],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 7],
    [1, 1, 1, 1, 3, 4, 4, 5, 5, 5],
    [2, 2, 2, 3, 3, 3, 3, 3, 3, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 8],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 6],
    [1, 1, 2, 3, 3, 3, 3, 3, 4, 4],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 7],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 8],
    [1, 2, 2, 2, 2, 4, 4, 4, 4, 4],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 9],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 7],
    [1, 2, 2, 3, 3, 3, 3, 3, 4, 4],
    [1, 2, 2, 2, 2, 2, 2, 4, 8, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 7],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 6],
    [1, 1, 1, 1, 4, 4, 4, 5, 5, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 5],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 8],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 9],
    [1, 2, 2, 2, 3, 3, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 8],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 8],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 6],
    [1, 1, 2, 3, 3, 3, 3, 3, 4, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 9, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 8],
    [1, 2, 2, 2, 2, 2, 2, 6, 6, 6],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 10],
    [1, 2, 2, 2, 3, 4, 4, 4, 4, 4],
    [1, 1, 1, 1, 3, 3, 3, 4, 8, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 7, 8],
    [1, 1, 1, 1, 2, 4, 6, 6, 6, 7],
    [1, 1, 1, 3, 3, 3, 3, 3, 5, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 9, 10],
    [1, 1, 1, 1, 3, 3, 3, 7, 8, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 10],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 8],
    [1, 2, 3, 3, 3, 3, 3, 3, 3, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 9],
    [1, 1, 1, 1, 3, 5, 5, 5, 5, 6],
    [1, 1, 1, 2, 2, 4, 4, 4, 4, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 9],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 9],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 7],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 6],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 9],
    [1, 1, 1, 1, 2, 5, 5, 5, 6, 6],
    [1, 2, 2, 2, 4, 4, 4, 4, 4, 4],
    [1, 1, 1, 2, 3, 3, 3, 4, 8, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 7, 9],
    [1, 1, 1, 1, 2, 4, 6, 6, 6, 8],
    [1, 1, 2, 3, 3, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 10, 10],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 9],
    [2, 2, 2, 2, 2, 2, 2, 4, 5, 6],
    [1, 1, 1, 1, 3, 3, 3, 4, 9, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 8, 9],
    [1, 1, 1, 1, 2, 4, 6, 6, 7, 8],
    [1, 1, 3, 3, 3, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 2, 4, 4, 4, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 10],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 10],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 8],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 7],
    [1, 2, 2, 2, 2, 2, 2, 6, 6, 7],
    [1, 1, 1, 1, 3, 3, 5, 5, 5, 10],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 10],
    [2, 2, 2, 2, 2, 2, 2, 4, 6, 6],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 9],
    [2, 2, 2, 3, 3, 3, 3, 3, 4, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 10],
    [1, 1, 1, 1, 4, 4, 4, 5, 5, 6],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 8],
    [1, 2, 2, 2, 2, 2, 2, 5, 7, 8],
    [1, 1, 1, 1, 3, 4, 4, 4, 6, 7],
    [2, 2, 2, 2, 3, 3, 3, 3, 3, 5]]
  | 11 => [
    [1, 1, 3, 3, 3, 5, 5, 6, 9, 11, 11],
    [2, 2, 4, 4, 4, 4, 4, 4, 8, 10, 10],
    [1, 1, 3, 3, 3, 5, 7, 7, 7, 11, 11],
    [2, 2, 3, 3, 4, 4, 6, 6, 6, 10, 10],
    [1, 1, 3, 3, 5, 5, 5, 5, 5, 11, 11],
    [2, 2, 3, 4, 4, 4, 4, 7, 8, 10, 10],
    [1, 1, 3, 3, 3, 6, 6, 6, 7, 11, 11],
    [2, 2, 3, 3, 5, 5, 5, 5, 6, 10, 10],
    [1, 1, 3, 4, 4, 4, 4, 7, 9, 11, 11],
    [2, 2, 3, 3, 3, 6, 6, 6, 8, 10, 10],
    [1, 1, 3, 3, 5, 5, 5, 5, 7, 11, 11],
    [2, 2, 3, 4, 4, 4, 4, 8, 9, 10, 10],
    [1, 1, 3, 3, 3, 5, 7, 7, 8, 11, 11],
    [2, 2, 4, 4, 4, 4, 5, 6, 6, 10, 10]]
  | _ => []

/-- Scan successive encoded vertices without assuming a semantic chain law. -/
def checkSteps {α : Type} (edge : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: tail => edge a b && checkSteps edge (b :: tail)

private theorem checkSteps_sound {α : Type} (edge : α → α → Bool) (c : List α)
    (h : checkSteps edge c = true) : c.IsChain (fun a b => edge a b = true) := by
  induction c with
  | nil => exact .nil
  | cons a tail ih =>
    cases tail with
    | nil => exact .singleton a
    | cons b tail =>
      simp only [checkSteps, Bool.and_eq_true] at h
      exact List.isChain_cons_cons.mpr ⟨h.1, ih h.2⟩

/-- Executable face-count, adjacent-order and label-range tests for arbitrary dice. -/
def checkDie (n : ℕ) (d : List ℕ) : Bool :=
  (d.length == n) && checkSteps (fun a b => decide (a ≤ b)) d &&
    d.all (fun x => decide (1 ≤ x ∧ x ≤ n))

private theorem checkDie_sound (n : ℕ) (d : List ℕ) (h : checkDie n d = true) :
    IsDie n d := by
  simp only [checkDie, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.1.1, ?_, h.2⟩
  have hs := checkSteps_sound _ _ h.1.2
  exact (hs.imp (by simpa using fun a b (hab : decide (a ≤ b) = true) => of_decide_eq_true hab)).pairwise

/-- Check the actual encoded cycle: nonempty, no duplicate vertices, valid dice,
    and every successive score including the closing edge. No graph law is input. -/
def checkCycle (n : ℕ) (c : List (List ℕ)) : Bool :=
  (!c.isEmpty) && (c.dedup.length == c.length) && c.all (checkDie n) &&
    checkSteps (fun d e => winCount d e == threshold n) (c ++ [c.head!])

/-- Successful arbitrary-input checking reconstructs the original probability graph. -/
theorem checkCycle_sound (n : ℕ) (hn : 3 ≤ n) (c : List (List ℕ))
    (h : checkCycle n c = true) : HasCycle n c.length := by
  simp only [checkCycle, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at h
  have hne : c ≠ [] := by
    intro he
    simp [he] at h
  have hnd : c.Nodup := List.nodup_iff_length_dedup_eq.mpr h.1.1.2
  have hvalid (d : List ℕ) (hd : d ∈ c) : IsDie n d := checkDie_sound n d (h.1.2 d hd)
  have hhead : c.head! ∈ c := by cases c with | nil => contradiction | cons a l => simp
  have hv (d : List ℕ) (hd : d ∈ c ++ [c.head!]) : IsDie n d := by
    rcases List.mem_append.mp hd with hmem | hmem
    · exact hvalid d hmem
    · have : d = c.head! := by simpa using hmem
      rw [this]
      exact hvalid _ hhead
  refine ⟨c,rfl,hnd,hne,?_⟩
  exact (checkSteps_sound _ _ h.2).imp_of_mem_imp (fun a b ha hb hab =>
    (edge_iff n hn a b (hv a ha) (hv b hb)).mpr (by simpa using hab))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The first actual checker inputs are precisely the six source and derived seeds. -/
theorem sourceSeed_check (n : ℕ) (hn : n ∈ [6,7,8,9,10,11]) :
    checkCycle n (sourceSeed n) = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- These finite witnesses are ingredients for the full parameter cover. -/
theorem finite_cycle_witnesses :
    HasCycle 6 6 ∧ HasCycle 7 14 ∧ HasCycle 8 29 ∧
      HasCycle 9 10 ∧ HasCycle 10 110 ∧ HasCycle 11 14 := by
  exact ⟨checkCycle_sound 6 (by decide) _ (sourceSeed_check 6 (by decide)),
    checkCycle_sound 7 (by decide) _ (sourceSeed_check 7 (by decide)),
    checkCycle_sound 8 (by decide) _ (sourceSeed_check 8 (by decide)),
    checkCycle_sound 9 (by decide) _ (sourceSeed_check 9 (by decide)),
    checkCycle_sound 10 (by decide) _ (sourceSeed_check 10 (by decide)),
    checkCycle_sound 11 (by decide) _ (sourceSeed_check 11 (by decide))⟩

end D5.S3.Combinatorics.Dice.EaslickCycleSeeds
