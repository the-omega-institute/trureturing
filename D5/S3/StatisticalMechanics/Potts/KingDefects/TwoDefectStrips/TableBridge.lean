/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sorted successor lists certify all transfer columns together. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229752.result)
count_filterMap_sum: proof_shape=bind-only; consumers=count_successors
count_successors: proof_shape=bind-only; consumers=Width5.Certificate.transition_counts
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! A list equality supplies every coordinate of a transfer row. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge

private theorem count_filterMap_sum {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → Option β) (s : β) :
    ((l.filterMap f).count s : ℤ) =
      (l.map fun r => if f r = some s then (1 : ℤ) else 0).sum := by
  rw [List.filterMap_eq_flatMap_toList, List.count_flatMap]
  push_cast
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  cases h : f a with
  | none => simp [h]
  | some b =>
    by_cases hb : b = s
    · subst b; simp [h, List.count_cons]
    · simp [h, List.count_cons, hb, Ne.symm hb]

theorem count_successors {q k M : ℕ} (P : (Fin k → Fin q) → Prop)
    [DecidablePred P] (c : (Fin k → Fin q) → Fin M) (s : Fin M) :
    (((List.ofFn (fun i : Fin (q^k) => finFunctionFinEquiv.symm i)).filterMap
      (fun r => if P r then some (c r) else none)).insertionSort (· ≤ ·)).count s =
      ∑ r : Fin k → Fin q, if P r ∧ c r = s then 1 else 0 := by
  have h := count_filterMap_sum
    (List.ofFn (fun i : Fin (q^k) => finFunctionFinEquiv.symm i))
    (fun r => if P r then some (c r) else none) s
  rw [List.map_ofFn, List.sum_ofFn] at h
  have he : (∑ i : Fin (q^k), if
      (if P (finFunctionFinEquiv.symm i) then some (c (finFunctionFinEquiv.symm i))
        else none) = some s then (1 : ℤ) else 0) =
      ∑ r : Fin k → Fin q, if P r ∧ c r = s then (1 : ℤ) else 0 := by
    rw [← finFunctionFinEquiv.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  have hp := (List.perm_insertionSort (· ≤ ·)
    ((List.ofFn (fun i : Fin (q^k) => finFunctionFinEquiv.symm i)).filterMap
      (fun r => if P r then some (c r) else none))).count_eq s
  exact_mod_cast hp.trans (by exact_mod_cast h.trans he)

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
