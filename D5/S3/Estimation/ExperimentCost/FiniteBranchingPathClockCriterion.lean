/- GID: D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Path divergence, depth-minimum divergence, and finite clock sublevels are equivalent. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Fintype.Order
import Mathlib.Data.List.TFAE
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.KonigLemma
import Mathlib.Order.Filter.Cofinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion

open Filter Set
open scoped BigOperators

/-- The accumulated clock along a finite history. -/
noncomputable def pathClock {A : Type*} (c : List A -> A -> ℝ) (h : List A) : ℝ :=
  ∑ i : Fin h.length, c (h.take i) (h.get i)

/-- The least clock value among histories at a fixed depth. -/
noncomputable def minimumPathClock {A : Type*} [Fintype A] [Nonempty A]
    (c : List A -> A -> ℝ) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun w : Fin n -> A => pathClock c (List.ofFn w)

/-- For a finite nonempty alphabet and nonnegative history-dependent edge costs, divergence along
every infinite path, divergence of the minimum clock at each depth, and finiteness of every bounded
clock sublevel are equivalent. -/
theorem finite_branching_path_clock_criterion {A : Type*} [Fintype A] [Nonempty A]
    (c : List A -> A -> ℝ) (hc : ∀ h x, 0 ≤ c h x) :
    List.TFAE [
      ∀ omega : ℕ -> A,
        Tendsto (fun n => pathClock c (List.ofFn fun i : Fin n => omega i)) atTop atTop,
      Tendsto (minimumPathClock c) atTop atTop,
      ∀ b : ℝ, {h : List A | pathClock c h ≤ b}.Finite] := by
  classical
  have hclock_nil : pathClock c [] = 0 := by
    simp [pathClock]
  have hclock_snoc : ∀ (h : List A) (x : A),
      pathClock c (h ++ [x]) = pathClock c h + c h x := by
    clear hc hclock_nil
    intro h x
    induction h generalizing c with
    | nil => simp [pathClock]
    | cons a h ih =>
        simp [pathClock, Fin.sum_univ_succ, add_assoc]
        simpa only [pathClock, List.get_eq_getElem] using
          ih (c := fun p y => c (a :: p) y)
  have hclock_append_le : ∀ (h tail : List A), pathClock c h ≤ pathClock c (h ++ tail) := by
    intro h tail
    induction tail using List.reverseRecOn with
    | nil => simp
    | append_singleton tail x ih =>
        rw [← List.append_assoc, hclock_snoc]
        exact ih.trans (le_add_of_nonneg_right (hc _ _))
  have hclock_take_le : ∀ (h : List A) (k : ℕ), pathClock c (h.take k) ≤ pathClock c h := by
    intro h k
    simpa only [List.take_append_drop] using hclock_append_le (h.take k) (h.drop k)
  have hminimum_le : ∀ (n : ℕ) (w : Fin n -> A),
      minimumPathClock c n ≤ pathClock c (List.ofFn w) := by
    intro n w
    exact Finset.inf'_le _ (Finset.mem_univ w)
  have hminimum_monotone : Monotone (minimumPathClock c) := by
    apply monotone_nat_of_le_succ
    intro n
    apply Finset.le_inf'
    intro w _
    refine (hminimum_le n (Fin.take n (Nat.le_succ n) w)).trans ?_
    rw [Fin.ofFn_take_eq_take_ofFn]
    exact hclock_take_le (List.ofFn w) n
  tfae_have 1 -> 2 := by
    intro hpaths
    rw [hminimum_monotone.tendsto_atTop_atTop_iff]
    intro b
    by_contra hlevel
    push Not at hlevel
    let Level (n : ℕ) :=
      {w : Fin n -> A // pathClock c (List.ofFn w) ≤ b}
    have hlevel_nonempty : ∀ n, Nonempty (Level n) := by
      intro n
      have hattain := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun w : Fin n -> A => pathClock c (List.ofFn w))
      obtain ⟨w, _, hw⟩ := hattain
      exact ⟨⟨w, hw ▸ (hlevel n).le⟩⟩
    let _ (n : ℕ) : Nonempty (Level n) := hlevel_nonempty n
    let project : {i j : ℕ} -> (hij : i ≤ j) -> Level j -> Level i :=
      fun {i j} hij w => ⟨Fin.take i hij w.1, by
        rw [Fin.ofFn_take_eq_take_ofFn]
        exact (hclock_take_le (List.ofFn w.1) i).trans w.2⟩
    have hproject_refl : ∀ ⦃i⦄ (w : Level i), project rfl.le w = w := by
      intro i w
      apply Subtype.ext
      exact Fin.take_eq_self w.1
    have hproject_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (w : Level k),
        project hij (project hjk w) = project (hij.trans hjk) w := by
      intro i j k hij hjk w
      apply Subtype.ext
      exact Fin.take_take hij hjk w.1
    have hproject_finite : ∀ i w,
        {v : Level (i + 1) | project (Nat.le_add_right i 1) v = w}.Finite := by
      intro i w
      exact Set.toFinite _
    obtain ⟨levels, hlevels⟩ := exists_seq_forall_proj_of_forall_finite
      project hproject_refl hproject_trans hproject_finite
    let omega : ℕ -> A := fun n => (levels (n + 1)).1 (Fin.last n)
    have hprefix : ∀ n,
        List.ofFn (fun i : Fin n => omega i) = List.ofFn (levels n).1 := by
      intro n
      rw [List.ofFn_inj]
      funext i
      have hcompat := congrArg Subtype.val
        (hlevels (Nat.succ_le_iff.mpr i.isLt) :
          project (Nat.succ_le_iff.mpr i.isLt) (levels n) = levels (i + 1))
      have hat := congrFun hcompat (Fin.last i)
      exact hat.symm
    have hbounded : ∀ n, pathClock c (List.ofFn fun i : Fin n => omega i) ≤ b := by
      intro n
      rw [hprefix n]
      exact (levels n).2
    have hevent := tendsto_atTop.1 (hpaths omega) (b + 1)
    obtain ⟨n, hn⟩ := hevent.exists
    exact (not_le_of_gt (lt_add_one b)) ((hn.trans (hbounded n)))
  tfae_have 2 -> 3 := by
    intro hminimum b
    have hevent := tendsto_atTop.1 hminimum (b + 1)
    obtain ⟨n, hn⟩ := hevent.exists
    apply (List.finite_length_lt A n).subset
    intro h hh
    by_contra hnot
    have hnlen : n ≤ h.length := Nat.le_of_not_gt hnot
    have hmin_n : minimumPathClock c n ≤ minimumPathClock c h.length :=
      hminimum_monotone hnlen
    have hmin_h : minimumPathClock c h.length ≤ pathClock c h := by
      simpa only [List.ofFn_get] using hminimum_le h.length h.get
    exact (not_le_of_gt (lt_add_one b)) (hn.trans (hmin_n.trans (hmin_h.trans hh)))
  tfae_have 3 -> 1 := by
    intro hfinite omega
    refine tendsto_atTop.2 fun b => ?_
    let pathPrefix : ℕ -> List A := fun n => List.ofFn fun i : Fin n => omega i
    have hprefix_injective : Function.Injective pathPrefix := by
      intro m n hmn
      have := congrArg List.length hmn
      simpa [pathPrefix] using this
    have hbad : {n : ℕ | pathClock c (pathPrefix n) ≤ b}.Finite := by
      exact Set.Finite.preimage hprefix_injective.injOn (hfinite b)
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hbad.eventually_cofinite_notMem] with n hn
    exact le_of_not_ge hn
  tfae_finish

#print axioms finite_branching_path_clock_criterion

end D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
