/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual periodic-skeleton density is invariant under compatible rescaling. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeletonDensity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! If q divides h and the actual q-periodic coordinates equal the actual
h-periodic coordinates, normalized skeleton density is unchanged. The finite
count proof splits a complete h-interval into equal q-intervals.
Public escape registrations remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/24726. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeleton

private noncomputable def residueCount (P : ℤ → Prop) (p : ℕ) : ℕ := by
  classical
  exact ∑ j : Fin p, if P (j.val : ℤ) then 1 else 0

private theorem residueCount_mul (P : ℤ → Prop) (q m : ℕ)
    (hP : ∀ i k : ℤ, P (i + k * (q : ℤ)) ↔ P i) :
    residueCount P (m * q) = m * residueCount P q := by
  classical
  unfold residueCount
  rw [← (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)).sum_comp]
  simp only [Fintype.sum_prod_type]
  have hi (a : Fin m) (b : Fin q) :
      P (((finProdFinEquiv (a, b)).val : ℕ) : ℤ) ↔ P (b.val : ℤ) := by
    convert hP (b.val : ℤ) (a.val : ℤ) using 1 <;>
      simp [finProdFinEquiv, Nat.cast_add, Nat.cast_mul, mul_comm]
  simp_rw [hi]
  simp

private theorem normalized_residueCount_of_dvd (P : ℤ → Prop) (q h : ℕ)
    (hq : q ∣ h) (hqpos : 0 < q) (hhpos : 0 < h)
    (hP : ∀ i k : ℤ, P (i + k * (q : ℤ)) ↔ P i) :
    (residueCount P q : ℝ) / (q : ℝ) =
      (residueCount P h : ℝ) / (h : ℝ) := by
  obtain ⟨m, rfl⟩ := hq
  have hmpos : 0 < m := Nat.pos_of_mul_pos_left hhpos
  rw [Nat.mul_comm q m, residueCount_mul P q m hP]
  push_cast
  field_simp

private noncomputable def phaseCount (P : ℤ → Prop) (p : ℕ) [NeZero p] : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : ZMod p => P (j.val : ℤ))).card

private theorem phaseCount_eq (P : ℤ → Prop) (p : ℕ) [NeZero p] :
    phaseCount P p = residueCount P p := by
  classical
  cases p with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ p =>
    unfold phaseCount residueCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl

private theorem normalized_phaseCount_of_dvd (P : ℤ → Prop) (q h : ℕ)
    [NeZero q] [NeZero h] (hq : q ∣ h)
    (hP : ∀ i k : ℤ, P (i + k * (q : ℤ)) ↔ P i) :
    (phaseCount P q : ℝ) / (q : ℝ) =
      (phaseCount P h : ℝ) / (h : ℝ) := by
  simp only [phaseCount_eq]
  exact normalized_residueCount_of_dvd P q h hq (NeZero.pos q) (NeZero.pos h) hP

private theorem coordinate_period_density_of_dvd (y : ℤ → Bool) (q h : ℕ)
    [NeZero q] [NeZero h] (hq : q ∣ h)
    (hEq : ∀ i : ℤ,
      (∀ k : ℤ, y (i + k * (q : ℤ)) = y i) ↔
      (∀ k : ℤ, y (i + k * (h : ℤ)) = y i)) :
    (phaseCount (fun i => ∀ k : ℤ, y (i + k * (q : ℤ)) = y i) q : ℝ) / q =
    (phaseCount (fun i => ∀ k : ℤ, y (i + k * (h : ℤ)) = y i) h : ℝ) / h := by
  have hP : ∀ i k : ℤ,
      (∀ t : ℤ, y ((i + k * (q : ℤ)) + t * (q : ℤ)) = y (i + k * (q : ℤ))) ↔
      (∀ t : ℤ, y (i + t * (q : ℤ)) = y i) := by
    intro i k
    constructor
    · intro hp t
      have hb := hp (-k)
      have ht := hp (t - k)
      have hzero : i + k * (q : ℤ) + -k * (q : ℤ) = i := by ring
      have heq : i + k * (q : ℤ) + (t - k) * (q : ℤ) = i + t * (q : ℤ) := by ring
      rw [hzero] at hb
      rw [heq] at ht
      exact ht.trans hb.symm
    · intro hp t
      have hb := hp k
      have ht := hp (k + t)
      have heq : i + (k + t) * (q : ℤ) = i + k * (q : ℤ) + t * (q : ℤ) := by ring
      rw [heq] at ht
      exact ht.trans hb.symm
  have heq : (fun i => ∀ k : ℤ, y (i + k * (h : ℤ)) = y i) =
      (fun i => ∀ k : ℤ, y (i + k * (q : ℤ)) = y i) := by
    funext i
    exact propext (hEq i).symm
  rw [heq]
  exact normalized_phaseCount_of_dvd _ q h hq hP

/-- Divisible periods with the same actual periodic coordinates have the
same normalized periodic-skeleton density. All signed multiples are retained. -/
theorem density_eq_of_dvd_of_periodic_coordinates_eq (y : ℤ → Bool) (q h : ℕ)
    [NeZero q] [NeZero h] (hq : q ∣ h)
    (hEq : ∀ i : ℤ,
      (∀ k : ℤ, y (i + k * (q : ℤ)) = y i) ↔
      (∀ k : ℤ, y (i + k * (h : ℤ)) = y i)) :
    density y q = density y h := by
  exact coordinate_period_density_of_dvd y q h hq hEq

end D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeleton
