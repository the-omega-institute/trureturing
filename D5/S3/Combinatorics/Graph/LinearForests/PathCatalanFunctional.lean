/- GID: D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse]
   utility: none
   digest: The Catalan functional is nonnegative on every finite path at every legal parameter. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Combinatorics.SimpleGraph.Hasse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset PowerSeries
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
namespace D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional

local instance : DecidableRel (SimpleGraph.hasse ℕ).Adj := Classical.decRel _

private lemma path_adj (u v : ℕ) :
    (SimpleGraph.hasse ℕ).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp [SimpleGraph.hasse_adj, ← Order.succ_eq_iff_covBy]

private def pathSeries (v : ℕ) : PowerSeries ℤ :=
  partition (SimpleGraph.hasse ℕ) (range v) (fun _ => -X)

private def C : PowerSeries ℤ := catalanSeries.map (Nat.castRingHom ℤ)

private lemma C_eq : C ^ 2 * X + 1 = C := by
  simpa [C] using congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    catalanSeries_sq_mul_X_add_one

private lemma path_zero : pathSeries 0 = 1 := by
  simp [pathSeries, partition_empty]

private lemma path_rec (v : ℕ) :
    pathSeries (v + 2) = pathSeries (v + 1) - X * pathSeries v := by
  have he : (range (v + 2)).erase (v + 1) = range (v + 1) := by
    ext x
    simp only [mem_erase, mem_range]
    omega
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1) =
      range v := by
    ext x
    simp only [closedComplement, mem_filter, mem_erase, mem_range, path_adj]
    omega
  simpa [pathSeries, he, hc, sub_eq_add_neg] using
    partition_delete (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1)
      (by simp) (fun _ => (-X : PowerSeries ℤ))

private lemma path_one : pathSeries 1 = 1 - X := by
  have he : (range 1).erase 0 = ∅ := by decide
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range 1) 0 = ∅ := by
    simp [closedComplement]
  have hh := partition_delete (SimpleGraph.hasse ℕ) (range 1) 0
    (by simp) (fun _ => (-X : PowerSeries ℤ))
  rw [he, hc, partition_empty] at hh
  simpa [pathSeries, partition_empty, sub_eq_add_neg] using hh

private lemma series_identity (v : ℕ) :
    pathSeries (v + 1) * C = pathSeries v + X ^ (v + 2) * C ^ (v + 3) := by
  have ce : X * C ^ 2 = C - 1 := by linear_combination C_eq
  induction v using Nat.twoStepInduction with
  | zero =>
    rw [path_one, path_zero]
    linear_combination (norm := ring_nf) -(1 + X * C) * C_eq
  | one =>
    rw [path_rec, path_one, path_zero]
    linear_combination (norm := ring_nf) -(1 - X + X * C + X ^ 2 * C ^ 2) * C_eq
  | more v ih₀ ih₁ =>
    rw [show v + 2 + 1 = (v + 1) + 2 by omega, path_rec, sub_mul, mul_assoc,
      show v + 1 + 1 = v + 2 by omega, ih₁, ih₀, path_rec]
    simp only [mul_add]
    have hh := congrArg (fun t : PowerSeries ℤ => X ^ (v + 3) * C ^ (v + 3) * t) ce
    simp only [pow_succ] at *
    linear_combination (norm := ring_nf) -hh

/-- The integer Catalan functional of the actual independent subsets of a finite domain. -/
def phi {α : Type*} [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (V : Finset α) (m : ℕ) : ℤ :=
  ∑ S ∈ configurations G V,
    (-1 : ℤ) ^ S.card * (catalan (m - S.card) : ℤ)

private lemma signed_power (k : ℕ) :
    (-X : PowerSeries ℤ) ^ k = PowerSeries.C ((-1 : ℤ) ^ k) * X ^ k := by
  rw [neg_eq_neg_one_mul, mul_pow]
  simp

private lemma configuration_card {v : ℕ} {S : Finset ℕ}
    (hS : S ∈ configurations (SimpleGraph.hasse ℕ) (range v)) : S.card ≤ v := by
  exact (Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)).trans
    (by simp)

private lemma coeff_phi (v m : ℕ) (hm : v ≤ m) :
    coeff m (pathSeries v * C) = phi (SimpleGraph.hasse ℕ) (range v) m := by
  unfold pathSeries partition phi
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hsm : S.card ≤ m := (configuration_card hS).trans hm
  rw [Finset.prod_const, signed_power, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', ite_eq_left hsm]
  simp [C]

private lemma coeff_path_zero (v m : ℕ) (hm : v < m) :
    coeff m (pathSeries v) = 0 := by
  unfold pathSeries partition
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hne : m ≠ S.card := by have := configuration_card hS; omega
  rw [Finset.prod_const, signed_power, coeff_C_mul, coeff_X_pow, ite_eq_right hne, mul_zero]

/-- All legal Catalan parameters, including the empty path and zero parameter. -/
theorem path_phi_nonnegative (v m : ℕ) (hm : v ≤ m) : 0 ≤ phi (SimpleGraph.hasse ℕ) (range v) m := by
  rw [← coeff_phi (SimpleGraph.hasse ℕ) (range v) m hm]
  cases v with
  | zero => simp [path_zero, C]
  | succ v =>
    rw [series_identity, map_add, coeff_path_zero v m (by omega), zero_add]
    have he : (X : PowerSeries ℤ) ^ (v + 2) * C ^ (v + 3) =
        PowerSeries.map (Nat.castRingHom ℤ)
          ((X : PowerSeries ℕ) ^ (v + 2) * catalanSeries ^ (v + 3)) := by
      simp [C]
    rw [he, coeff_map]
    exact Int.natCast_nonneg _

#print axioms path_phi_nonnegative
end D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
