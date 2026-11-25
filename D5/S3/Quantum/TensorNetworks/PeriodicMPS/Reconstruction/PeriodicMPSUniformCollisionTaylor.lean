/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCollisionTaylor
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCollisionTaylor
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Normalized Taylor polynomial at the fourfold collision. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHermiteLiteralJet
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum

/-! The degree-seven normalized power at the fourfold transfer collision. -/

set_option autoImplicit false

namespace HorizontalKCollision

open Polynomial
open D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHermiteLiteralJet

noncomputable section

def taylor {R : Type*} [CommRing R] (m : ℕ) : R[X] :=
  ∑ s ∈ Finset.range 8, C (m.choose s : R) * (4 * X - 1)^s

theorem taylor_degree {R : Type*} [CommRing R] (m : ℕ) :
    (taylor (R := R) m).natDegree ≤ 7 := by
  apply natDegree_sum_le_of_forall_le
  intro s hs
  have hl : ((4 : R[X]) * X - 1).natDegree ≤ 1 := by
    have h : ((4 : R[X]) * X).natDegree ≤ 1 := by
      exact (natDegree_mul_le).trans (by simpa using (natDegree_X_le : (X : R[X]).natDegree ≤ 1))
    exact natDegree_sub_le_of_le (n := 1) h (by simp)
  have hp : (((4 : R[X]) * X - 1)^s).natDegree ≤ s := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left s hl)
  exact (natDegree_C_mul_le _ _).trans (hp.trans (by have := Finset.mem_range.mp hs; omega))

/-- The binomial tail is divisible by the square of the characteristic
polynomial of the fourfold collision. -/
theorem charpoly_sq_dvd_taylor_sub {F : Type*} [Field F] [CharZero F] (m : ℕ) :
    ((X - C (1/4 : F))^4)^2 ∣ (4 * X)^m - taylor (R := F) m := by
  let Y : F[X] := 4 * X - 1
  have hY : Y = C (4 : F) * (X - C (1/4 : F)) := by
    dsimp [Y]
    rw [mul_sub, ← C_mul]
    norm_num [map_ofNat]
  have hsum :
      (∑ s ∈ Finset.range (max 8 (m+1)), C (m.choose s : F) * Y^s) =
      (∑ s ∈ Finset.range (m+1), C (m.choose s : F) * Y^s) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (le_max_right 8 (m+1)))
    intro s _ hs
    have hlt : m < s := by simpa using hs
    simp [Nat.choose_eq_zero_of_lt hlt]
  have hbin : (4 * X : F[X])^m =
      ∑ s ∈ Finset.range (max 8 (m+1)), C (m.choose s : F) * Y^s := by
    rw [hsum]
    have h : Y + 1 = (4 * X : F[X]) := by simp [Y]
    rw [← h, add_pow]
    apply Finset.sum_congr rfl
    intro s hs
    simp [mul_comm]
  rw [hbin, taylor, ← pow_mul]
  change (X - C (1/4 : F))^8 ∣
    (∑ s ∈ Finset.range (max 8 (m+1)), C (m.choose s : F) * Y^s) -
    ∑ s ∈ Finset.range 8, C (m.choose s : F) * Y^s
  rw [← Finset.sum_sdiff (Finset.range_mono (le_max_left 8 (m+1))), add_sub_cancel_right]
  apply Finset.dvd_sum
  intro s hs
  have h8 : 8 ≤ s := by simpa using (Finset.mem_sdiff.mp hs).2
  apply dvd_mul_of_dvd_right
  rw [hY, mul_pow]
  exact dvd_mul_of_dvd_right (pow_dvd_pow _ h8) _

/-- Equality on arbitrary ambient dual lifts, including defective transfers. -/
theorem taylor_ambient_jet {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    [DecidableEq ι] (T J : Matrix ι ι F)
    (hχ : T.charpoly = (X - C (1/4 : F))^4) (m : ℕ) :
    aeval (perturbation T J) (taylor (R := F) m) =
      aeval (perturbation T J) ((4 * X)^m : F[X]) := by
  have h := charpoly_sq_dvd_taylor_sub (F := F) m
  rw [← hχ] at h
  obtain ⟨q, hq⟩ := h
  have hz : aeval (perturbation T J) ((4 * X)^m : F[X]) -
      aeval (perturbation T J) (taylor (R := F) m) = 0 := by
    rw [← map_sub, hq, map_mul, aeval_charpoly_sq_perturbation, zero_mul]
  exact (sub_eq_zero.mp hz).symm

end

end HorizontalKCollision
