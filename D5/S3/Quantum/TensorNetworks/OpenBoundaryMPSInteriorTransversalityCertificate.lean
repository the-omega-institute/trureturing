/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.Field.ZMod]
   utility: none
   digest: Division-free integer recurrence certificate for all positive exterior lengths. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Integer numerators for the fixed-target transversality slopes. Their
nonzero mod-5 product is consumed by the native real derivative proof. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate

def lu : ℕ → Fin 3 → ℤ
  | 0 => ![1, 0, -1]
  | n + 1 => ![3 * lu n 0 - 2 * lu n 1, 5 * lu n 2, -2 * lu n 0 + 3 * lu n 1]
def lv : ℕ → Fin 3 → ℤ
  | 0 => ![1, 0, 1]
  | n + 1 => ![3 * lv n 0 + 2 * lv n 1, lv n 2, 2 * lv n 0 + 3 * lv n 1]
def rx : ℕ → Fin 3 → ℤ
  | 0 => ![0, 1, 0]
  | n + 1 => ![3 * rx n 0 - 2 * rx n 1, 5 * rx n 2, -2 * rx n 0 + 3 * rx n 1]
def ry : ℕ → Fin 3 → ℤ
  | 0 => ![1, 0, 0]
  | n + 1 => ![3 * ry n 0 + 2 * ry n 2, 2 * ry n 0 + 3 * ry n 2, ry n 1]

def U : ℕ → ℤ
  | 0 => 0
  | n + 1 => 5 * U n + 2 * (lu (n+1) 0 * lv (n+1) 1 + lu (n+1) 1 * lv (n+1) 0)
def V : ℕ → ℤ
  | 0 => 0
  | n + 1 => 5 * V n + 2 * (-1) ^ (n+2) *
      (rx (n+1) 0 + 5^(n+1) * ry (n+2) 2)

private lemma lu_mod (n : ℕ) (i : Fin 3) :
    (lu (n+1) i : ZMod 5) = 3^(n+1) * (![1,0,1] : Fin 3 → ZMod 5) i := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  induction n generalizing i with
  | zero => fin_cases i <;> norm_num [lu] <;> decide
  | succ n ih =>
      rw [lu]
      fin_cases i <;>
        simp only [ Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, pow_succ]
      all_goals norm_num only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
        Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      all_goals try simp only [Nat.add_comm 1 n, ih]
      all_goals ring_nf
      all_goals simp [show (5 : ZMod 5) = 0 by decide,
        show (6 : ZMod 5) = 1 by decide,
        show (9 : ZMod 5) = 4 by decide,
        show (15 : ZMod 5) = 0 by decide,
        show (-6 : ZMod 5) = 4 by decide]
      all_goals linear_combination -(3^n) * h5

private lemma lv_mod (n : ℕ) (i : Fin 3) :
    (lv (n+1) i : ZMod 5) = 2^n * (![3,1,2] : Fin 3 → ZMod 5) i := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  induction n generalizing i with
  | zero => fin_cases i <;> norm_num [lv] <;> decide
  | succ n ih =>
      rw [lv]
      fin_cases i <;>
        simp only [ Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, pow_succ]
      all_goals norm_num only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
        Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      all_goals try simp only [Nat.add_comm 1 n, ih]
      all_goals ring_nf
      all_goals simp [show (5 : ZMod 5) = 0 by decide,
        show (6 : ZMod 5) = 1 by decide,
        show (9 : ZMod 5) = 4 by decide,
        show (15 : ZMod 5) = 0 by decide,
        show (-6 : ZMod 5) = 4 by decide]
      · linear_combination 2 * (2^n) * h5
      · ring
      · linear_combination (2^n) * h5

private lemma rx_mod (n : ℕ) (i : Fin 3) :
    (rx (n+1) i : ZMod 5) = 3^(n+1) * (![1,0,1] : Fin 3 → ZMod 5) i := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  induction n generalizing i with
  | zero => fin_cases i <;> norm_num [rx] <;> decide
  | succ n ih =>
      rw [rx]
      fin_cases i <;>
        simp only [ Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, pow_succ]
      all_goals norm_num only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
        Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      all_goals try simp only [Nat.add_comm 1 n, ih]
      all_goals ring_nf
      all_goals simp [show (5 : ZMod 5) = 0 by decide,
        show (6 : ZMod 5) = 1 by decide,
        show (9 : ZMod 5) = 4 by decide,
        show (15 : ZMod 5) = 0 by decide,
        show (-6 : ZMod 5) = 4 by decide]
      all_goals linear_combination -(3^n) * h5

private lemma U_mod (n : ℕ) : (U (n+1) : ZMod 5) = 1 := by
  simp only [U, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  rw [lu_mod, lu_mod, lv_mod, lv_mod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, mul_zero, add_zero,
    mul_one, show (5 : ZMod 5) = 0 by decide]
  have he : (3 : ZMod 5)^(n+1) * 2^n = 3 := by
    calc
      _ = 3 * ((3 : ZMod 5) * 2)^n := by rw [mul_pow, pow_succ]; ring
      _ = 3 := by rw [show (3 : ZMod 5) * 2 = 1 by decide]; simp
  rw [he]
  decide

private lemma V_mod (n : ℕ) :
    (V (n+1) : ZMod 5) = 2 * (-1)^(n+2) * 3^(n+1) := by
  simp only [V, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat]
  rw [rx_mod]
  simp only [Matrix.cons_val_zero, mul_one, show (5 : ZMod 5) = 0 by decide,
    zero_pow (by omega : n+1 ≠ 0), zero_mul, add_zero, zero_add]

theorem certificate_nonzero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    U p ≠ 0 ∧ V q ≠ 0 ∧
      ((U p * V q : ℤ) : ZMod 5) = 2 * (-1)^(q+1) * 3^q := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hu := U_mod n
  have hv := V_mod m
  have hvn : (V (m+1) : ZMod 5) ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ (by decide)))
      (pow_ne_zero _ (by decide))
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he : (0 : ZMod 5) = 1 := by simpa only [h, Int.cast_zero] using hu
    exact zero_ne_one he
  · intro h
    exact hvn (by simp [h])
  · simpa only [Int.cast_mul, hu, one_mul] using hv


end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
