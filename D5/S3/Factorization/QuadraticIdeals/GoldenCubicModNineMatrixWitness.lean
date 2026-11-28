/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicModNineMatrixWitness
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The Cayley-Hamilton sixth power detects a nontrivial mod-nine congruence direction. -/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicModNineMatrixWitness

abbrev M9 := Matrix (Fin 2) (Fin 2) (ZMod 9)
abbrev M3 := Matrix (Fin 2) (Fin 2) (ZMod 3)

def reduceNine : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)

/-- The two-by-two Cayley–Hamilton equation over the actual nonfield ring. -/
theorem cayley_sq (A : M9) : A^2 = A.trace • A - A.det • (1:M9) := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem cayley_cube (A : M9) (hd : A.det = 1) :
    A^3 = (A.trace^2-1) • A - A.trace • (1:M9) := by
  have h := cayley_sq A
  calc
    A^3 = (A.trace • A - (1:M9)) * A := by
      rw [pow_succ, h, hd, one_smul]
    _ = A.trace • A^2 - A := by rw [sub_mul, smul_mul_assoc, one_mul, pow_two]
    _ = _ := by
      rw [h, hd, one_smul, smul_sub, smul_smul, sub_smul]
      simp only [← pow_two, one_smul]
      abel

private theorem square_affine (A : M9) (s t : ZMod 9) :
    (s • A - t • (1:M9))^2 =
      s^2 • A^2 - (2*s*t) • A + t^2 • (1:M9) := by
  rw [pow_two, pow_two, sub_mul, mul_sub, mul_sub,
    smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    one_mul, mul_one, mul_one, ← pow_two, ← pow_two]
  rw [show (2*s*t : ZMod 9) = s*t+t*s by ring, add_smul]
  simp only [← pow_two]
  abel

theorem sixth_formula (A : M9) (hd : A.det=1) (ht : A.trace=4 ∨ A.trace=5) :
    A^6 = (if A.trace=4 then (6:ZMod 9) else 3) • A + (7:ZMod 9) • (1:M9) := by
  have hc := cayley_cube A hd
  change A^(3*2) = _
  rw [pow_mul, hc, square_affine]
  rcases ht with ht|ht
  · rw [ht, ite_eq_left rfl, show ((4:ZMod 9)^2-1)=6 by decide,
      show (6:ZMod 9)^2=0 by decide, show (2:ZMod 9)*6*4=3 by decide,
      show (4:ZMod 9)^2=7 by decide, zero_smul, zero_sub, ← neg_smul,
      show -(3:ZMod 9)=6 by decide]
  · rw [ht, ite_eq_right (by decide : (5:ZMod 9) ≠ 4),
      show ((5:ZMod 9)^2-1)=6 by decide,
      show (6:ZMod 9)^2=0 by decide, show (2:ZMod 9)*6*5=6 by decide,
      show (5:ZMod 9)^2=7 by decide, zero_smul, zero_sub, ← neg_smul,
      show -(6:ZMod 9)=3 by decide]

private theorem annihilated_products (k : ZMod 9) (hk : k=6 ∨ k=3) :
    ∀ x y : ZMod 9, k*x=0 → k*y=0 → x*y=0 := by
  rcases hk with hk|hk <;> rw [hk] <;> decide

private theorem vecDiscriminant (A : M9) :
    A.trace^2 - 4*A.det = (A 0 0-A 1 1)^2 + 4*A 0 1*A 1 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

theorem sixth_not_identity (A : M9) (hd : A.det=1) (ht : A.trace=4 ∨ A.trace=5) :
    A^6 ≠ 1 := by
  intro hid
  have he := sixth_formula A hd ht
  rw [hid] at he
  let k : ZMod 9 := if A.trace=4 then 6 else 3
  change (1:M9) = k • A + (7:ZMod 9) • (1:M9) at he
  have hk : k=6 ∨ k=3 := by unfold k; split <;> simp
  have e00 := congrFun (congrFun he 0) 0
  have e01 := congrFun (congrFun he 0) 1
  have e10 := congrFun (congrFun he 1) 0
  have e11 := congrFun (congrFun he 1) 1
  simp at e00 e01 e10 e11
  have hdiff : k*(A 0 0-A 1 1) = 0 := by linear_combination e11 - e00
  have h₁ := annihilated_products k hk _ _ hdiff hdiff
  have h₂ := annihilated_products k hk _ _ e01.symm e10.symm
  have hz : A.trace^2 - 4*A.det = 0 := by
    rw [vecDiscriminant, pow_two, h₁, mul_assoc, h₂, mul_zero, add_zero]
  rw [hd] at hz
  rcases ht with ht|ht
  · rw [ht] at hz
    exact (by decide : (4:ZMod 9)^2-4*1 ≠ 0) hz
  · rw [ht] at hz
    exact (by decide : (5:ZMod 9)^2-4*1 ≠ 0) hz

theorem sixth_reduces_to_identity (A : M9) (hd : A.det=1) (ht : A.trace=4 ∨ A.trace=5) :
    (A^6).map reduceNine = (1:M3) := by
  rw [sixth_formula A hd ht]
  let k : ZMod 9 := if A.trace=4 then 6 else 3
  change (k • A + (7:ZMod 9) • (1:M9)).map reduceNine = (1:M3)
  have hk : reduceNine k = 0 := by unfold k; split <;> decide
  have h7 : reduceNine 7=1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, hk, h7]

def companionNine (t : ZMod 9) : M9 := !![0,-1;1,t]

theorem companion_four_sixth :
    companionNine 4 ^ 6 = (!![7,3;6,4] : M9) := by
  rw [sixth_formula _ (by simp [companionNine, Matrix.det_fin_two_of])
    (Or.inl (by simp [companionNine, Matrix.trace_fin_two_of]))]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem companion_five_sixth :
    companionNine 5 ^ 6 = (!![7,6;3,4] : M9) := by
  rw [sixth_formula _ (by simp [companionNine, Matrix.det_fin_two_of])
    (Or.inr (by simp [companionNine, Matrix.trace_fin_two_of]))]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicModNineMatrixWitness
