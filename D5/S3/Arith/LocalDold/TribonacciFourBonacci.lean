/- GID: D5/S3/Arith/LocalDold/TribonacciFourBonacci
   generality: I
   mirror-B: D5/B/S3/Arith/LocalDold/TribonacciFourBonacci
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The printed Tribonacci and four-Bonacci sequences have no local-Dold good prime. -/

import D5.S3.Arith.LocalDold.UnimodularObstruction
import D5.S1.Recurrence.FiniteCompanionCyclicModule
import D5.S0.Tower.Tribonacci.Names
import D5.S0.Tower.Tribonacci.Values

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LocalDold.TribonacciFourBonacci

open D5.S3.Arith.LocalDold.UnimodularObstruction
open D5.S1.Recurrence.FiniteCompanionCyclicModule
open D5.S0.Tower.Tribonacci.Names

open scoped ArithmeticFunction.Moebius

noncomputable section

def dold (p : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (n : ℤ) ∣ ∑ d ∈ n.divisors, (μ (n / d)) * (pPart p (a d) : ℤ)

def goodPrimes (a : ℕ → ℕ) : Set ℕ := {p | p.Prime ∧ dold p a}

private def matrixGLOfLinearEquiv {d : ℕ}
    (e : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ)) : GLInt d :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

private theorem matrixGLOfLinearEquiv_action {d : ℕ}
    (e : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ)) (x : Fin d → ℤ) :
    ((matrixGLOfLinearEquiv e).val.mulVec x) = e x := by
  change (LinearMap.toMatrix' e.toLinearMap).mulVec x = e x
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

/- The source's four-Bonacci sequence starts with `1,1,1,2`; its value at
   index zero is kept as a neutral natural placeholder, while the inverse
   companion state uses the modeling extension `B₀ = -1`. -/
def fourBonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | n + 5 =>
      fourBonacci (n + 4) + fourBonacci (n + 3) +
        fourBonacci (n + 2) + fourBonacci (n + 1)

private theorem fourBonacci_pos (n : ℕ) (hn : 0 < n) : 0 < fourBonacci n := by
  cases n with
  | zero => omega
  | succ n =>
      induction n using Nat.strong_induction_on with
      | h n ih =>
          rcases n with _ | _ | _ | _ | n
          · norm_num [fourBonacci]
          · norm_num [fourBonacci]
          · norm_num [fourBonacci]
          · norm_num [fourBonacci]
          · simp only [fourBonacci]
            have h4 : 0 < fourBonacci (n + 4) := by
              simpa [Nat.add_assoc] using ih (n + 3) (by omega)
            omega

private theorem fourBonacci_add_four (n : ℕ) (hn : 0 < n) :
    fourBonacci (n + 4) =
      fourBonacci (n + 3) + fourBonacci (n + 2) +
        fourBonacci (n + 1) + fourBonacci n := by
  rcases n with _ | n
  · omega
  · change fourBonacci (n + 5) =
      fourBonacci (n + 4) + fourBonacci (n + 3) +
        fourBonacci (n + 2) + fourBonacci (n + 1)
    rfl

private theorem time_3_apply (x : Fin 3 → ℤ) :
    time 1 3 (by decide) x = ![x 0 + x 1 + x 2, x 0, x 1] := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [time, D5.S1.Recurrence.FiniteCompanionSquareDefect.time,
      Fin.sum_univ_succ, add_assoc]
  · fin_cases j <;> rfl

private theorem time_4_apply (x : Fin 4 → ℤ) :
    time 1 4 (by decide) x = ![x 0 + x 1 + x 2 + x 3, x 0, x 1, x 2] := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [time, D5.S1.Recurrence.FiniteCompanionSquareDefect.time,
      Fin.sum_univ_succ, add_assoc]
  · fin_cases j <;> rfl

private def tribonacciTime : (Fin 3 → ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun := time 1 3 (by decide)
  invFun := fun y => ![y 1, y 2, y 0 - y 1 - y 2]
  left_inv := by
    intro x
    rw [time_3_apply]
    ext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro y
    rw [time_3_apply]
    ext i
    fin_cases i <;> simp <;> ring
  map_add' := (time (1 : ℤ) 3 (by decide)).map_add
  map_smul' := (time (1 : ℤ) 3 (by decide)).map_smul

private def fourBonacciTime : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun := time 1 4 (by decide)
  invFun := fun y => ![y 1, y 2, y 3, y 0 - y 1 - y 2 - y 3]
  left_inv := by
    intro x
    rw [time_4_apply]
    ext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro y
    rw [time_4_apply]
    ext i
    fin_cases i <;> simp <;> ring
  map_add' := (time (1 : ℤ) 4 (by decide)).map_add
  map_smul' := (time (1 : ℤ) 4 (by decide)).map_smul

private def tribonacciMatrix : GLInt 3 := matrixGLOfLinearEquiv tribonacciTime
private def fourBonacciMatrix : GLInt 4 := matrixGLOfLinearEquiv fourBonacciTime

private def tribonacciState : Fin 3 → ℤ := ![1, 1, 0]
private def fourBonacciState : Fin 4 → ℤ := ![1, 1, 1, -1]

private def tribonacciStateAt (n : ℕ) : Fin 3 → ℤ :=
  ![tribonacci (n + 2), tribonacci (n + 1), tribonacci n]

private def fourBonacciStateAt (n : ℕ) : Fin 4 → ℤ :=
  ![fourBonacci (n + 3), fourBonacci (n + 2),
    fourBonacci (n + 1), fourBonacci n]

private theorem tribonacci_time_state (n : ℕ) (hn : 0 < n) :
    tribonacciTime (tribonacciStateAt n) = tribonacciStateAt (n + 1) := by
  change time 1 3 (by decide) (tribonacciStateAt n) = _
  rw [time_3_apply]
  ext i
  fin_cases i
  · simp [tribonacciStateAt]
    rw [show n + 1 + 2 = n + 3 by omega, tribonacci_add_three]
    push_cast
    ring
  · simp [tribonacciStateAt, Nat.add_assoc]
  · simp [tribonacciStateAt, Nat.add_assoc]

private theorem fourBonacci_time_state (n : ℕ) (hn : 0 < n) :
    fourBonacciTime (fourBonacciStateAt n) = fourBonacciStateAt (n + 1) := by
  change time 1 4 (by decide) (fourBonacciStateAt n) = _
  rw [time_4_apply]
  ext i
  fin_cases i
  · simp [fourBonacciStateAt]
    rw [show n + 1 + 3 = n + 4 by omega, fourBonacci_add_four n hn]
    push_cast
    ring
  · simp [fourBonacciStateAt, Nat.add_assoc]
  · simp [fourBonacciStateAt, Nat.add_assoc]
  · simp [fourBonacciStateAt, Nat.add_assoc]

private theorem tribonacci_matrix_power_state : ∀ n, 0 < n →
    (tribonacciMatrix.val ^ n).mulVec tribonacciState = tribonacciStateAt n
  | 0, hn => by omega
  | 1, hn => by
      rw [pow_one]
      change (matrixGLOfLinearEquiv tribonacciTime).val.mulVec tribonacciState = _
      rw [matrixGLOfLinearEquiv_action]
      change time 1 3 (by decide) tribonacciState = _
      rw [time_3_apply]
      norm_num [tribonacciState, tribonacciStateAt, tribonacci]
  | n + 2, hn => by
      have ih := tribonacci_matrix_power_state (n + 1) (by omega)
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      change (matrixGLOfLinearEquiv tribonacciTime).val.mulVec _ = _
      rw [matrixGLOfLinearEquiv_action]
      exact tribonacci_time_state (n + 1) (by omega)

private theorem fourBonacci_matrix_power_state : ∀ n, 0 < n →
    (fourBonacciMatrix.val ^ n).mulVec fourBonacciState = fourBonacciStateAt n
  | 0, hn => by omega
  | 1, hn => by
      rw [pow_one]
      change (matrixGLOfLinearEquiv fourBonacciTime).val.mulVec fourBonacciState = _
      rw [matrixGLOfLinearEquiv_action]
      change time 1 4 (by decide) fourBonacciState = _
      rw [time_4_apply]
      norm_num [fourBonacciState, fourBonacciStateAt, fourBonacci]
  | n + 2, hn => by
      have ih := fourBonacci_matrix_power_state (n + 1) (by omega)
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      change (matrixGLOfLinearEquiv fourBonacciTime).val.mulVec _ = _
      rw [matrixGLOfLinearEquiv_action]
      exact fourBonacci_time_state (n + 1) (by omega)

private theorem tribonacci_state_inverse :
    ((tribonacciMatrix⁻¹).val.mulVec tribonacciState) = ![1, 0, 0] := by
  rw [show (tribonacciMatrix⁻¹).val = tribonacciTime.symm.toLinearMap.toMatrix' by
    rfl, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  ext i
  fin_cases i <;> simp [tribonacciMatrix, tribonacciState, tribonacciTime, time,
    D5.S1.Recurrence.FiniteCompanionSquareDefect.time, Fin.cons, Fin.cases, Fin.sum_univ_succ] <;> ring

private theorem fourBonacci_state_inverse :
    ((fourBonacciMatrix⁻¹).val.mulVec fourBonacciState) = ![1, 1, -1, 0] := by
  rw [show (fourBonacciMatrix⁻¹).val = fourBonacciTime.symm.toLinearMap.toMatrix' by
    rfl, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  ext i
  fin_cases i <;> simp [fourBonacciMatrix, fourBonacciState, fourBonacciTime, time,
    D5.S1.Recurrence.FiniteCompanionSquareDefect.time, Fin.cons, Fin.cases, Fin.sum_univ_succ] <;> ring

private theorem tribonacci_coordinate (n : ℕ) (hn : 0 < n) :
    (tribonacci n : ℤ) =
      ((tribonacciMatrix.val ^ n).mulVec tribonacciState) (2 : Fin 3) := by
  rw [tribonacci_matrix_power_state n hn]
  simp [tribonacciStateAt]

private theorem fourBonacci_coordinate (n : ℕ) (hn : 0 < n) :
    (fourBonacci n : ℤ) =
      ((fourBonacciMatrix.val ^ n).mulVec fourBonacciState) (3 : Fin 4) := by
  rw [fourBonacci_matrix_power_state n hn]
  simp [fourBonacciStateAt]

private theorem tribonacci_pos (n : ℕ) (hn : 0 < n) : 0 < tribonacci n := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => norm_num [tribonacci]
      | succ n =>
          simpa [Nat.add_assoc] using
            D5.S0.Tower.Tribonacci.Values.tribonacci_level_pos n

private theorem tribonacci_one : tribonacci 1 = 1 := by
  norm_num [tribonacci]

private theorem fourBonacci_one : fourBonacci 1 = 1 := by
  rfl

theorem result (a : ℕ → ℕ) (ha : a = tribonacci ∨ a = fourBonacci) :
    goodPrimes a = ∅ ∧
    ∀ p : ℕ, p.Prime → ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) := by
  have hw : ∀ p : ℕ, p.Prime → ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) := by
    rcases ha with rfl | rfl
    · intro p hp
      exact unimodular_coordinate_obstruction tribonacciMatrix tribonacciState (2 : Fin 3)
        (by simpa using congrFun tribonacci_state_inverse (2 : Fin 3))
        tribonacci tribonacci_coordinate tribonacci_pos tribonacci_one p hp
    · intro p hp
      exact unimodular_coordinate_obstruction fourBonacciMatrix fourBonacciState (3 : Fin 4)
        (by simpa using congrFun fourBonacci_state_inverse (3 : Fin 4))
        fourBonacci fourBonacci_coordinate fourBonacci_pos fourBonacci_one p hp
  refine ⟨Set.eq_empty_iff_forall_notMem.mpr ?_, hw⟩
  intro p hp
  obtain ⟨q, hq0, hq, hpos, hlt, hnd⟩ := hw p hp.1 0
  exact hnd (hp.2 q (by omega))

end
end D5.S3.Arith.LocalDold.TribonacciFourBonacci
