/- GID: D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.claim; result=D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result; claim=D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.claim
   digest: Two enzyme routes refute the waiting-time randomness and skewness ordering. -/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation

open scoped BigOperators Matrix

/-- Row-source generator with the marked product release sent to a cemetery. -/
noncomputable def cemetery {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then -(∑ l, if i = l then 0 else k i l)
    else if i = p ∧ j = r then 0 else k i j

/-- First-passage moments, using the preregistered linear-system characterization. -/
noncomputable def moment {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) :
    ℕ → Fin m → ℝ :=
  Nat.rec (fun _ => 1)
    (fun n v => ((n + 1 : ℕ) : ℝ) • ((-(cemetery k p r))⁻¹ *ᵥ v))

noncomputable def variance {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) : ℝ :=
  moment k p r 2 r - (moment k p r 1 r)^2

noncomputable def randomness {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) : ℝ :=
  variance k p r / (moment k p r 1 r)^2

noncomputable def skewness {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) : ℝ :=
  (moment k p r 3 r - 3 * moment k p r 1 r * variance k p r -
    (moment k p r 1 r)^3) / (Real.sqrt (variance k p r))^3

def IsNetwork {m : ℕ} (k : Fin m → Fin m → ℝ) (p r : Fin m) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ k i j) ∧ 0 < k p r ∧
    ∀ i, Relation.ReflTransGen (fun i j => 0 < k i j) i p

def claim : Prop :=
  ∀ (m : ℕ) (k : Fin m → Fin m → ℝ) (p r : Fin m),
    IsNetwork k p r → 0 < variance k p r → skewness k p r ≤ 2 → randomness k p r ≤ 1

private noncomputable def rates : Fin 8 → Fin 8 → ℝ :=
  !![0, 75, 25, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 25;
     0, 0, 0, 5, 0, 0, 0, 0;
     0, 0, 0, 0, 5, 0, 0, 0;
     0, 0, 0, 0, 0, 5, 0, 0;
     0, 0, 0, 0, 0, 0, 5, 0;
     0, 0, 0, 0, 0, 0, 0, 5;
     25, 0, 0, 0, 0, 0, 0, 0]

private noncomputable def a : Matrix (Fin 8) (Fin 8) ℝ :=
  !![100, -75, -25, 0, 0, 0, 0, 0;
     0, 25, 0, 0, 0, 0, 0, -25;
     0, 0, 5, -5, 0, 0, 0, 0;
     0, 0, 0, 5, -5, 0, 0, 0;
     0, 0, 0, 0, 5, -5, 0, 0;
     0, 0, 0, 0, 0, 5, -5, 0;
     0, 0, 0, 0, 0, 0, 5, -5;
     0, 0, 0, 0, 0, 0, 0, 25]

private noncomputable def v1 : Fin 8 → ℝ :=
  ![33/100, 2/25, 26/25, 21/25, 16/25, 11/25, 6/25, 1/25]

private noncomputable def v2 : Fin 8 → ℝ :=
  ![1673/5000, 6/625, 802/625, 542/625, 332/625, 172/625, 62/625, 2/625]

private noncomputable def v3 : Fin 8 → ℝ :=
  ![234843/500000, 24/15625, 28656/15625, 16626/15625,
    8496/15625, 3516/15625, 936/15625, 6/15625]

private theorem network : IsNetwork rates 7 0 := by
  sorry

private theorem cemetery_eq : -(cemetery rates 7 0) = a := by
  sorry

private theorem determinant_unit : IsUnit a.det := by
  sorry

private theorem moment_step (n : ℕ) (v : Fin 8 → ℝ)
    (h : a *ᵥ v = ((n + 1 : ℕ) : ℝ) • moment rates 7 0 n) :
    moment rates 7 0 (n + 1) = v := by
  sorry

private theorem first_moment : moment rates 7 0 1 = v1 := by
  apply moment_step 0
  sorry

private theorem second_moment : moment rates 7 0 2 = v2 := by
  apply moment_step 1
  rw [first_moment]
  sorry

private theorem third_moment : moment rates 7 0 3 = v3 := by
  apply moment_step 2
  rw [second_moment]
  sorry

private theorem moment_values :
    moment rates 7 0 1 0 = 33/100 ∧ moment rates 7 0 2 0 = 1673/5000 ∧
      moment rates 7 0 3 0 = 234843/500000 := by
  rw [first_moment, second_moment, third_moment]
  sorry

private theorem variance_value : variance rates 7 0 = 2257/10000 := by
  sorry

private theorem randomness_gt : 1 < randomness rates 7 0 := by
  sorry

private theorem skewness_le : skewness rates 7 0 ≤ 2 := by
  sorry

theorem result : ¬ claim := by
  intro h
  have hv : 0 < variance rates 7 0 := by rw [variance_value]; norm_num
  exact (not_le_of_gt randomness_gt) (h 8 rates 7 0 network hv skewness_le)

end D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation
