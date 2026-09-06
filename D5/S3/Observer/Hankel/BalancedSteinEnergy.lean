/- GID: D5/S3/Observer/Hankel/BalancedSteinEnergy
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/BalancedSteinEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A diagonal reachability Stein inequality yields an inverse-storage input-energy inequality. -/

import D5.S3.Observer.Hankel.ProjectedRealizationError
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin

/- The two Stein hypotheses below are quadratic-form versions of
   A^T D A + C^T C <= D and A D A^T + B B^T <= D.
   Inverse-storage dissipativity is derived by weighted Young duality.
   In particular it is not placed in the definition of balanced data.
   All energies use sums of coordinate squares, not the default Pi sup norm. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.BalancedSteinEnergy

open D5.S3.Observer.Hankel.ProjectedRealizationError
open scoped BigOperators

variable {ι κ η : Type} [Fintype ι] [Fintype κ] [Fintype η]

/-- The quadratic form of a real diagonal matrix. -/
def energy (w x : ι → ℝ) : ℝ := ∑ i, w i * (x i) ^ 2

/-- Euclidean squared size, deliberately independent of the Pi sup norm. -/
def squareSum (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The ordinary matrix action as a continuous linear map on finite coordinates. -/
def matrixMap (M : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecBilin ℝ ℝ M)

@[simp] theorem matrixMap_apply (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    matrixMap M x = M.mulVec x := rfl

/-- Matrix coordinates of the existing zero-initial forced-state constructor. -/
def matrixState (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (u : ℕ → κ → ℝ) : ℕ → ι → ℝ :=
  drivenState (matrixMap A) (matrixMap B) u

/-- The output of the actual matrix state recurrence. -/
def matrixResponse (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix η ι ℝ) (u : ℕ → κ → ℝ) (k : ℕ) : η → ℝ :=
  C.mulVec (matrixState A B u k)

@[simp] theorem matrixState_zero (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (u : ℕ → κ → ℝ) : matrixState A B u 0 = 0 := rfl

@[simp] theorem matrixState_succ (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (u : ℕ → κ → ℝ) (k : ℕ) :
    matrixState A B u (k + 1) = A.mulVec (matrixState A B u k) + B.mulVec (u k) := rfl

/-- A diagonal observability Stein inequality, tested on every state. -/
def ObservabilityStein (w : ι → ℝ) (A : Matrix ι ι ℝ) (C : Matrix η ι ℝ) : Prop :=
  ∀ x, energy w (A.mulVec x) + squareSum (C.mulVec x) ≤ energy w x

/-- A diagonal reachability Stein inequality, tested on every dual state. -/
def ReachabilityStein (w : ι → ℝ) (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) : Prop :=
  ∀ z, energy w (A.transpose.mulVec z) + squareSum (B.transpose.mulVec z) ≤ energy w z

/-- Positive common diagonal storage for both discrete-time Stein inequalities. -/
def BalancedStein (w : ι → ℝ) (A : Matrix ι ι ℝ)
    (B : Matrix ι κ ℝ) (C : Matrix η ι ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ObservabilityStein w A C ∧ ReachabilityStein w A B

@[simp] theorem energy_zero (w : ι → ℝ) : energy w 0 = 0 := by
  simp [energy]

@[simp] theorem squareSum_zero : squareSum (0 : ι → ℝ) = 0 := by
  simp [squareSum]

theorem energy_nonneg (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ energy w x := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg (x i))

theorem squareSum_nonneg (x : ι → ℝ) : 0 ≤ squareSum x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Scalar multiplication has its usual Euclidean energy scaling. -/
theorem squareSum_smul (a : ℝ) (x : ι → ℝ) :
    squareSum (a • x) = a ^ 2 * squareSum x := by
  simp only [squareSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem weighted_young_scalar (w a b : ℝ) (hw : 0 < w) :
    2 * a * b ≤ w * a ^ 2 + w⁻¹ * b ^ 2 := by
  apply (mul_le_mul_iff_right₀ hw).mp
  calc
    (2 * a * b) * w ≤ (w * a) ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (w * a - b)]
    _ = (w * a ^ 2 + w⁻¹ * b ^ 2) * w := by
      field_simp [ne_of_gt hw]
      <;> ring

private theorem weighted_young (w a b : ι → ℝ) (hw : ∀ i, 0 < w i) :
    2 * (∑ i, a i * b i) ≤ energy w a + energy (fun i => (w i)⁻¹) b := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => weighted_young_scalar (w i) (a i) (b i) (hw i))
  simpa only [energy, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using h

private theorem transpose_pairing (M : Matrix ι κ ℝ) (z : ι → ℝ) (x : κ → ℝ) :
    (∑ i, z i * (M.mulVec x) i) = ∑ j, (M.transpose.mulVec z) j * x j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The reachability Stein inequality controls actual forced next-state energy
in the inverse diagonal metric. No inverse-energy or gain premise is assumed. -/
theorem inverse_energy_step (w : ι → ℝ) (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hw : ∀ i, 0 < w i) (hR : ReachabilityStein w A B)
    (x : ι → ℝ) (u : κ → ℝ) :
    energy (fun i => (w i)⁻¹) (A.mulVec x + B.mulVec u) ≤
      energy (fun i => (w i)⁻¹) x + squareSum u := by
  let t := A.mulVec x + B.mulVec u
  let z : ι → ℝ := fun i => (w i)⁻¹ * t i
  have hz : energy w z = energy (fun i => (w i)⁻¹) t := by
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [z]
    field_simp [ne_of_gt (hw i)]
    <;> ring
  have ht : (∑ i, z i * t i) = energy (fun i => (w i)⁻¹) t := by
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [z]
    ring
  have hp : (∑ i, z i * t i) =
      (∑ i, (A.transpose.mulVec z) i * x i) +
        ∑ j, (B.transpose.mulVec z) j * u j := by
    dsimp only [t]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [transpose_pairing, transpose_pairing]
  have ha := weighted_young w (A.transpose.mulVec z) x hw
  have hb := weighted_young (fun _ : κ => (1 : ℝ)) (B.transpose.mulVec z) u
    (fun _ => by norm_num)
  simp only [energy, inv_one, one_mul] at hb
  change 2 * (∑ j, (B.transpose.mulVec z) j * u j) ≤
    squareSum (B.transpose.mulVec z) + squareSum u at hb
  have hr := hR z
  rw [hz] at hr
  change energy (fun i => (w i)⁻¹) t ≤ _
  nlinarith [ht, hp]

#print axioms inverse_energy_step

end D5.S3.Observer.Hankel.BalancedSteinEnergy
