/- GID: D5/S3/VertexAlgebra/FiniteCubicRecovery
   generality: G
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite real algebra recovery from metric and cubic tensor; stabilizers preserve product. -/

import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.FiniteCubicRecovery

open scoped BigOperators

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Space (n : ℕ) := ℝ × Vec n

/-- The Euclidean form on the traceless coordinates. -/
def vecInner {n : ℕ} (u v : Vec n) : ℝ := ∑ i, u i * v i

/-- The finite algebra form, normalized so that the distinguished unit has norm `3`. -/
def spaceInner {n : ℕ} (x y : Space n) : ℝ := 3 * x.1 * y.1 + vecInner x.2 y.2

def unit {n : ℕ} : Space n := (1, 0)

def traceless {n : ℕ} (u : Vec n) : Space n := (0, u)

/-- A finite real algebra in the coordinate model used by the recovery theorem. -/
structure FiniteCubicAlgebra (n : ℕ) where
  mul : Space n →ₗ[ℝ] Space n →ₗ[ℝ] Space n
  comm : ∀ x y, mul x y = mul y x
  unit_mul : ∀ x, mul unit x = x
  invariant : ∀ x y z, spaceInner (mul x y) z = spaceInner x (mul y z)

def cubicSharp {n : ℕ} (A : FiniteCubicAlgebra n) (u v : Vec n) : Vec n :=
  (A.mul (traceless u) (traceless v)).2

def cubicTensor {n : ℕ} (A : FiniteCubicAlgebra n)
    (u v w : Vec n) : ℝ :=
  vecInner (cubicSharp A u v) w

noncomputable def recoveredMul {n : ℕ} (sharp : Vec n → Vec n → Vec n) (x y : Space n) : Space n :=
  (x.1 * y.1 + vecInner x.2 y.2 / 3,
    x.1 • y.2 + y.1 • x.2 + sharp x.2 y.2)

private theorem mul_traceless_traceless {n : ℕ} (A : FiniteCubicAlgebra n)
    (u v : Vec n) :
    A.mul (traceless u) (traceless v) =
      (vecInner u v / 3, cubicSharp A u v) := by
  apply Prod.ext
  · have h := A.invariant (traceless u) (traceless v) unit
    have hv : A.mul (traceless v) unit = traceless v := by
      rw [A.comm, A.unit_mul]
    rw [hv] at h
    simp [spaceInner, traceless, unit, vecInner] at h ⊢
    linear_combination h / 3
  · rfl

private theorem mul_unit_traceless {n : ℕ} (A : FiniteCubicAlgebra n)
    (a : ℝ) (u : Vec n) :
    A.mul (a • unit) (traceless u) = (0, a • u) := by
  simp only [map_smul, LinearMap.smul_apply, A.unit_mul]
  ext <;> simp [traceless]

private theorem mul_traceless_unit {n : ℕ} (A : FiniteCubicAlgebra n)
    (a : ℝ) (u : Vec n) :
    A.mul (traceless u) (a • unit) = (0, a • u) := by
  rw [A.comm, mul_unit_traceless]

private theorem mul_scalar_unit {n : ℕ} (A : FiniteCubicAlgebra n)
    (a b : ℝ) : A.mul (a • unit) (b • unit) = (a * b, 0) := by
  simp only [map_smul, LinearMap.smul_apply, A.unit_mul, map_smul]
  simp [unit]
  ring

/-- The full multiplication is forced by the unit, metric, and cubic tensor. -/
theorem mul_eq_recoveredMul {n : ℕ} (A : FiniteCubicAlgebra n) (x y : Space n) :
    A.mul x y = recoveredMul (cubicSharp A) x y := by
  have hx : x = x.1 • unit + traceless x.2 := by
    ext <;> simp [unit, traceless]
  have hy : y = y.1 • unit + traceless y.2 := by
    ext <;> simp [unit, traceless]
  rw [hx, hy]
  simp only [map_add, LinearMap.add_apply]
  rw [mul_scalar_unit, mul_unit_traceless, mul_traceless_unit,
    mul_traceless_traceless]
  simp [recoveredMul, unit, traceless, vecInner, smul_eq_mul]
  abel

/-- Coordinate form of the recovery identity, corresponding to the `ae + u` formula. -/
theorem mul_recovery_formula {n : ℕ} (A : FiniteCubicAlgebra n)
    (a b : ℝ) (u v : Vec n) :
    A.mul (a, u) (b, v) =
      (a * b + vecInner u v / 3, a • v + b • u + cubicSharp A u v) := by
  simpa [recoveredMul] using mul_eq_recoveredMul A (a, u) (b, v)

/-- Extending an orthogonal map on the unit complement while fixing the unit. -/
def extend {n : ℕ} (U : Vec n ≃ₗ[ℝ] Vec n) : Space n ≃ₗ[ℝ] Space n :=
  (LinearEquiv.refl ℝ ℝ).prodCongr U

def IsOrthogonal {n : ℕ} (U : Vec n ≃ₗ[ℝ] Vec n) : Prop :=
  ∀ u v, vecInner (U u) (U v) = vecInner u v

def PreservesCubic {n : ℕ} (A : FiniteCubicAlgebra n)
    (U : Vec n ≃ₗ[ℝ] Vec n) : Prop :=
  ∀ u v, U (cubicSharp A u v) = cubicSharp A (U u) (U v)

private theorem extend_apply {n : ℕ} (U : Vec n ≃ₗ[ℝ] Vec n)
    (x : Space n) : extend U x = (x.1, U x.2) := by
  simp [extend]

private theorem extend_inner {n : ℕ} (U : Vec n ≃ₗ[ℝ] Vec n)
    (hU : IsOrthogonal U) (x y : Space n) :
    spaceInner (extend U x) (extend U y) = spaceInner x y := by
  simp only [extend_apply, spaceInner]
  rw [hU]

/-- An orthogonal map is a product automorphism exactly when it preserves the cubic data. -/
theorem extend_preserves_mul_iff {n : ℕ} (A : FiniteCubicAlgebra n)
    (U : Vec n ≃ₗ[ℝ] Vec n) (hU : IsOrthogonal U) :
    (∀ x y, extend U (A.mul x y) = A.mul (extend U x) (extend U y)) ↔
      PreservesCubic A U := by
  constructor
  · intro hmul u v
    have hprod := hmul (traceless u) (traceless v)
    have hsharp := congrArg Prod.snd hprod
    simpa [extend_apply, traceless, cubicSharp] using hsharp
  · intro hT x y
    rw [mul_eq_recoveredMul A, mul_eq_recoveredMul A]
    apply Prod.ext
    · simp only [extend_apply, recoveredMul]
      rw [hU]
    · simp only [extend_apply, recoveredMul, map_add, map_smul]
      rw [hT x.2 y.2]

/-- Sharp-form cubic preservation implies preservation of the scalar three-point tensor. -/
theorem preserves_cubicTensor {n : ℕ} (A : FiniteCubicAlgebra n)
    (U : Vec n ≃ₗ[ℝ] Vec n) (hU : IsOrthogonal U) (hT : PreservesCubic A U) :
    ∀ u v w, cubicTensor A (U u) (U v) (U w) = cubicTensor A u v w := by
  intro u v w
  simp only [cubicTensor]
  rw [← hT, hU]

end D5.S3.VertexAlgebra.FiniteCubicRecovery
