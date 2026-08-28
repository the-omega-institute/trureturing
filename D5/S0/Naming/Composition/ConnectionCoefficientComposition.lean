/- GID: D5/S0/Naming/Composition/ConnectionCoefficientComposition
   generality: G
   mirror-B: D5/B/S0/Naming/Composition/ConnectionCoefficientComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed completion paths retain coefficient order, roles, and certificate status. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Tactic

namespace D5.S0.Naming.Composition.ConnectionCoefficientComposition

open Quiver

-- The completed path obtained by following two typed completion steps in order.
def completedPath {V : Type*} [Quiver V] {X Y Z : V}
    (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z) : Path X Z :=
  firstStep.toPath.comp secondStep.toPath

-- A composite coefficient factors along the displayed pair of typed completion steps.
def FactorsAlongCompletedPath {V : Type*} [Quiver V] {R : Type*} [Monoid R]
    {X Y Z : V} (edgeWeight : ∀ {i j : V}, (i ⟶ j) → R)
    (compositeCoefficient : R) (path : Path X Z)
    (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z) : Prop :=
  path = completedPath firstStep secondStep ∧
    Path.weight edgeWeight path = compositeCoefficient

-- A primitive connection path consists of exactly one completion step.
def IsPrimitiveConnectionPath {V : Type*} [Quiver V] {X Z : V}
    (path : Path X Z) : Prop :=
  path.length = 1

-- The four completion stages used by the Ramanujan 541 factorization.
inductive RamanujanCompletionStage
  | source
  | gaussianCompleted
  | flowCompleted
  | scaleCompleted
  deriving DecidableEq

-- Each Ramanujan factor is a typed edge and can occur only at its source stage.
inductive RamanujanCompletionStep :
    RamanujanCompletionStage → RamanujanCompletionStage → Type
  | completeGaussian : RamanujanCompletionStep .source .gaussianCompleted
  | advanceExponential : RamanujanCompletionStep .gaussianCompleted .flowCompleted
  | applyScale : RamanujanCompletionStep .flowCompleted .scaleCompleted

instance : Quiver RamanujanCompletionStage where
  Hom := RamanujanCompletionStep

-- The semantic role carried by each factor in the Ramanujan completion path.
inductive RamanujanFactorRole
  | gaussianTotalMass
  | exponentialFlow
  | scaleJacobian
  deriving DecidableEq

def ramanujanStepRole {i j : RamanujanCompletionStage} (step : i ⟶ j) :
    RamanujanFactorRole :=
  match step with
  | .completeGaussian => .gaussianTotalMass
  | .advanceExponential => .exponentialFlow
  | .applyScale => .scaleJacobian

def ramanujanPathRoles :
    ∀ {i j : RamanujanCompletionStage}, Path i j → List RamanujanFactorRole
  | _, _, .nil => []
  | _, _, .cons path step => ramanujanPathRoles path ++ [ramanujanStepRole step]

-- The ordered Gaussian, exponential-flow, and scale-Jacobian completion path.
def ramanujanCompletionPath :
    Path RamanujanCompletionStage.source RamanujanCompletionStage.scaleCompleted :=
  (Quiver.Hom.toPath RamanujanCompletionStep.completeGaussian).comp
    ((Quiver.Hom.toPath RamanujanCompletionStep.advanceExponential).comp
      (Quiver.Hom.toPath RamanujanCompletionStep.applyScale))

noncomputable def gaussianMassFactor : ℝ :=
  Real.sqrt (Real.pi / 2)

noncomputable def exponentialFlowFactor (x : ℝ) : ℝ :=
  Real.exp (x / 2)

noncomputable def scaleJacobianFactor (x : ℝ) : ℝ :=
  x ^ (-1 / 2 : ℝ)

noncomputable def ramanujanRadical (x : ℝ) : ℝ :=
  Real.sqrt (Real.pi * Real.exp x / (2 * x))

noncomputable def ramanujanStepWeight (x : ℝ)
    {i j : RamanujanCompletionStage} (step : i ⟶ j) : ℝ :=
  match step with
  | .completeGaussian => gaussianMassFactor
  | .advanceExponential => exponentialFlowFactor x
  | .applyScale => scaleJacobianFactor x

-- Certificate status requires the exact completed path, its ordered roles,
-- non-primitiveness, and agreement between the radical and the path weight.
def IsStructuralConstantCompositionCertificate (x : ℝ)
    (path : Path RamanujanCompletionStage.source RamanujanCompletionStage.scaleCompleted) : Prop :=
  path = ramanujanCompletionPath ∧
    ramanujanPathRoles path =
      [.gaussianTotalMass, .exponentialFlow, .scaleJacobian] ∧
    ¬ IsPrimitiveConnectionPath path ∧
    ramanujanRadical x = Path.weight (ramanujanStepWeight x) path

theorem connection_coefficient_multiplication :
    (∀ (a b X Y Z : ℝ),
      Y = a * X → Z = b * Y → Z = (a * b) * X) ∧
    (∀ {V : Type} [Quiver.{0} V] {R : Type} [Monoid R]
      {X Y Z : V} (edgeWeight : ∀ {i j : V}, (i ⟶ j) → R)
      (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z),
      Path.weight edgeWeight (completedPath firstStep secondStep) =
        edgeWeight firstStep * edgeWeight secondStep) ∧
    (∀ {V : Type} [Quiver.{0} V] {R : Type} [Monoid R]
      {X Y Z : V} (edgeWeight : ∀ {i j : V}, (i ⟶ j) → R)
      (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z),
      FactorsAlongCompletedPath edgeWeight
        (edgeWeight firstStep * edgeWeight secondStep)
        (completedPath firstStep secondStep) firstStep secondStep) ∧
    (∀ {V : Type} [Quiver.{0} V] {X Y Z : V}
      (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z),
      ¬ IsPrimitiveConnectionPath (completedPath firstStep secondStep)) ∧
    (∀ (x : ℝ), 0 < x →
      ramanujanRadical x =
        gaussianMassFactor * exponentialFlowFactor x * scaleJacobianFactor x) ∧
    (∀ (x : ℝ), 0 < x →
      IsStructuralConstantCompositionCertificate x ramanujanCompletionPath) := by
  fail_if_success rfl
  have hfactor : ∀ (x : ℝ), 0 < x →
      ramanujanRadical x =
        gaussianMassFactor * exponentialFlowFactor x * scaleJacobianFactor x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hrad : 0 ≤ Real.pi * Real.exp x / (2 * x) := by
      positivity
    have hpi : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 := by
      exact Real.sq_sqrt (by positivity)
    have hexp : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hrpow : (x ^ (-1 / 2 : ℝ)) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx)]
      norm_num
      exact Real.rpow_neg_one x
    have hproduct :
        (Real.sqrt (Real.pi / 2) * Real.exp (x / 2) * x ^ (-1 / 2 : ℝ)) ^ 2 =
          Real.pi * Real.exp x / (2 * x) := by
      rw [mul_pow, mul_pow, hpi, hexp, hrpow]
      field_simp [hx0]
    change Real.sqrt (Real.pi * Real.exp x / (2 * x)) =
      Real.sqrt (Real.pi / 2) * Real.exp (x / 2) * x ^ (-1 / 2 : ℝ)
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    calc
      (Real.sqrt (Real.pi * Real.exp x / (2 * x))) ^ 2 =
          Real.pi * Real.exp x / (2 * x) := Real.sq_sqrt hrad
      _ = (Real.sqrt (Real.pi / 2) * Real.exp (x / 2) *
          x ^ (-1 / 2 : ℝ)) ^ 2 := hproduct.symm
  refine ⟨?_, ?_, ?_, ?_, hfactor, ?_⟩
  · intro a b X Y Z hY hZ
    calc
      Z = b * Y := hZ
      _ = b * (a * X) := by rw [hY]
      _ = (a * b) * X := by ring
  · intro V quiver R monoid X Y Z edgeWeight firstStep secondStep
    rw [completedPath, Path.weight_comp]
    simp [Quiver.Hom.toPath]
  · intro V quiver R monoid X Y Z edgeWeight firstStep secondStep
    refine ⟨rfl, ?_⟩
    rw [completedPath, Path.weight_comp]
    simp [Quiver.Hom.toPath]
  · intro V quiver X Y Z firstStep secondStep
    simp [IsPrimitiveConnectionPath, completedPath]
  · intro x hx
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [ramanujanCompletionPath, ramanujanPathRoles, ramanujanStepRole,
        Quiver.Hom.toPath]
    · simp [IsPrimitiveConnectionPath, ramanujanCompletionPath]
    · simpa [ramanujanCompletionPath, ramanujanStepWeight, Quiver.Hom.toPath,
        Path.weight] using hfactor x hx

-- The public type exposes non-primitiveness for every typed two-step path.
example {V : Type} [Quiver.{0} V] {X Y Z : V}
    (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z) :
    ¬ IsPrimitiveConnectionPath (completedPath firstStep secondStep) :=
  connection_coefficient_multiplication.2.2.2.1 firstStep secondStep

-- The scalar carriers cannot be replaced by Unit while projecting the public clause.
example : True := by
  fail_if_success
    have _hUnit : ∀ (a b X Y Z : Unit),
        Y = a * X → Z = b * Y → Z = (a * b) * X :=
      connection_coefficient_multiplication.1
  trivial

-- The source equations expose a concrete nontrivial consequence of the public clause.
example : (6 : ℝ) = (2 * 3) * 1 := by
  exact connection_coefficient_multiplication.1 2 3 1 2 6 (by norm_num) (by norm_num)

-- The certificate fixes factor roles in path order, not merely their commutative product.
example :
    ramanujanPathRoles ramanujanCompletionPath =
      [.gaussianTotalMass, .exponentialFlow, .scaleJacobian] :=
  (connection_coefficient_multiplication.2.2.2.2.2 1 (by norm_num)).2.1

example :
    ramanujanPathRoles ramanujanCompletionPath ≠
      [.exponentialFlow, .gaussianTotalMass, .scaleJacobian] := by
  intro hpermuted
  have hordered :=
    (connection_coefficient_multiplication.2.2.2.2.2 1 (by norm_num)).2.1
  rw [hordered] at hpermuted
  simp at hpermuted

end D5.S0.Naming.Composition.ConnectionCoefficientComposition
