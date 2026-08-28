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

-- A composite coefficient is the weight of the displayed completed path.
def FactorsAlongCompletedPath {V : Type*} [Quiver V] {R : Type*} [Monoid R]
    {X Y Z : V} (edgeWeight : ∀ {i j : V}, (i ⟶ j) → R)
    (compositeCoefficient : R) (firstStep : X ⟶ Y) (secondStep : Y ⟶ Z) : Prop :=
  Path.weight edgeWeight (completedPath firstStep secondStep) = compositeCoefficient

-- A primitive connection path consists of exactly one completion step.
def IsPrimitiveConnectionPath {V : Type*} [Quiver V] {X Z : V}
    (path : Path X Z) : Prop :=
  path.length = 1

-- The three scalar states and the two typed edges are one coefficient-bearing chain.
inductive CompletionChainStage
  | source
  | middle
  | target
  deriving DecidableEq

inductive CompletionChainStep : CompletionChainStage → CompletionChainStage → Type
  | first : CompletionChainStep .source .middle
  | second : CompletionChainStep .middle .target

instance : Quiver CompletionChainStage where
  Hom := CompletionChainStep

def firstCompletionStep : CompletionChainStage.source ⟶ CompletionChainStage.middle :=
  CompletionChainStep.first

def secondCompletionStep : CompletionChainStage.middle ⟶ CompletionChainStage.target :=
  CompletionChainStep.second

def completionChainPath : Path CompletionChainStage.source CompletionChainStage.target :=
  completedPath firstCompletionStep secondCompletionStep

-- The scalar states X, Y, Z read the vertices of the same typed path.
def completionChainStateValue (X Y Z : ℝ) : CompletionChainStage → ℝ
  | .source => X
  | .middle => Y
  | .target => Z

-- The coefficients a, b read the weights of the same path's first and second edges.
def completionChainStepWeight (a b : ℝ) :
    ∀ {i j : CompletionChainStage}, (i ⟶ j) → ℝ
  | _, _, .first => a
  | _, _, .second => b

-- Named bridge between the scalar equations and their edge-weight reading.
def IsCoefficientBearingCompletionChain (a b X Y Z : ℝ) : Prop :=
  completionChainStateValue X Y Z .middle =
      completionChainStepWeight a b firstCompletionStep *
        completionChainStateValue X Y Z .source ∧
    completionChainStateValue X Y Z .target =
      completionChainStepWeight a b secondCompletionStep *
        completionChainStateValue X Y Z .middle

theorem isCoefficientBearingCompletionChain_iff (a b X Y Z : ℝ) :
    IsCoefficientBearingCompletionChain a b X Y Z ↔
      (Y = a * X ∧ Z = b * Y) := by
  rfl

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

-- Certificate status includes the source's positive-real domain and path data.
def IsStructuralConstantCompositionCertificate (x : ℝ)
    (path : Path RamanujanCompletionStage.source RamanujanCompletionStage.scaleCompleted) : Prop :=
  0 < x ∧
    path = ramanujanCompletionPath ∧
      ramanujanPathRoles path =
        [.gaussianTotalMass, .exponentialFlow, .scaleJacobian] ∧
      ¬ IsPrimitiveConnectionPath path ∧
      ramanujanRadical x = Path.weight (ramanujanStepWeight x) path

theorem connection_coefficient_multiplication :
    (∀ (a b X Y Z : ℝ), IsCoefficientBearingCompletionChain a b X Y Z →
      Z = (a * b) * X ∧
        FactorsAlongCompletedPath (completionChainStepWeight a b) (a * b)
          firstCompletionStep secondCompletionStep ∧
        ¬ IsPrimitiveConnectionPath completionChainPath) ∧
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
  refine ⟨?_, hfactor, ?_⟩
  · intro a b X Y Z hbridge
    rcases (isCoefficientBearingCompletionChain_iff a b X Y Z).1 hbridge with ⟨hY, hZ⟩
    refine ⟨?_, ?_, ?_⟩
    · calc
        Z = b * Y := hZ
        _ = b * (a * X) := by rw [hY]
        _ = (a * b) * X := by ring
    · change Path.weight (completionChainStepWeight a b)
        (completedPath firstCompletionStep secondCompletionStep) = a * b
      rw [completedPath, Path.weight_comp]
      simp [completionChainStepWeight, firstCompletionStep, secondCompletionStep,
        Quiver.Hom.toPath]
    · simp [IsPrimitiveConnectionPath, completionChainPath, completedPath,
        firstCompletionStep, secondCompletionStep]
  · intro x hx
    refine ⟨hx, rfl, ?_, ?_, ?_⟩
    · simp [ramanujanCompletionPath, ramanujanPathRoles, ramanujanStepRole,
        Quiver.Hom.toPath]
    · simp [IsPrimitiveConnectionPath, ramanujanCompletionPath]
    · simpa [ramanujanCompletionPath, ramanujanStepWeight, Quiver.Hom.toPath,
        Path.weight] using hfactor x hx

-- Probe R1 (CAS-A1): the shared bridge recovers the boxed scalar conclusion.
example : (6 : ℝ) = (2 * 3) * 1 := by
  have hbridge : IsCoefficientBearingCompletionChain 2 3 1 2 6 :=
    (isCoefficientBearingCompletionChain_iff 2 3 1 2 6).2 ⟨by norm_num, by norm_num⟩
  exact (connection_coefficient_multiplication.1 2 3 1 2 6 hbridge).1

-- Probe R2/T2 (CAS-A1/A2): one bridge exposes both scalar and edge-weight readings.
example (a b X Y Z : ℝ) (hbridge : IsCoefficientBearingCompletionChain a b X Y Z) :
    (Y = a * X ∧ Z = b * Y) ∧
      FactorsAlongCompletedPath (completionChainStepWeight a b) (a * b)
        firstCompletionStep secondCompletionStep := by
  exact ⟨(isCoefficientBearingCompletionChain_iff a b X Y Z).1 hbridge,
    (connection_coefficient_multiplication.1 a b X Y Z hbridge).2.1⟩

-- Probe R3 (CAS-A3): non-primitiveness is about that same completed path.
example : ¬ IsPrimitiveConnectionPath completionChainPath := by
  have hbridge : IsCoefficientBearingCompletionChain 2 3 1 2 6 :=
    (isCoefficientBearingCompletionChain_iff 2 3 1 2 6).2 ⟨by norm_num, by norm_num⟩
  exact (connection_coefficient_multiplication.1 2 3 1 2 6 hbridge).2.2

-- Probe R4 (CAS-A4): the positive-real Ramanujan factorization is public.
example :
    ramanujanRadical 1 =
      gaussianMassFactor * exponentialFlowFactor 1 * scaleJacobianFactor 1 :=
  connection_coefficient_multiplication.2.1 1 (by norm_num)

-- Probe R5 (CAS-A5): the certificate fixes roles in path order.
example :
    ramanujanPathRoles ramanujanCompletionPath =
      [.gaussianTotalMass, .exponentialFlow, .scaleJacobian] :=
  (connection_coefficient_multiplication.2.2 1 (by norm_num)).2.2.1

example :
    ramanujanPathRoles ramanujanCompletionPath ≠
      [.exponentialFlow, .gaussianTotalMass, .scaleJacobian] := by
  intro hpermuted
  have hordered :=
    (connection_coefficient_multiplication.2.2 1 (by norm_num)).2.2.1
  rw [hordered] at hpermuted
  simp at hpermuted

-- Probe T1 (CAS-A5): zero is outside the certificate carrier itself.
example :
    ¬ IsStructuralConstantCompositionCertificate 0 ramanujanCompletionPath := by
  intro hcertificate
  exact (lt_irrefl 0) hcertificate.1

end D5.S0.Naming.Composition.ConnectionCoefficientComposition
