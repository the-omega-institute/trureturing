/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalBond
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalBond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual independent bond configurations on a three-terminal star, their five connectivity masses, determinant bound and sharpness. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

open scoped BigOperators

/-- The five partitions of three labelled terminals. -/
inductive Mode where
  | separate | ab | bc | all | ac
  deriving DecidableEq, Fintype

/-- Edges are indexed by `E`, with endpoints specified independently of their states. -/
def openGraph {V E : Type*} (ends : E → V × V) (ω : E → Bool) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ e, ω e = true ∧ ends e = (x,y)

/-- Decidable reachability in the actual open graph. -/
def connected {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (ω : E → Bool) (x y : V) : Bool := by
  letI : DecidableRel (openGraph ends ω).Adj := fun u v =>
    inferInstanceAs (Decidable (u ≠ v ∧
      ((∃ e, ω e = true ∧ ends e = (u,v)) ∨ (∃ e, ω e = true ∧ ends e = (v,u)))))
  exact decide ((openGraph ends ω).Reachable x y)

/-- The partition is read from paths, before any probabilities are assigned. -/
def partition {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (a b c : V) (ω : E → Bool) : Mode :=
  if connected ends ω a b then
    if connected ends ω b c then .all else .ab
  else if connected ends ω b c then .bc
  else if connected ends ω a c then .ac else .separate

/-- Independent Bernoulli bond mass on the complete configuration cube. -/
def weight {E : Type*} [Fintype E] (θ : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then θ e else 1 - θ e

/-- Actual five-mode pushforward, a finite sum over open-edge configurations. -/
def law {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (a b c : V) (θ : E → ℝ) (s : Mode) : ℝ :=
  ∑ ω : E → Bool, if partition ends a b c ω = s then weight θ ω else 0

/-- The determinant of the four base partition masses. -/
def delta (p : Mode → ℝ) : ℝ := p .separate * p .all - p .ab * p .bc

private lemma sum_cube_succ (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ ω, f ω) = ∑ x : Bool, ∑ ω : Fin n → Bool, f (Fin.cons x ω) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

/-- The center is vertex 3; edges 0,1,2 lead to terminals 0,1,2. -/
def starEnds (e : Fin 3) : Fin 4 × Fin 4 := (3, e.castSucc)

private lemma star_partition (ω : Fin 3 → Bool) :
    partition starEnds 0 1 2 ω =
      if ω 0 && ω 1 then (if ω 1 && ω 2 then .all else .ab)
      else if ω 1 && ω 2 then .bc
      else if ω 0 && ω 2 then .ac else .separate := by
  revert ω
  decide +kernel

/-- All five masses of the actual star, not a stipulated five-vector. -/
theorem star_law (A B C : ℝ) :
    law starEnds 0 1 2 ![A,B,C] = fun s => match s with
      | .separate => 1-A*B-A*C-B*C+2*A*B*C
      | .ab => A*B*(1-C)
      | .bc => (1-A)*B*C
      | .all => A*B*C
      | .ac => A*(1-B)*C := by
  funext s
  unfold law
  simp only [star_partition]
  rw [sum_cube_succ, Bool.sum_bool]
  simp only [sum_cube_succ, Bool.sum_bool]
  cases s <;> simp [weight, Fin.prod_univ_succ] <;> ring

/-- The source-law determinant factors through the exceptional partition mass. -/
theorem star_determinant (A B C : ℝ) :
    delta (law starEnds 0 1 2 ![A,B,C]) =
      B*(1-A*C)*law starEnds 0 1 2 ![A,B,C] .ac := by
  rw [star_law]
  simp only [delta]
  ring

/-- The constant-one bound includes all deterministic and zero-mass boundaries. -/
theorem star_bound (A B C : ℝ) (hA : A ∈ Set.Icc 0 1)
    (hB : B ∈ Set.Icc 0 1) (hC : C ∈ Set.Icc 0 1) :
    0 ≤ delta (law starEnds 0 1 2 ![A,B,C]) ∧
    delta (law starEnds 0 1 2 ![A,B,C]) ≤ law starEnds 0 1 2 ![A,B,C] .ac := by
  have hAC0 : 0 ≤ A*C := mul_nonneg hA.1 hC.1
  have hAC1 : A*C ≤ 1 := mul_le_one₀ hA.2 hC.1 hC.2
  have hZ : 0 ≤ law starEnds 0 1 2 ![A,B,C] .ac := by
    rw [star_law]
    exact mul_nonneg (mul_nonneg hA.1 (sub_nonneg.mpr hB.2)) hC.1
  rw [star_determinant]
  constructor
  · exact mul_nonneg (mul_nonneg hB.1 (sub_nonneg.mpr hAC1)) hZ
  · exact mul_le_of_le_one_left hZ (by nlinarith [mul_nonneg hB.1 hAC0])

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
