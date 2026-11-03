/- GID: D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim; result=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result; claim=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim
   digest: Two cubic product-coupled baths admit an open set with five Bose-selected modes. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators
open Matrix Set

/-- The source's odd power-law spectrum, with its positive scale set to one. -/
noncomputable def spectral (d x : ℝ) : ℝ := Real.sign x * |x| ^ d

/-- Squared coupling amplitudes normalized to total weight one. -/
noncomputable def weight {m : ℕ} (F : Fin m → ℝ) (i : Fin m) : ℝ :=
  F i / (∑ k, F k)

/-- The source's two-bath rate asymmetry, with the positive factor `2π/ℏ` set to one. -/
noncomputable def asym (d : ℝ) {m : ℕ} (ε F G : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => spectral d (ε j - ε i) *
    (weight F i * weight F j - weight G i * weight G j)

/-- Equation MS-problem; `w` denotes the source's vector of selected occupations. -/
def IsSelected {m : ℕ} (a : Matrix (Fin m) (Fin m) ℝ) (s : Finset (Fin m))
    (w : Fin m → ℝ) : Prop :=
  ∀ i, (i ∈ s → 0 < w i ∧ (a *ᵥ w) i = 0) ∧
    (i ∉ s → w i = 0 ∧ (a *ᵥ w) i < 0)

/-- Positive two-bath parameters supporting at least four selected modes. -/
def violating (d : ℝ) (m : ℕ) :
    Set ((Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ)) :=
  {p | (∀ i, 0 < p.2.1 i) ∧ (∀ i, 0 < p.2.2 i) ∧
    ∃ s w, IsSelected (asym d p.1 p.2.1 p.2.2) s w ∧ 4 ≤ s.card}

/-- The preregistered generic reading of the expected two-bath bound. -/
def claim : Prop :=
  ∀ d : ℝ, 0 < d → ∀ m : ℕ, interior (violating d m) = ∅

private noncomputable def pfaffianVector (a : Matrix (Fin 5) (Fin 5) ℝ) : Fin 5 → ℝ :=
  ![a 1 2 * a 3 4 - a 1 3 * a 2 4 + a 1 4 * a 2 3,
    -(a 0 2 * a 3 4 - a 0 3 * a 2 4 + a 0 4 * a 2 3),
    a 0 1 * a 3 4 - a 0 3 * a 1 4 + a 0 4 * a 1 3,
    -(a 0 1 * a 2 4 - a 0 2 * a 1 4 + a 0 4 * a 1 2),
    a 0 1 * a 2 3 - a 0 2 * a 1 3 + a 0 3 * a 1 2]

private noncomputable def base :
    (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) :=
  (![1, 2, 3, 4, 5], ![5, 4, 4, 4, 4], ![6, 6, 3, 3, 3])

private def couplingDomain : Set ((Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) :=
  {p | (∀ i, 0 < p.2.1 i) ∧ (∀ i, 0 < p.2.2 i)}

private noncomputable def neighborhood :
    Set ((Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) :=
  {p | p ∈ couplingDomain ∧ ∀ i, 0 < pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i}

private theorem spectral_three (x : ℝ) : spectral 3 x = x ^ 3 := by
  sorry

private theorem asym_skew {m : ℕ} (ε F G : Fin m → ℝ) (i j : Fin m) :
    asym 3 ε F G j i = -asym 3 ε F G i j := by
  sorry

private theorem pfaffian_kernel (a : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, a j i = -a i j) : a *ᵥ pfaffianVector a = 0 := by
  sorry

private theorem couplingDomain_open : IsOpen couplingDomain := by
  sorry

private theorem asym_continuousOn (i j : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      asym 3 p.1 p.2.1 p.2.2 i j) couplingDomain := by
  sorry

private theorem pfaffian_continuousOn (i : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i) couplingDomain := by
  sorry

private theorem neighborhood_open : IsOpen neighborhood := by
  sorry

private theorem base_mem : base ∈ neighborhood := by
  sorry

private theorem neighborhood_subset : neighborhood ⊆ violating 3 5 := by
  sorry

private theorem interior_nonempty : (interior (violating 3 5)).Nonempty := by
  exact ⟨base, interior_mono neighborhood_subset
    (neighborhood_open.interior_eq.symm ▸ base_mem)⟩

theorem result : ¬ claim := by
  intro h
  obtain ⟨p, hp⟩ := interior_nonempty
  rw [h 3 (by norm_num) 5] at hp
  exact hp

end D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
