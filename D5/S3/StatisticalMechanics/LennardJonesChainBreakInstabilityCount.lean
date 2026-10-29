/- GID: D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unstable-eigenvalue count of a clamped Lennard-Jones chain is k-1 or k. -/

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

def ljPotential (r : ℝ) : ℝ := r ^ (-12 : ℤ) - 2 * r ^ (-6 : ℤ)

def inflectionPoint : ℝ := (13 / 7 : ℝ) ^ ((1 : ℝ) / 6)

def bondLength {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) (j : Fin (m + 1)) : ℝ :=
  d + u j.succ - u j.castSucc

def force {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) (n : Fin m) : ℝ :=
  deriv ljPotential (bondLength d u n.succ) - deriv ljPotential (bondLength d u n.castSucc)

def jacobian {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) : Matrix (Fin m) (Fin m) ℝ := fun n q =>
  let c : Fin (m + 1) → ℝ := fun j => deriv (deriv ljPotential) (bondLength d u j)
  if n = q then -c n.castSucc - c n.succ
  else if (n : ℕ) + 1 = (q : ℕ) then c n.succ
  else if (q : ℕ) + 1 = (n : ℕ) then c q.succ
  else 0

def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (d : ℝ), 0 < d →
    ∀ (u : Fin (m + 2) → ℝ), u 0 = 0 → u (Fin.last _) = 0 →
      (∀ n, force d u n = 0) → (∀ j, 0 < bondLength d u j) →
        ∀ k : ℕ, 1 ≤ k →
          (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k →
            ∀ h : (jacobian d u).IsHermitian,
              k - 1 ≤ (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ∧
                (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ≤ k

private lemma curvature_formula (r : ℝ) (hr : 0 < r) :
    deriv (deriv ljPotential) r = 12 * (13 - 7 * r ^ (6 : ℕ)) / r ^ (14 : ℕ) := by
  sorry

private lemma curvature_sign (r : ℝ) (hr : 0 < r) :
    deriv (deriv ljPotential) r < 0 ↔ inflectionPoint < r := by
  sorry

private lemma jacobian_factorization {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) :
    ∃ (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
      (c : Fin (m + 1) → ℝ),
      (∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
        (if n.succ = j then 1 else 0)) ∧
      (∀ j, c j = deriv (deriv ljPotential) (bondLength d u j)) ∧
      jacobian d u = -(b.transpose * Matrix.diagonal c * b) := by
  sorry

private lemma bond_difference_injective {m : ℕ}
    (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
    (hb : ∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
      (if n.succ = j then 1 else 0)) :
    Function.Injective (b.mulVec) := by
  sorry

private lemma bond_difference_range {m : ℕ}
    (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
    (hb : ∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
      (if n.succ = j then 1 else 0)) :
    Module.finrank ℝ (LinearMap.range b.mulVecLin) = m := by
  sorry

private lemma inertia_lower_bound {m : ℕ} (hm : 1 ≤ m) (d : ℝ)
    (u : Fin (m + 2) → ℝ) (hd : 0 < d)
    (hpos : ∀ j, 0 < bondLength d u j)
    (k : ℕ) (hk : 1 ≤ k)
    (hbroken : (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k)
    (h : (jacobian d u).IsHermitian) :
    k - 1 ≤ Finset.card (Finset.univ.filter (fun i => 0 < h.eigenvalues i)) := by
  sorry

private lemma inertia_upper_bound {m : ℕ} (hm : 1 ≤ m) (d : ℝ)
    (u : Fin (m + 2) → ℝ) (hd : 0 < d)
    (hpos : ∀ j, 0 < bondLength d u j)
    (k : ℕ) (hk : 1 ≤ k)
    (hbroken : (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k)
    (h : (jacobian d u).IsHermitian) :
    Finset.card (Finset.univ.filter (fun i => 0 < h.eigenvalues i)) ≤ k := by
  sorry

private lemma result_core : claim := by
  intro m hm d hd u hu0 huLast hsteady hpos k hk hbroken h
  exact ⟨inertia_lower_bound hm d u hd hpos k hk hbroken h,
    inertia_upper_bound hm d u hd hpos k hk hbroken h⟩

theorem result : claim := result_core

end D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
