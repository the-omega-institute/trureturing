/- GID: D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unstable-eigenvalue count of a clamped Lennard-Jones chain is k-1 or k. -/

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
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
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hfirst : ∀ x : ℝ, 0 < x →
      deriv ljPotential x = -12 * x ^ (-13 : ℤ) + 12 * x ^ (-7 : ℤ) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    change deriv ((fun y : ℝ => y ^ (-12 : ℤ)) -
      (fun y : ℝ => 2 * y ^ (-6 : ℤ))) x = _
    rw [deriv_sub]
    · rw [deriv_zpow]
      rw [deriv_const_mul (2 : ℝ)]
      · rw [deriv_zpow]
        ring_nf
      · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)
    · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)).const_mul 2
  have hev : (fun x : ℝ => deriv ljPotential x) =ᶠ[nhds r]
      (fun x : ℝ => -12 * x ^ (-13 : ℤ) + 12 * x ^ (-7 : ℤ)) := by
    filter_upwards [eventually_gt_nhds hr] with x hx
    exact hfirst x hx
  rw [hev.deriv_eq]
  change deriv ((fun x : ℝ => -12 * x ^ (-13 : ℤ)) +
      (fun x : ℝ => 12 * x ^ (-7 : ℤ))) r = _
  rw [deriv_add]
  · rw [deriv_const_mul (-12 : ℝ), deriv_const_mul (12 : ℝ)]
    · rw [deriv_zpow, deriv_zpow]
      ring_nf
      rw [zpow_neg, zpow_neg]
      field_simp
      ring
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)
  · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)).const_mul (-12)
  · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)).const_mul 12

private lemma inflection_iff (r : ℝ) (hr : 0 < r) :
    inflectionPoint < r ↔ 13 < 7 * r ^ (6 : ℕ) := by
  have hroot : 0 < (13 / 7 : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpow : ((13 / 7 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6 : ℝ) = 13 / 7 := by
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (13 / 7 : ℝ))]
    norm_num
  change (13 / 7 : ℝ) ^ ((1 : ℝ) / 6) < r ↔ _
  rw [← Real.rpow_lt_rpow_iff hroot.le hr.le (by norm_num : (0 : ℝ) < 6)]
  norm_num [hpow]
  constructor <;> intro h
  · nlinarith
  · nlinarith

private lemma curvature_sign (r : ℝ) (hr : 0 < r) :
    deriv (deriv ljPotential) r < 0 ↔ inflectionPoint < r := by
  rw [curvature_formula r hr, div_neg_iff]
  have hden : 0 < r ^ (14 : ℕ) := pow_pos hr _
  rw [inflection_iff r hr]
  constructor
  · intro h
    rcases h with h | h
    · exfalso
      linarith
    · nlinarith [h.1]
  · intro h
    right
    constructor
    · nlinarith [h]
    · exact hden

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
