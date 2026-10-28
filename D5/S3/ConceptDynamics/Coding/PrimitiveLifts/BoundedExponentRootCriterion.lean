/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/BoundedExponentRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/BoundedExponentRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Bounded exponent forces trivial return data in finite rootable isotypic classes. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteOrbitRootCriterion
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Universal roots on arbitrary complete return-atlas families of bounded group exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.BoundedExponentRootCriterion

open PrimitiveLiftRootCriterion PrimeOrbitRootCriterion FiniteOrbitRootCriterion
universe u v w

/-- Roots of every positive degree need not be coherent. Only finite actual isotypic
classes obstruct them, and a common positive exponent makes their return data trivial. -/
theorem universal_rootability_iff
    {H : Type u} [Group H] (hH : Monoid.ExponentExists H)
    {ι : Type w} {X : ι → Type v} (A : ∀ i, ReturnAtlas H (X i)) :
    (∀ k : ℕ, 0 < k → ∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧ R^[k] = jointTime A) ↔
    (∀ i, Finite {j // Isotypic A i j} →
      (A i).period = 1 ∧ (A i).holonomy = 1) := by
  classical
  constructor
  · intro roots i hfinite
    haveI : Finite {j // Isotypic A i j} := hfinite
    haveI : Nonempty {j // Isotypic A i j} := ⟨⟨i, isotypic_refl A i⟩⟩
    let N := Nat.card {j // Isotypic A i j}
    let d := (A i).period
    let E := Monoid.exponent H
    let k := N.factorial * d * E
    have hN : 0 < N := Nat.card_pos
    have hdpos : 0 < d := (A i).positive
    have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos N) hdpos)
      hH.exponent_pos
    obtain ⟨L, hsum, hallow⟩ := (arbitrary_root_criterion A hk).mp (roots k hk) i
    obtain ⟨ell, hmem⟩ : ∃ ell, ell ∈ L := by
      cases L with
      | nil => simp at hsum; omega
      | cons ell L => exact ⟨ell, by simp⟩
    obtain ⟨hellpos, hellk, s, m, b, _, hphase, hhol⟩ := hallow ell hmem
    have hellN : ell ≤ N := by
      change ell ≤ Nat.card {j // Isotypic A i j}
      rw [← hsum]
      exact List.le_sum_of_mem hmem
    have hellfac : ell ∣ N.factorial := Nat.dvd_factorial hellpos hellN
    obtain ⟨t, ht⟩ := hellfac
    have hdq : d ∣ k / ell := (Nat.dvd_div_iff_mul_dvd hellk).mpr (by
      refine ⟨t * E, ?_⟩
      dsimp only [k]
      rw [ht]
      ring)
    have hEq : E ∣ k / ell := (Nat.dvd_div_iff_mul_dvd hellk).mpr (by
      refine ⟨t * d, ?_⟩
      dsimp only [k]
      rw [ht]
      ring)
    have hdqz : (d : ℤ) ∣ ((k / ell : ℕ) : ℤ) := by exact_mod_cast hdq
    change ((k / ell : ℕ) : ℤ) * (s.val : ℤ) = 1 + (d : ℤ) * m at hphase
    have hdOne : (d : ℤ) ∣ 1 := by
      have h := dvd_sub (dvd_mul_of_dvd_left hdqz (s.val : ℤ)) (dvd_mul_right (d : ℤ) m)
      simpa only [hphase, add_sub_cancel_right] using h
    have hd : d = 1 := Nat.dvd_one.mp (by exact_mod_cast hdOne)
    have hs : s.val = 0 := by
      have := s.isLt
      change s.val < d at this
      omega
    have hm : m = -1 := by
      simp only [hs, hd, Nat.cast_zero, Nat.cast_one, mul_zero, one_mul] at hphase
      omega
    have hb : b ^ (k / ell) = 1 := by
      obtain ⟨r, hr⟩ := hEq
      rw [hr, pow_mul]
      change (b ^ Monoid.exponent H) ^ r = 1
      rw [Monoid.pow_exponent_eq_one, one_pow]
    refine ⟨hd, ?_⟩
    simpa only [hb, hm, one_mul, zpow_neg_one, inv_eq_one] using hhol
  · intro trivial k hk
    apply (arbitrary_root_criterion A hk).mpr
    intro i
    by_cases hfinite : Finite {j // Isotypic A i j}
    · obtain ⟨hd, hh⟩ := trivial i hfinite
      refine ⟨List.replicate (Nat.card {j // Isotypic A i j}) 1, by simp, ?_⟩
      intro ell hmem
      have hell : ell = 1 := List.eq_of_mem_replicate hmem
      subst ell
      refine ⟨by omega, one_dvd k, ?_⟩
      change Local (k / 1) (A i)
      refine ⟨⟨0, (A i).positive⟩, -1, 1, ?_, ?_, ?_⟩
      · simp [hh, Commute]
      · simp [hd]
      · simp [hh]
    · haveI : Infinite {j // Isotypic A i j} := not_finite_iff_infinite.mp hfinite
      exact ⟨[], by simp, by simp⟩

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.BoundedExponentRootCriterion
