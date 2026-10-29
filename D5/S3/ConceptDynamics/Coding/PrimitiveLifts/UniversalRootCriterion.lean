/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/UniversalRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/UniversalRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Bounded exponent forces trivial return data in finite rootable isotypic classes. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteOrbitRootCriterion
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Universal independent roots on arbitrary complete return-atlas families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.UniversalRootCriterion

open PrimitiveLiftRootCriterion PrimeOrbitRootCriterion FiniteOrbitRootCriterion
universe u v w

/-- Roots of every positive degree need not be coherent. Only finite actual isotypic
classes obstruct them, and their holonomies must admit every positive root. -/
theorem universal_rootability_iff
    {H : Type u} [Group H]
    {ι : Type w} {X : ι → Type v} (A : ∀ i, ReturnAtlas H (X i)) :
    (∀ k : ℕ, 0 < k → ∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧ R^[k] = jointTime A) ↔
    (∀ i, Finite {j // Isotypic A i j} →
      (A i).period = 1 ∧
        ∀ n : ℕ, 0 < n → ∃ b : H, b ^ n = (A i).holonomy) := by
  classical
  constructor
  · intro roots i hfinite
    haveI : Finite {j // Isotypic A i j} := hfinite
    haveI : Nonempty {j // Isotypic A i j} := ⟨⟨i, isotypic_refl A i⟩⟩
    let N := Nat.card {j // Isotypic A i j}
    let d := (A i).period
    have hextract : ∀ n : ℕ, 0 < n → d = 1 ∧ ∃ b : H, b ^ n = (A i).holonomy := by
      intro n hn
      let k := N.factorial * d * n
      have hN : 0 < N := Nat.card_pos
      have hdpos : 0 < d := (A i).positive
      have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos N) hdpos) hn
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
        refine ⟨t * n, ?_⟩
        dsimp only [k]
        rw [ht]
        ring)
      have hnq : n ∣ k / ell := (Nat.dvd_div_iff_mul_dvd hellk).mpr (by
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
      have hbq : b ^ (k / ell) = (A i).holonomy := by
        rw [hm, zpow_neg_one] at hhol
        exact mul_inv_eq_one.mp hhol
      obtain ⟨q, hq⟩ := hnq
      refine ⟨hd, b ^ q, ?_⟩
      rw [← pow_mul, Nat.mul_comm, ← hq, hbq]
    have hperiod := hextract 1 (by omega)
    refine ⟨hperiod.1, ?_⟩
    intro n hn
    exact (hextract n hn).2
  · intro trivial k hk
    apply (arbitrary_root_criterion A hk).mpr
    intro i
    by_cases hfinite : Finite {j // Isotypic A i j}
    · obtain ⟨hd, hroots⟩ := trivial i hfinite
      refine ⟨List.replicate (Nat.card {j // Isotypic A i j}) 1, by simp, ?_⟩
      intro ell hmem
      have hell : ell = 1 := List.eq_of_mem_replicate hmem
      subst ell
      obtain ⟨b, hb⟩ := hroots k hk
      refine ⟨by omega, one_dvd k, ?_⟩
      change Local (k / 1) (A i)
      refine ⟨⟨0, (A i).positive⟩, -1, b, ?_, ?_, ?_⟩
      · rw [← hb]
        exact Commute.self_pow b k
      · simp [hd]
      · simp [hb]
    · haveI : Infinite {j // Isotypic A i j} := not_finite_iff_infinite.mp hfinite
      exact ⟨[], by simp, by simp⟩

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.UniversalRootCriterion
