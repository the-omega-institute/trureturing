/- GID: D5/S3/ConceptDynamics/Attribution/FractionalGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FractionalGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp permutation-equivariant grid budgets with fractional orbit weights. -/

import D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
import D5.S3.Combinatorics.Partitions.CommonBlockWeights
import D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
import D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.FractionalGridSupport

open D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction (law_of_scaled_block_allocations)
open Finset
open scoped Nat
open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.PermutationGrid (Profile)

private theorem reduced_grid_budget_iff {k K b A : ℕ} (two : 2 ≤ k)
    (factor : K * b = k) (apos : 0 < A)
    (coprime : Nat.Coprime b A)
    (divisible : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ (k - 1) * (K * A))
    (n : ℕ) :
    let m := (k - 1) * (K * A)
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile (Fin k) m → S → Fin k), CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * (n + 1)) ↔
      K * A + 1 ≤ (K + 1) * (k + 1)^n := by
  classical
  let m := (k - 1) * (K * A)
  let I := Fin k
  let D := (k - 2)!
  have productPositive : 0 < K * b := factor ▸ (show 0 < k by omega)
  have KPositive : 0 < K := Nat.pos_of_ne_zero (fun h => by simp [h] at productPositive)
  have bPositive : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at productPositive)
  have positive : 0 < m := Nat.mul_pos (by omega) (Nat.mul_pos KPositive apos)
  have cardI : Fintype.card I = k := Fintype.card_fin k
  have fact : k ! = D * (k * (k - 1)) := by
    have pred : (k - 1)! = (k - 1) * D := by
      simpa only [D, show k - 1 - 1 = k - 2 by omega] using
        (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm
    rw [← Nat.mul_factorial_pred (n := k) (by omega), pred]
    ac_rfl
  have scaleEq : b * m = k * (k - 1) * A := by
    dsimp [m]
    rw [← factor]
    ac_rfl
  constructor
  · rintro ⟨S, _, _, w, f, ⟨wp, total, wi, mass, covariance⟩, bound⟩
    have realPos : 0 < (m : ℝ) := by exact_mod_cast positive
    let v (s : S) := (m : ℝ) * w s
    have calibrated (p : Profile I m) (i : I) :
        (∑ s, if f p s = i then v s else 0) = (p.val i : ℝ) := by
      have term (s : S) :
          (if f p s = i then v s else 0) = (m : ℝ) * (if f p s = i then w s else 0) := by
        by_cases h : f p s = i <;> simp [h, v]
      rw [Finset.sum_congr rfl (fun s _ => term s), ← Finset.mul_sum, mass, mul_comm]
      exact div_mul_cancel₀ _ realPos.ne'
    have free := PrimeCycleSeedFreeness.free_of_prime_divisibility
      (fun p hp hpI => divisible p hp (by simpa only [Fintype.card_fin] using hpI)) v
      (fun s => mul_pos realPos (wp s)) f calibrated covariance
    obtain ⟨r, weights, support, norm, rawCover⟩ := weighted_orbit_spectrum (I := I)
      (by simpa only [cardI] using two) free v
      (fun g s => congrArg ((m : ℝ) * ·) (wi g s)) f calibrated covariance
    simp only [I, Fintype.card_fin] at support norm
    have levels : m / (Fintype.card I - 1) + 1 = K * A + 1 := by
      rw [cardI]
      dsimp [m]
      rw [Nat.mul_comm (k - 1), Nat.mul_div_cancel _ (show 0 < k - 1 by omega)]
    have digitCount : Fintype.card I + 1 = k + 1 := congrArg (· + 1) cardI
    have cover (l : Fin (K * A + 1)) : ∃ d : Fin r → Fin (k + 1),
        ∑ j, ((d j).val : ℝ) * weights j = (l.val : ℝ) := by
      obtain ⟨d, eq⟩ := rawCover (Fin.cast levels.symm l)
      exact ⟨fun j => Fin.cast digitCount (d j), eq⟩
    have rPos : 0 < r := by
      by_contra! hz
      have zero : r = 0 := by omega
      subst r
      let level : Fin (K * A + 1) := ⟨1, by
        exact Nat.lt_succ_of_le (Nat.succ_le_of_lt (Nat.mul_pos KPositive (by omega)))⟩
      obtain ⟨d, h⟩ := cover level
      have rhs : (level.val : ℝ) = 1 := by norm_num [level]
      simp [rhs] at h
    obtain ⟨r', rEq⟩ := Nat.exists_eq_succ_of_ne_zero rPos.ne'
    subst r
    have hcard : r' ≤ n := by
      rw [support] at bound
      have le := Nat.le_of_mul_le_mul_left bound (Nat.factorial_pos k)
      omega
    have vTotal : (∑ s, v s) = m := by simp [v, ← Finset.mul_sum, total]
    rw [vTotal] at norm
    have board : (∑ j, weights j) = (A : ℝ) / b := by
      have realFact : ((k ! : ℕ) : ℝ) = (D : ℝ) * ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
        exact_mod_cast fact
      have scaled : (b : ℝ) * (m : ℝ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (A : ℝ) := by
        exact_mod_cast scaleEq
      rw [realFact] at norm
      have dNe : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (k - 2)).ne'
      have kNe : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have prevNe : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
      have bNe : (b : ℝ) ≠ 0 := by exact_mod_cast bPositive.ne'
      apply (eq_div_iff bNe).mpr
      have eq1 : ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) * (∑ j, weights j) = (m : ℝ) := by
        apply mul_left_cancel₀ dNe
        linear_combination norm
      apply mul_left_cancel₀ (mul_ne_zero kNe prevNe)
      linear_combination (b : ℝ) * eq1 + scaled
    let level (l : Fin (K * A + 1)) : ℤ := l.val
    have distinct : Function.Injective level := by
      intro x y neq
      change (x.val : ℤ) = (y.val : ℤ) at neq
      exact Fin.ext (by exact_mod_cast neq)
    have all (l : Fin (K * A + 1)) : ∃ d : Fin (r' + 1) → Fin (k + 1),
        ∑ j, ((d j).val : ℝ) * weights j = (level l : ℝ) := by
      simpa only [level, Int.cast_natCast] using cover l
    have signedCoprime : (A : ℤ).natAbs.Coprime b := by simpa using coprime.symm
    have signedTotal : (∑ j, weights j) = ((A : ℤ) : ℝ) / b := by simpa using board
    have levelBound := D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity.integral_levels_capacity
      bPositive signedCoprime weights signedTotal level distinct all
    have coeff : b + k = (K + 1) * b := by rw [Nat.add_mul, Nat.one_mul, factor]; omega
    rw [coeff, Nat.mul_right_comm (K + 1) b, Nat.mul_comm b] at levelBound
    have capacity := Nat.le_of_mul_le_mul_right levelBound bPositive
    exact capacity.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcard))
  · intro cap
    have reducedCap : K * A + 1 ≤ (K * b.gcd A + 1) * (k + 1)^n := by
      simpa only [show b.gcd A = 1 from coprime, Nat.mul_one] using cap
    obtain ⟨w, total, cover⟩ := D5.S3.Combinatorics.Partitions.CommonBlockWeights.common_fractional_allocations
      (show 0 < k by omega) factor reducedCap
    have weights : k * (k - 1) * (∑ j, w j) = b * m := by rw [total, scaleEq]
    have allocation (t U : ℕ) (tpos : 0 < t) (blocks : k * (t - 1) ≤ U) (x : Fin t → ℕ)
        (balance : k * (k - 1) * (∑ i, x i) = U * m) :
        ∃ a : Fin (n + 1) → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = b * x i) := by
      have leftCoeff : k * (k - 1) = ((k - 1) * K) * b := by
        rw [← factor]
        ac_rfl
      have mass : b * (∑ i, x i) = U * A := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (show 0 < k - 1 by omega) KPositive)
        rw [← Nat.mul_assoc, ← leftCoeff, balance]
        dsimp [m]
        ac_rfl
      exact cover t U (Or.inl tpos) blocks x mass
    obtain ⟨S, fs, action, v, f, pos, total, inv, mass, equiv, card⟩ :=
      law_of_scaled_block_allocations two positive bPositive (dvd_mul_right _ _) w weights allocation
    exact ⟨S, fs, action, v, f, ⟨pos, total, inv, mass, equiv⟩, card⟩

/-- The exact budget on the complete grid of denominator `(k - 1) * q` is
controlled by the gcd of the tied-level range parameter and the label count. -/
theorem fractional_grid_budget_iff {k q : ℕ} (two : 2 ≤ k) (positive : 0 < q)
    (divisible : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ (k - 1) * q)
    (n : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile (Fin k) ((k - 1) * q) → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * (n + 1)) ↔
      q + 1 ≤ (k.gcd q + 1) * (k + 1)^n := by
  obtain ⟨b, A, coprime, k_eq, q_eq⟩ := Nat.exists_coprime k q
  have factor : k.gcd q * b = k := (Nat.mul_comm _ _).trans k_eq.symm
  have numer : k.gcd q * A = q := (Nat.mul_comm _ _).trans q_eq.symm
  have apos : 0 < A := Nat.pos_of_ne_zero fun zero => by
    rw [zero, Nat.mul_zero] at numer
    exact positive.ne' numer.symm
  let feasible (t : ℕ) : Prop :=
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile (Fin k) ((k - 1) * t) → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * (n + 1)) ↔
      t + 1 ≤ (k.gcd q + 1) * (k + 1)^n
  have reduced : feasible (k.gcd q * A) :=
    reduced_grid_budget_iff two factor apos coprime (by simpa only [numer] using divisible) n
  exact Eq.mp (congrArg feasible numer) reduced

end D5.S3.ConceptDynamics.Attribution.FractionalGridSupport
