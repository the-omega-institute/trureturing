/- GID: D5/S3/Analytic/Dilation/EquivariantSeriesObserver
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/EquivariantSeriesObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recovery of positive bivariate class-function series is equivalent to power closure. -/

import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Algebra.Group.Conj
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.EquivariantSeriesObserver

open scoped BigOperators

variable {G K : Type*} [Group G] [Field K] [CharZero K]

abbrev Series (G K : Type*) := G → MvPowerSeries (Fin 2) K

noncomputable def exponent (m n : ℕ) : Fin 2 →₀ ℕ :=
  (finTwoArrowEquiv' ℕ).symm (m, n)

def Positive (H : Series G K) : Prop :=
  ∀ g d, d 0 = 0 ∨ d 1 = 0 → H g d = 0

def ClassInvariant (H : Series G K) : Prop :=
  ∀ g h, IsConj g h → H g = H h

def conjugacySaturation (S : Set G) : Set G :=
  {g | ∃ s ∈ S, IsConj s g}

def PowerClosed (S : Set G) : Prop :=
  ∀ g ∈ S, ∀ n : ℕ, 0 < n → g ^ n ∈ S

noncomputable def logarithmicHistory (H : Series G K) : Series G K :=
  fun g d => if 0 < d 0 ∧ 0 < d 1 then
    ∑ k ∈ (Nat.gcd (d 0) (d 1)).divisors,
      H (g ^ k) (exponent (d 0 / k) (d 1 / k)) / (k : K)
  else 0

private noncomputable def hiddenPrimitive (u : G) : Series G K := by
  classical
  exact fun g d => if d 0 = d 1 ∧ IsConj (g ^ d 0) u then
    (ArithmeticFunction.moebius (d 0) : K) / (d 0 : K)
  else 0

theorem observed_recovery_iff_power_closed (S : Set G) :
    (∀ H₁ H₂ : Series G K,
      Positive H₁ → Positive H₂ → ClassInvariant H₁ → ClassInvariant H₂ →
      Set.EqOn (logarithmicHistory H₁) (logarithmicHistory H₂) S →
      Set.EqOn H₁ H₂ S) ↔ PowerClosed (conjugacySaturation S) := by
  classical
  have hiddenPrimitive_history : ∀ (u g : G) (d : Fin 2 →₀ ℕ),
    logarithmicHistory (hiddenPrimitive u : Series G K) g d =
      if d 0 = 1 ∧ d 1 = 1 ∧ IsConj g u then 1 else 0 := by
    intro u g d
    by_cases hpos : 0 < d 0 ∧ 0 < d 1
    · rw [logarithmicHistory, if_pos hpos]
      by_cases hdiag : d 0 = d 1
      · rw [← hdiag, Nat.gcd_self]
        have hterm : ∀ k ∈ (d 0).divisors,
          hiddenPrimitive (K := K) u (g ^ k) (exponent (d 0 / k) (d 0 / k)) /
              (k : K) =
            (ArithmeticFunction.moebius (d 0 / k) : K) / (d 0 : K) *
              (if IsConj (g ^ d 0) u then 1 else 0) := by
          intro k hk
          have hkdvd := Nat.dvd_of_mem_divisors hk
          have hk0 : (k : K) ≠ 0 := by
            exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
          have hdiv : k * (d 0 / k) = d 0 := Nat.mul_div_cancel' hkdvd
          have he0 : exponent (d 0 / k) (d 0 / k) 0 = d 0 / k := by simp [exponent]
          have he1 : exponent (d 0 / k) (d 0 / k) 1 = d 0 / k := by simp [exponent]
          simp only [hiddenPrimitive, he0, he1, eq_self, true_and, ← pow_mul, hdiv]
          split_ifs <;> simp only [mul_one, mul_zero, zero_div]
          rw [div_div, ← Nat.cast_mul, Nat.mul_comm (d 0 / k) k, hdiv]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div,
          Nat.sum_div_divisors (d 0) (fun n => (ArithmeticFunction.moebius n : K))]
        have hmu : (∑ k ∈ (d 0).divisors, (ArithmeticFunction.moebius k : K)) =
            if d 0 = 1 then 1 else 0 := by
          have h := congrArg (fun f : ArithmeticFunction K => f (d 0))
            (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := K))
          simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
            ArithmeticFunction.one_apply] using h
        rw [hmu]
        by_cases h1 : d 0 = 1
        · simp [h1]
        · simp [h1]
      · have hterm : ∀ k ∈ (Nat.gcd (d 0) (d 1)).divisors,
          hiddenPrimitive (K := K) u (g ^ k) (exponent (d 0 / k) (d 1 / k)) /
            (k : K) = 0 := by
          intro k hk
          have hkm : k ∣ d 0 := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_left _ _)
          have hkn : k ∣ d 1 := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_right _ _)
          have hne : d 0 / k ≠ d 1 / k := by
            intro heq
            apply hdiag
            calc
              d 0 = k * (d 0 / k) := (Nat.mul_div_cancel' hkm).symm
              _ = k * (d 1 / k) := congrArg (k * ·) heq
              _ = d 1 := Nat.mul_div_cancel' hkn
          simp [hiddenPrimitive, exponent, hne]
        rw [Finset.sum_eq_zero hterm]
        split_ifs with h
        · exact (hdiag (h.1.trans h.2.1.symm)).elim
        · rfl
    · rw [logarithmicHistory, if_neg hpos]
      split_ifs with h
      · exact (hpos (by simp [h.1, h.2.1])).elim
      · rfl
  constructor
  · intro hdecode
    have hprime : ∀ h ∈ conjugacySaturation S, ∀ p : ℕ,
        p.Prime → h ^ p ∈ conjugacySaturation S := by
      intro h hh p hp
      by_contra hhidden
      obtain ⟨s, hs, hsh⟩ := hh
      let H : Series G K := hiddenPrimitive (h ^ p)
      have hpositive : Positive H := by
        intro g d hd
        rcases hd with hd | hd
        · simp [H, hiddenPrimitive, hd]
        · by_cases hdiag : d 0 = d 1
          · simp [H, hiddenPrimitive, hdiag, hd]
          · simp [H, hiddenPrimitive, hdiag]
      have hclass : ClassInvariant H := by
        intro g g' hgg'
        funext d
        have hc : IsConj (g ^ d 0) (h ^ p) ↔ IsConj (g' ^ d 0) (h ^ p) :=
          ⟨fun hc => (hgg'.pow (d 0)).symm.trans hc,
            fun hc => (hgg'.pow (d 0)).trans hc⟩
        simp only [H, hiddenPrimitive, hc]
      have hhistory : Set.EqOn (logarithmicHistory H)
          (logarithmicHistory (fun _ => 0)) S := by
        intro t ht
        funext d
        have htu : ¬IsConj t (h ^ p) := by
          intro htu
          exact hhidden ⟨t, ht, htu⟩
        change logarithmicHistory (hiddenPrimitive (h ^ p) : Series G K) t d = _
        rw [hiddenPrimitive_history]
        simp only [htu, and_false, if_false, logarithmicHistory]
        change 0 = if 0 < d 0 ∧ 0 < d 1 then
          ∑ k ∈ (Nat.gcd (d 0) (d 1)).divisors, (0 : K) / (k : K) else 0
        simp
      have heq := hdecode H (fun _ => 0) hpositive
        (by intro g d hd; rfl) hclass (by intro g g' hgg'; rfl) hhistory hs
      have hcoeff := congrArg (fun F : MvPowerSeries (Fin 2) K => F (exponent p p)) heq
      have hc : IsConj (s ^ p) (h ^ p) := hsh.pow p
      have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
      change hiddenPrimitive (K := K) (h ^ p) s (exponent p p) = 0 at hcoeff
      have he0 : exponent p p 0 = p := by simp [exponent]
      have he1 : exponent p p 1 = p := by simp [exponent]
      simp only [hiddenPrimitive, he0, he1, eq_self, true_and, if_pos hc,
        ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one] at hcoeff
      exact (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hpK) hcoeff
    intro g hg n hn
    induction n using Nat.strong_induction_on generalizing g with
    | h n ih =>
      by_cases h1 : n = 1
      · simpa [h1] using hg
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      have hmul : n / p * p = n := Nat.div_mul_cancel hpn
      have hquot : 0 < n / p := by nlinarith [hp.pos]
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      have hin := ih (n / p) hlt g hg hquot
      simpa only [← pow_mul, hmul] using hprime (g ^ (n / p)) hin p hp
  · intro hclosed H₁ H₂ hpos₁ hpos₂ hclass₁ hclass₂ hhistory
    have hhistoryC : Set.EqOn (logarithmicHistory H₁)
        (logarithmicHistory H₂) (conjugacySaturation S) := by
      intro g hg
      obtain ⟨s, hs, hsg⟩ := hg
      have hconj : ∀ H : Series G K, ClassInvariant H →
          logarithmicHistory H s = logarithmicHistory H g := by
        intro H hclass
        funext d
        unfold logarithmicHistory
        split_ifs
        · exact Finset.sum_congr rfl fun k hk =>
            congrArg (fun F : MvPowerSeries (Fin 2) K =>
              F (exponent (d 0 / k) (d 1 / k)) / (k : K))
                (hclass _ _ (hsg.pow k))
        · rfl
      exact (hconj H₁ hclass₁).symm.trans ((hhistory hs).trans (hconj H₂ hclass₂))
    have hcoeff : ∀ m : ℕ, ∀ n : ℕ, 0 < m → 0 < n →
        ∀ g ∈ conjugacySaturation S, H₁ g (exponent m n) = H₂ g (exponent m n) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro n hm hn g hg
        have he0 : exponent m n 0 = m := by simp [exponent]
        have he1 : exponent m n 1 = n := by simp [exponent]
        have hsum := congrArg
          (fun F : MvPowerSeries (Fin 2) K => F (exponent m n)) (hhistoryC hg)
        simp only [logarithmicHistory, he0, he1,
          if_pos (show 0 < m ∧ 0 < n from ⟨hm, hn⟩)] at hsum
        have h1mem : 1 ∈ (Nat.gcd m n).divisors :=
          Nat.one_mem_divisors.mpr (Nat.gcd_pos_of_pos_left n hm).ne'
        have hrest : ∀ k ∈ (Nat.gcd m n).divisors.erase 1,
            H₁ (g ^ k) (exponent (m / k) (n / k)) / (k : K) =
              H₂ (g ^ k) (exponent (m / k) (n / k)) / (k : K) := by
          intro k hk
          obtain ⟨hk1, hk⟩ := Finset.mem_erase.mp hk
          have hkpos := Nat.pos_of_mem_divisors hk
          have hk2 : 1 < k := by omega
          have hkm : k ∣ m := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_left _ _)
          have hkn : k ∣ n := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_right _ _)
          have hmp : 0 < m / k := Nat.div_pos (Nat.le_of_dvd hm hkm) hkpos
          have hnp : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hn hkn) hkpos
          exact congrArg (fun x : K => x / (k : K))
            (ih (m / k) (Nat.div_lt_self hm hk2) (n / k) hmp hnp
              (g ^ k) (hclosed g hg k hkpos))
        rw [← Finset.sum_erase_add _ _ h1mem, ← Finset.sum_erase_add _ _ h1mem,
          Finset.sum_congr rfl hrest] at hsum
        simpa using add_left_cancel hsum
    intro g hg
    funext d
    by_cases hd : d 0 = 0 ∨ d 1 = 0
    · rw [hpos₁ g d hd, hpos₂ g d hd]
    · have h0 : 0 < d 0 := by omega
      have h1 : 0 < d 1 := by omega
      have hexp : exponent (d 0) (d 1) = d := by
        apply (finTwoArrowEquiv' ℕ).injective
        simp [exponent]
      rw [← hexp]
      exact hcoeff (d 0) (d 1) h0 h1 g ⟨g, hg, IsConj.refl g⟩

#print axioms observed_recovery_iff_power_closed

end D5.S3.Analytic.Dilation.EquivariantSeriesObserver
