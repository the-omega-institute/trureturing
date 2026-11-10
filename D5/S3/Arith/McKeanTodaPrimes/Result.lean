/- GID: D5/S3/Arith/McKeanTodaPrimes/Result
   generality: G
   mirror-B: D5/B/S3/Arith/McKeanTodaPrimes/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/McKeanTodaPrimes/Result.claim; result=D5/S3/Arith/McKeanTodaPrimes/Result.result; claim=D5/S3/Arith/McKeanTodaPrimes/Result.claim
   digest: Both Bernoulli-denominator assertions about Toda primes are false. -/

/-
admission_basis: open-problem-resolution (#22475; Refuted)
No frozen D5 dependencies: the mathematical imports are pinned Mathlib.
Per declaration: name | proof_shape | escape_witness | consumers.
  todaPrimes | bind-only (definition) | none | t, clauseI, todaReduction, family,
    witnessII, refuteI, refuteII
  t | bind-only (definition) | none | clauseII, refuteII
  bernDen | bind-only (definition) | none | clauseI, clauseII, denominatorFormula,
    primeDenIff, familyMinimum, family, witnessII, refuteI, refuteII
  denominatorPrimes | bind-only (definition) | none | memDenominatorPrimes,
    denominatorFormula, todaReduction, familyPrimeSets, primeDenIff, family, witnessII
  clauseI | bind-only (definition) | none | claim, refuteI, refutedClauses, result
  clauseII | bind-only (definition) | none | claim, refuteII, refutedClauses, result
  claim | bind-only (definition) | none | result
  memDenominatorPrimes | bind-only | none | denominatorFormula, todaReduction,
    familyPrimeSets, primeDenIff
  denominatorFormula | bind-only | none | primeDenIff, family, witnessII
  todaReduction | bind-only | none | family
  compositeByMod | bind-only | none | familyCandidates
  familyCandidates | bind-only | none | familyPrimeSets
  familyPrimeSets | bind-only | none | family
  primeDenIff | bind-only | none | familyMinimum
  familyMinimum | bind-only | none | family
  family | bind-only | none | refuteI
  witnessII | bind-only | none | refuteII
  refuteI | bind-only | none | refutedClauses
  refuteII | bind-only | none | refutedClauses
  refutedClauses | bind-only | none | result
  result | bind-only | none | settling result
Bypass test: the denominator product uses Bernoulli.vonStaudt_clausen,
Finset.Rat.den_sum_dvd_prod_den, Bernoulli.dvd_den_bernoulli, Nat.coprime_primes
and Finset.prod_dvd_of_isRelPrime. The Toda reduction uses
Nat.not_dvd_of_pos_of_lt, Nat.prime_eq_prime_of_dvd_pow,
Nat.Prime.dvd_mul, Nat.Prime.coprime_iff_not_dvd and Nat.mul_div_cancel'.
The conditional family uses exists_dvd_and_dvd_of_dvd_mul,
Nat.dvd_prime_pow and Nat.not_prime_of_dvd_of_lt; its successor cases
and first-index bound normalize the supplied divisibility and residue facts.
The finite prime sets use kernel reduction. Both refutations instantiate
these facts. No declaration supplies an escape witness.
The conditional family does not assert infinitude of the prime pairs.
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity

/-! Bernoulli denominators and two counterexamples for Toda primes. -/

open Finset
namespace D5.S3.Arith.McKeanTodaPrimes.Result

def todaPrimes (n : ℕ) : Finset ℕ :=
  (range (4 * n + 2)).filter fun p =>
    p.Prime ∧ Odd p ∧ p - 1 ∣ 4 * n ∧ Nat.Coprime p (4 * n / (p - 1))

def t (n : ℕ) : ℕ := (todaPrimes n).card

def bernDen (k : ℕ) : ℕ := (bernoulli k).den

def denominatorPrimes (k : ℕ) : Finset ℕ :=
  (range (k + 2)).filter fun p => p.Prime ∧ p - 1 ∣ k

def clauseI : Prop := ∀ a m : ℕ, 0 < a → 0 < m →
  (∀ k, 0 < k → Even k → k < 4 * a → bernDen k ≠ bernDen (4 * a)) →
  bernDen (4 * a * m) = bernDen (4 * a) → todaPrimes (a * m) = todaPrimes a

def clauseII : Prop := ∀ a m : ℕ, 0 < a → 0 < m →
  bernDen (4 * a * m) ≠ bernDen (4 * a) → t a ≤ t (a * m)

def claim : Prop := clauseI ∧ clauseII

private theorem memDenominatorPrimes {k p : ℕ} (hk : 0 < k) :
    p ∈ denominatorPrimes k ↔ p.Prime ∧ p - 1 ∣ k := by
  simp only [denominatorPrimes, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hp, hd⟩
    have := Nat.le_of_dvd hk hd
    exact ⟨by omega, hp, hd⟩

theorem denominatorFormula (k : ℕ) (hk : 0 < k) :
    bernDen (2 * k) = ∏ p ∈ denominatorPrimes (2 * k), p := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  apply Nat.dvd_antisymm
  · have hb : bernoulli (2 * k) =
        (z : ℚ) - ∑ p ∈ denominatorPrimes (2 * k), (1 : ℚ) / p := by
      change (z : ℚ) = bernoulli (2 * k) +
        ∑ p ∈ denominatorPrimes (2 * k), (1 : ℚ) / p at hz
      exact eq_sub_of_add_eq hz.symm
    rw [bernDen, hb, Rat.intCast_sub_den]
    apply (Rat.den_sum_dvd_prod_den _ _).trans
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    simp only [one_div, Rat.inv_natCast_den_of_pos
      ((memDenominatorPrimes (Nat.succ_mul_pos 1 hk)).mp hp).1.pos]
    exact dvd_rfl
  · apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes
        ((memDenominatorPrimes (Nat.succ_mul_pos 1 hk)).mp hp).1
        ((memDenominatorPrimes (Nat.succ_mul_pos 1 hk)).mp hq).1).mpr hpq
    · intro p hp
      obtain ⟨hprime, hd⟩ := (memDenominatorPrimes (Nat.succ_mul_pos 1 hk)).mp hp
      have : Fact p.Prime := ⟨hprime⟩
      exact Bernoulli.dvd_den_bernoulli hk hd

theorem todaReduction (n : ℕ) (hn : 0 < n) :
    todaPrimes n = (denominatorPrimes (4 * n)).filter fun p => Odd p ∧ ¬p ∣ n := by
  ext p
  simp only [todaPrimes, mem_filter, mem_range]
  rw [memDenominatorPrimes (Nat.succ_mul_pos 3 hn)]
  constructor
  · rintro ⟨hr, hp, ho, hd, hc⟩
    have hp2 := hp.two_le
    refine ⟨⟨hp, hd⟩, ho, ?_⟩
    intro hpn
    have hpred : ¬ p ∣ p - 1 :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hprod : p ∣ (p - 1) * (4 * n / (p - 1)) := by
      rw [Nat.mul_div_cancel' hd]
      exact dvd_mul_of_dvd_right hpn 4
    exact (hp.coprime_iff_not_dvd.mp hc) ((hp.dvd_mul.mp hprod).resolve_left hpred)
  · rintro ⟨⟨hp, hd⟩, ho, hpn⟩
    have hp4 : ¬ p ∣ 4 := by
      intro h
      have heq : p = 2 :=
        Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two
          (show p ∣ 2 ^ 2 by simpa using h)
      subst p
      norm_num at ho
    refine ⟨by have := Nat.le_of_dvd (Nat.succ_mul_pos 3 hn) hd; omega,
      hp, ho, hd, hp.coprime_iff_not_dvd.mpr ?_⟩
    intro h
    have : p ∣ 4 * n := h.trans (Nat.div_dvd_of_dvd hd)
    exact hpn ((hp.dvd_mul.mp this).resolve_left hp4)

private theorem compositeByMod {q c : ℕ} (hc : 1 < c) (hlt : c < q)
    (hmod : q % c = 0) : ¬q.Prime := by
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) (Nat.succ_le_of_lt hc) hlt

private theorem familyCandidates {a q : ℕ} (ha : a.Prime) (ham : a % 30 = 23)
    (hp : (2 * a + 1).Prime) (hq : q.Prime) (hd : q - 1 ∣ 4 * a * (2 * a + 1)) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 2 * a + 1 := by
  have ha23 : 23 ≤ a := ham ▸ Nat.mod_le a 30
  obtain ⟨x, z, hx, hz, he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨u, v, hu, hv, hxv⟩ := exists_dvd_and_dvd_of_dvd_mul hx
  have hu' : u = 1 ∨ u = 2 ∨ u = 4 := by
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show u ∣ 2 ^ 2 by simpa using hu)
    interval_cases j <;> norm_num
  have hv' := ha.eq_one_or_self_of_dvd v hv
  have hz' := hp.eq_one_or_self_of_dvd z hz
  have ha2 : a % 2 = 1 := by omega
  have ha3 : a % 3 = 2 := by omega
  have ha5 : a % 5 = 3 := by omega
  rw [hxv] at he
  rcases hu' with rfl | rfl | rfl <;>
    rcases hv' with rfl | rfl <;> rcases hz' with rfl | rfl <;>
    try simp only [one_mul, mul_one] at he
  all_goals try omega
  all_goals exfalso
  all_goals have hqe : q = (q - 1) + 1 :=
    (Nat.sub_add_cancel hq.one_le).symm
  all_goals rw [he] at hqe
  all_goals subst q
  all_goals first
    | solve
      | refine compositeByMod (c := 2) (by omega) ?_ ?_ hq
        · nlinarith
        · norm_num [Nat.add_mod, Nat.mul_mod, ha2]
    | solve
      | refine compositeByMod (c := 3) (by omega) ?_ ?_ hq
        · nlinarith
        · norm_num [Nat.add_mod, Nat.mul_mod, ha3]
    | solve
      | refine compositeByMod (c := 5) (by omega) ?_ ?_ hq
        · nlinarith
        · norm_num [Nat.add_mod, Nat.mul_mod, ha5]

private theorem familyPrimeSets {a : ℕ} (ha : a.Prime) (ham : a % 30 = 23)
    (hp : (2 * a + 1).Prime) :
    denominatorPrimes (4 * a) = {2, 3, 5, 2 * a + 1} ∧
    denominatorPrimes (4 * a * (2 * a + 1)) = {2, 3, 5, 2 * a + 1} := by
  have ha23 : 23 ≤ a := ham ▸ Nat.mod_le a 30
  have hlarge : denominatorPrimes (4 * a * (2 * a + 1)) =
      {2, 3, 5, 2 * a + 1} := by
    ext q
    rw [memDenominatorPrimes (by positivity)]
    simp only [mem_insert, mem_singleton]
    constructor
    · exact fun h => familyCandidates ha ham hp h.1 h.2
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨Nat.prime_two, by simp⟩
      · exact ⟨Nat.prime_three, by
          simpa using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) a) (2 * a + 1)⟩
      · exact ⟨Nat.prime_five, by simpa [mul_assoc] using dvd_mul_right 4 (a * (2 * a + 1))⟩
      · exact ⟨hp, by
          simpa using dvd_mul_of_dvd_left (Nat.mul_dvd_mul_right (by decide : 2 ∣ 4) a) (2 * a + 1)⟩
  refine ⟨?_, hlarge⟩
  ext q
  rw [memDenominatorPrimes (by positivity)]
  simp only [mem_insert, mem_singleton]
  constructor
  · intro h
    exact familyCandidates ha ham hp h.1 (dvd_mul_of_dvd_left h.2 _)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Nat.prime_two, by simp⟩
    · exact ⟨Nat.prime_three, by simpa using dvd_mul_of_dvd_left (by decide : 2 ∣ 4) a⟩
    · exact ⟨Nat.prime_five, by simpa using dvd_mul_right 4 a⟩
    · exact ⟨hp, by simpa using Nat.mul_dvd_mul_right (by decide : 2 ∣ 4) a⟩

private theorem primeDenIff {k p : ℕ} (hk : 0 < k) (he : Even k) (hp : p.Prime) :
    p ∣ bernDen k ↔ p - 1 ∣ k := by
  obtain ⟨j, rfl⟩ := he
  rw [← two_mul j, denominatorFormula j (by omega)]
  constructor
  · intro hd
    obtain ⟨q, hq, hdq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    obtain ⟨hqprime, hqd⟩ := (memDenominatorPrimes (by omega)).mp hq
    have hpq := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hdq
    simpa [← hpq] using hqd
  · intro hd
    exact dvd_prod_of_mem id ((memDenominatorPrimes (by omega)).mpr ⟨hp, hd⟩)

private theorem familyMinimum {a : ℕ} (ha : a.Prime) (ham : a % 30 = 23)
    (hp : (2 * a + 1).Prime) :
    ∀ k, 0 < k → Even k → bernDen k = 30 * (2 * a + 1) → 4 * a ≤ k := by
  intro k hk he hd
  have h4 : 4 ∣ k := (primeDenIff hk he Nat.prime_five).mp
    (by rw [hd]; exact dvd_mul_of_dvd_left (by decide : 5 ∣ 30) _)
  have h2a : 2 * a ∣ k := by
    simpa using (primeDenIff hk he hp).mp (by rw [hd]; exact dvd_mul_left _ _)
  obtain ⟨r, hr⟩ := h2a
  have ha2 : a % 2 = 1 := by omega
  have hkr : k = 2 * (a * r) := by simpa only [Nat.mul_assoc] using hr
  have har : (a * r) % 2 = 0 := by
    exact Nat.mod_eq_zero_of_dvd
      ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp (hkr ▸ h4))
  have hr2 : r % 2 = 0 := by simpa [Nat.mul_mod, ha2] using har
  have hapos := ha.pos
  have hrpos : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ hk)
  have : 2 ≤ r := Nat.le_of_dvd hrpos (Nat.dvd_of_mod_eq_zero hr2)
  nlinarith

theorem family (a : ℕ) (ha : a.Prime) (ham : a % 30 = 23)
    (hp : (2 * a + 1).Prime) :
    bernDen (4 * a) = 30 * (2 * a + 1) ∧
    bernDen (4 * a * (2 * a + 1)) = 30 * (2 * a + 1) ∧
    (∀ k, 0 < k → Even k → k < 4 * a → bernDen k ≠ 30 * (2 * a + 1)) ∧
    todaPrimes a = {3, 5, 2 * a + 1} ∧
    todaPrimes (a * (2 * a + 1)) = {3, 5} := by
  have ha23 : 23 ≤ a := ham ▸ Nat.mod_le a 30
  obtain ⟨hs, hl⟩ := familyPrimeSets ha ham hp
  have hb : bernDen (4 * a) = 30 * (2 * a + 1) := by
    rw [show 4 * a = 2 * (2 * a) from mul_assoc 2 2 a,
      denominatorFormula _ (by omega)]
    rw [show 2 * (2 * a) = 4 * a from (mul_assoc 2 2 a).symm, hs]
    simp [show (2 : ℕ) ≠ 2 * a + 1 by omega, show (3 : ℕ) ≠ 2 * a + 1 by omega,
      show (5 : ℕ) ≠ 2 * a + 1 by omega]; ring
  have hbl : bernDen (4 * a * (2 * a + 1)) = 30 * (2 * a + 1) := by
    rw [show 4 * a * (2 * a + 1) = 2 * (2 * a * (2 * a + 1)) by
      simp only [← mul_assoc]; rfl,
      denominatorFormula _ (by positivity)]
    rw [show 2 * (2 * a * (2 * a + 1)) = 4 * a * (2 * a + 1) by
      simp only [← mul_assoc]; rfl, hl]
    simp [show (2 : ℕ) ≠ 2 * a + 1 by omega, show (3 : ℕ) ≠ 2 * a + 1 by omega,
      show (5 : ℕ) ≠ 2 * a + 1 by omega]; ring
  refine ⟨hb, hbl, ?_, ?_, ?_⟩
  · intro k hk he hlt hden
    exact (not_le_of_gt hlt) (familyMinimum ha ham hp k hk he hden)
  · rw [todaReduction a (by omega), hs]
    have ha3 : ¬3 ∣ a := by omega
    have ha5 : ¬5 ∣ a := by omega
    have hpa : ¬2 * a + 1 ∣ a :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hop : Odd (2 * a + 1) := odd_two_mul_add_one a
    norm_num [filter_insert, filter_singleton, ha3, ha5, hpa, hop]
  · rw [todaReduction _ (by positivity), show 4 * (a * (2 * a + 1)) =
      4 * a * (2 * a + 1) from (mul_assoc 4 a (2 * a + 1)).symm, hl]
    have ha3 : ¬3 ∣ a * (2 * a + 1) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have ha3m : a % 3 = 2 := by omega
      simp [Nat.mul_mod, Nat.add_mod, ha3m]
    have ha5 : ¬5 ∣ a * (2 * a + 1) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have ha5m : a % 5 = 3 := by omega
      simp [Nat.mul_mod, Nat.add_mod, ha5m]
    norm_num [filter_insert, filter_singleton, ha3, ha5]

private theorem witnessII :
    bernDen 44 = 690 ∧ bernDen 220 = 7590 ∧
      todaPrimes 11 = {3, 5, 23} ∧ todaPrimes 55 = {3, 23} := by
  have h44 : denominatorPrimes 44 = {2, 3, 5, 23} := by decide +kernel
  have h220 : denominatorPrimes 220 = {2, 3, 5, 11, 23} := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 44 = 2 * 22 by rfl, denominatorFormula 22 (by omega), h44]
    norm_num
  · rw [show 220 = 2 * 110 by rfl, denominatorFormula 110 (by omega), h220]
    norm_num
  · decide +kernel
  · decide +kernel

private theorem refuteI : ¬clauseI := by
  intro hc
  obtain ⟨hb, hl, hm, ht, htl⟩ := family 23 (by norm_num) (by norm_num) (by norm_num)
  have h := hc 23 47 (by omega) (by omega) (by simpa [hb] using hm)
    (by simpa using hl.trans hb.symm)
  rw [show 23 * 47 = 23 * (2 * 23 + 1) by rfl, htl, ht] at h
  have : (47 : ℕ) ∈ ({3, 5} : Finset ℕ) := by rw [h]; norm_num
  norm_num at this

private theorem refuteII : ¬clauseII := by
  intro hc
  obtain ⟨h44, h220, h11, h55⟩ := witnessII
  have h := hc 11 5 (by omega) (by omega) (by norm_num [h44, h220])
  norm_num [t, h11, h55] at h

theorem refutedClauses : ¬clauseI ∧ ¬clauseII := ⟨refuteI, refuteII⟩

theorem result : ¬ claim := by
  classical
  intro hc
  by_cases hi : clauseI
  · exact refutedClauses.1 hi
  · exact refutedClauses.2 hc.2

end D5.S3.Arith.McKeanTodaPrimes.Result
