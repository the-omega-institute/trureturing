/- GID: D5/S3/Arith/StechkinFunctionDivisorCount
   generality: I
   mirror-B: D5/B/S3/Arith/StechkinFunctionDivisorCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: For n at least two, the Stechkin function plus two equals two adjacent divisor counts. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.StechkinFunctionDivisorCount

/-- The number of source-admissible indices in the interval from two through `n`. -/
def stechkinFunction (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter (fun m => (m - 1) ∣ n * (m - 1) / m)).card

private theorem stechkin_divisibility_iff {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    k ∣ n * k / (k + 1) ↔ (k + 1) ∣ n ∨ (k + 1) ∣ (n - 1) := by
  have hkpos : 0 < k := by omega
  let d := k + 1
  let q := n / d
  let r := n % d
  have hdpos : 0 < d := by dsimp [d]; omega
  have hkd : k < d := by dsimp [d]; omega
  have hrepr : r + d * q = n := by
    dsimp [r, q]
    exact Nat.mod_add_div n d
  have hdecomp : n * k / d = q * k + r * k / d := by
    rw [← hrepr]
    calc
      (r + d * q) * k / d = (r * k + d * (q * k)) / d := by ring_nf
      _ = r * k / d + q * k := Nat.add_mul_div_left (r * k) (q * k) hdpos
      _ = q * k + r * k / d := by omega
  have hrt_lt : r * k / d < k := by
    apply (Nat.div_lt_iff_lt_mul hdpos).2
    have hrlt : r < d := by
      dsimp [r, d]
      exact Nat.mod_lt n (by omega)
    have hmul := Nat.mul_lt_mul_of_pos_right hrlt hkpos
    simpa [Nat.mul_comm] using hmul
  have hr_zero_or_one_of_dvd : k ∣ r * k / d → r = 0 ∨ r = 1 := by
    intro hdiv
    have hzero : r * k / d = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hrt_lt
    have hrsmall : r * k < d := (Nat.div_eq_zero_iff.mp hzero).resolve_left (by omega)
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · right
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hrle : r * k ≤ k := by
        have : r * k < k + 1 := by simpa [d] using hrsmall
        omega
      have hr_le_one : r ≤ 1 := by
        apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using hrle) hkpos
      omega
  have hr_zero_of_dvd_n : (k + 1) ∣ n → r = 0 := by
    intro hd
    have hm : n % d = 0 := Nat.mod_eq_zero_of_dvd (by simpa [d] using hd)
    simpa [r] using hm
  have hr_one_of_dvd_pred : (k + 1) ∣ (n - 1) → r = 1 := by
    intro hd
    have hnm : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hm : (n - 1) % d = 0 := Nat.mod_eq_zero_of_dvd (by simpa [d] using hd)
    have hmodone : n % d = 1 := by
      rw [← hnm, Nat.add_mod, hm]
      have hone : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
      simp [hone]
    simpa [r] using hmodone
  have hdvd_n_of_hr_zero : r = 0 → (k + 1) ∣ n := by
    intro hr0
    apply Nat.dvd_of_mod_eq_zero
    simpa [r, d] using hr0
  have hdvd_pred_of_hr_one : r = 1 → (k + 1) ∣ (n - 1) := by
    intro hr1
    have hdecomp' : n = d * q + 1 := by
      calc
        n = r + d * q := hrepr.symm
        _ = d * q + 1 := by simp [hr1, Nat.add_comm]
    have hpred : n - 1 = d * q := by omega
    rw [hpred]
    exact dvd_mul_right d q
  constructor
  · intro hdiv
    have hsum : k ∣ q * k + r * k / d := by
      have hdiv' : k ∣ n * k / d := by simpa [d] using hdiv
      rw [hdecomp] at hdiv'
      exact hdiv'
    have hrem : k ∣ r * k / d :=
      (Nat.dvd_add_iff_right (Nat.dvd_mul_left k q)).2 hsum
    rcases hr_zero_or_one_of_dvd hrem with hr0 | hr1
    · exact Or.inl (by simpa [d] using hdvd_n_of_hr_zero hr0)
    · exact Or.inr (by simpa [d] using hdvd_pred_of_hr_one hr1)
  · intro hrhs
    have hr : r = 0 ∨ r = 1 := hrhs.elim (fun h => Or.inl (hr_zero_of_dvd_n h))
      (fun h => Or.inr (hr_one_of_dvd_pred h))
    rw [hdecomp]
    rcases hr with hr0 | hr1
    · have hzero : r * k / d = 0 := by simp [hr0]
      rw [hzero]
      exact Nat.dvd_mul_left k q
    · have hzero : r * k / d = 0 := by
        rw [hr1]
        apply Nat.div_eq_of_lt
        simpa using hkd
      rw [hzero]
      exact Nat.dvd_mul_left k q

/-- Oudra's formula for the Boris Stechkin function. -/
theorem result (n : ℕ) (hn : 2 ≤ n) :
    stechkinFunction n + 2 = n.divisors.card + (n - 1).divisors.card := by
  have hn0 : n ≠ 0 := by omega
  have hn10 : n - 1 ≠ 0 := by omega
  let source := (Finset.Icc 2 n).filter
    (fun m => (m - 1) ∣ n * (m - 1) / m)
  let leftDivisors := n.divisors.erase 1
  let rightDivisors := (n - 1).divisors.erase 1
  have hsource : source = leftDivisors ∪ rightDivisors := by
    ext m
    simp only [source, leftDivisors, rightDivisors, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_union, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hm2, hmn⟩, hp⟩
      have hp' : (m - 1) ∣ n * (m - 1) / (m - 1 + 1) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hp
      have hchar :=
        (stechkin_divisibility_iff (n := n) (k := m - 1) (by omega) (by omega)).1 hp'
      have hrewrite : m - 1 + 1 = m := by omega
      rw [hrewrite] at hchar
      rcases hchar with hmnDvd | hpredDvd
      · exact Or.inl ⟨by omega, hmnDvd, hn0⟩
      · exact Or.inr ⟨by omega, hpredDvd, hn10⟩
    · intro hmem
      have hmpos : 2 ≤ m := by
        rcases hmem with hmem | hmem
        · have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmem.2.1 hn0.bot_lt
          omega
        · have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hmem.2.1 hn10.bot_lt
          omega
      have hmle : m ≤ n := by
        rcases hmem with hmem | hmem
        · exact Nat.le_of_dvd hn0.bot_lt hmem.2.1
        · exact (Nat.le_of_dvd hn10.bot_lt hmem.2.1).trans (by omega)
      refine ⟨⟨hmpos, hmle⟩, ?_⟩
      have hchar : (m - 1) ∣ n * (m - 1) / (m - 1 + 1) := by
        apply (stechkin_divisibility_iff
          (n := n) (k := m - 1) (by omega) (by omega)).2
        have hrewrite : m - 1 + 1 = m := by omega
        rw [hrewrite]
        rcases hmem with hmem | hmem
        · exact Or.inl hmem.2.1
        · exact Or.inr hmem.2.1
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hchar
  have hdisjoint : Disjoint leftDivisors rightDivisors := by
    rw [Finset.disjoint_left]
    intro m hmleft hmright
    simp only [leftDivisors, rightDivisors, Finset.mem_erase,
      Nat.mem_divisors] at hmleft hmright
    have hmone : m ∣ 1 := by
      have := Nat.dvd_sub hmleft.2.1 hmright.2.1
      have heq : n - (n - 1) = 1 := by omega
      rwa [heq] at this
    exact hmleft.1 (Nat.eq_one_of_dvd_one hmone)
  have hone_n : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hone_pred : 1 ∈ (n - 1).divisors := Nat.one_mem_divisors.mpr hn10
  have hcard_n : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, hone_n⟩
  have hcard_pred : 1 ≤ (n - 1).divisors.card := Finset.card_pos.mpr ⟨1, hone_pred⟩
  change source.card + 2 = n.divisors.card + (n - 1).divisors.card
  rw [hsource, Finset.card_union_of_disjoint hdisjoint]
  simp only [leftDivisors, rightDivisors, Finset.card_erase_of_mem hone_n,
    Finset.card_erase_of_mem hone_pred]
  omega

end D5.S3.Arith.StechkinFunctionDivisorCount
