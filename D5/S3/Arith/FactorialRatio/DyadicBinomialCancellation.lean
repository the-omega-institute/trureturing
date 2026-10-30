/- GID: D5/S3/Arith/FactorialRatio/DyadicBinomialCancellation
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/DyadicBinomialCancellation
   mirror-E: none(waiver:pure-arithmetic)
   anchors: []
   utility: none
   digest: Exact reduced polarization-transfer fractions at every positive index. -/

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Reduced fractions in the dyadic binomial bounds of OEIS A362534 -/

/- This explicitly requested formalization preserves an existing written correction.
proof_shape: bind-only (binomial identity, exact prime-power decomposition,
  coprimality and Rat normalization from pinned Mathlib, composed by arithmetic).
No novel mathematical assertion, escape witness, open-problem admission or freeze
is claimed. The private helper is consumed by denominator_formula. The symbolic
unbounded theorem has no computational content of the four utility categories.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23314
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation

/- The two rational functions are restated locally so this general arithmetic
result remains independent of the S0 certified counterexample layer. -/
def f (n : ℕ) : ℚ :=
  if n % 2 = 0 then (2 : ℚ) ^ ((1 : ℤ) - n) * n * (n - 1).choose (n / 2)
  else (2 : ℚ) ^ ((1 : ℤ) - n) * n * (n - 1).choose ((n - 1) / 2)

def g (n : ℕ) : ℚ :=
  if n % 2 = 0 then 2 * (1 - (2 : ℚ) ^ (-(n : ℤ)) * n.choose (n / 2))
  else 2 * (1 - (2 : ℚ) ^ (-(n : ℤ)) * n.choose ((n - 1) / 2))

private theorem bounds_as_fractions (n : ℕ) (hn : 1 ≤ n) :
    f n = (2 : ℚ) * ((n - n / 2 : ℕ) : ℚ) * n.choose (n / 2) / 2 ^ n ∧
    g n = 2 * (1 - (n.choose (n / 2) : ℚ) / 2 ^ n) := by
  have hk : (n - 1) / 2 = n / 2 ∨ n % 2 = 0 := by omega
  have hbin : n * (n - 1).choose (n / 2) = n.choose (n / 2) * (n - n / 2) := by
    simpa [Nat.sub_add_cancel hn, Nat.mul_comm] using
      Nat.choose_mul_succ_eq (n - 1) (n / 2)
  have hpow : (2 : ℚ) ^ ((1 : ℤ) - n) = 2 / (2 : ℚ) ^ n := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
  have hneg : (2 : ℚ) ^ (-(n : ℤ)) = 1 / (2 : ℚ) ^ n := by simp
  have hf : f n = (2 : ℚ) ^ ((1 : ℤ) - n) * n * (n - 1).choose (n / 2) := by
    rcases hk with hk | hk <;> simp [f, hk]
  have hg : g n = 2 * (1 - (2 : ℚ) ^ (-(n : ℤ)) * n.choose (n / 2)) := by
    rcases hk with hk | hk <;> simp [g, hk]
  constructor
  · rw [hf, hpow]
    have hc : (n : ℚ) * ((n - 1).choose (n / 2) : ℚ) =
        (n.choose (n / 2) : ℚ) * ((n - n / 2 : ℕ) : ℚ) := by exact_mod_cast hbin
    calc
      _ = 2 * ((n : ℚ) * ((n - 1).choose (n / 2) : ℚ)) / 2 ^ n := by ring
      _ = _ := by rw [hc]; ring
  · rw [hg, hneg]; ring

/-- For every positive `n`, the numerator of `g n` is the odd binomial gap `G`,
and the only cancellation in the ratio is `gcd (ceil (n/2)) G`.
Here `factorization B 2` is exactly the exponent of 2 in the positive binomial
coefficient `B`; all divisions defining `b` and `G` are exact natural divisions. -/
theorem denominator_formula (n : ℕ) (hn : 1 ≤ n) :
    let m := n - n / 2
    let B := n.choose (n / 2)
    let v := B.factorization 2
    let b := B / 2 ^ v
    let G := (2 ^ n - B) / 2 ^ v
    (g n).num = (G : ℤ) ∧
      (f n / g n).den = G / Nat.gcd m G ∧
      (f n / g n).num = ((m * b / Nat.gcd m G : ℕ) : ℤ) := by
  dsimp only
  let m := n - n / 2
  let B := n.choose (n / 2)
  let v := B.factorization 2
  let b := B / 2 ^ v
  let r := n - v
  let G := 2 ^ r - b
  have hB : 0 < B := Nat.choose_pos (Nat.div_le_self n 2)
  have hBlt : B < 2 ^ n := Nat.choose_lt_two_pow n (n / 2) (by omega)
  have hd : 2 ^ v ∣ B := Nat.ordProj_dvd B 2
  have hdb : 2 ^ v * b = B := Nat.mul_div_cancel' hd
  have hv : v < n := by
    have hp : 2 ^ v ≤ B := Nat.le_of_dvd hB hd
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt hp hBlt)
  have hr : 0 < r := by dsimp [r]; omega
  have hsplit : 2 ^ n = 2 ^ v * 2 ^ r := by rw [← pow_add]; congr 1; dsimp [r]; omega
  have hb : 0 < b := Nat.ordCompl_pos 2 hB.ne'
  have hblt : b < 2 ^ r := by
    have h := hBlt
    rw [← hdb, hsplit] at h
    exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ v)).mp h
  have hG : 0 < G := Nat.sub_pos_of_lt hblt
  have hGdef : (2 ^ n - B) / 2 ^ v = G := by
    rw [hsplit, ← hdb, ← Nat.mul_sub_left_distrib, Nat.mul_div_right _ (by positivity)]
  have hb2 : Nat.Coprime b 2 := (Nat.coprime_ordCompl Nat.prime_two hB.ne').symm
  have hbG : Nat.Coprime b G :=
    (Nat.coprime_sub_self_right hblt.le).mpr (hb2.pow_right r)
  have hdenpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hG2 : Nat.Coprime G 2 := by
    apply Nat.coprime_two_right.mpr
    apply (Nat.odd_sub' hblt.le).mpr
    exact ⟨fun _ => by exact ⟨2 ^ (r - 1), by omega⟩,
      fun _ => hb2.odd_of_right⟩
  have hGpow : Nat.Coprime G (2 ^ (r - 1)) := hG2.pow_right _
  obtain ⟨hf, hg⟩ := bounds_as_fractions n hn
  have hdbq : (B : ℚ) = 2 ^ v * b := by exact_mod_cast hdb.symm
  have hsplitq : (2 : ℚ) ^ n = 2 ^ v * 2 ^ r := by exact_mod_cast hsplit
  have hGq : (G : ℚ) = 2 ^ r - b := by exact_mod_cast Nat.cast_sub hblt.le
  have hg' : g n = (G : ℚ) / 2 ^ (r - 1) := by
    rw [hg, hdbq, hsplitq, hGq]
    have hpq : (2 : ℚ) ^ r = 2 * 2 ^ (r - 1) := by exact_mod_cast hdenpow
    rw [hpq]
    field_simp
    <;> ring
  have hratio : f n / g n = ((m * b : ℕ) : ℚ) / G := by
    rw [hf, hg, hdbq, hsplitq, hGq]
    simp only [Nat.cast_mul]
    change (2 * (m : ℚ) * (2 ^ v * b) / (2 ^ v * 2 ^ r)) /
      (2 * (1 - (2 ^ v * b) / (2 ^ v * 2 ^ r))) =
      (m : ℚ) * b / (2 ^ r - b)
    have hne : (2 : ℚ) ^ r - b ≠ 0 := by
      rw [← hGq]; exact_mod_cast hG.ne'
    field_simp [hne]
    <;> ring
  change (g n).num = (((2 ^ n - B) / 2 ^ v : ℕ) : ℤ) ∧
    (f n / g n).den = ((2 ^ n - B) / 2 ^ v) / Nat.gcd m ((2 ^ n - B) / 2 ^ v) ∧
    (f n / g n).num = ((m * b / Nat.gcd m ((2 ^ n - B) / 2 ^ v) : ℕ) : ℤ)
  rw [hGdef, hratio]
  constructor
  · rw [hg']
    rw [show (2 : ℚ) ^ (r - 1) = ((2 ^ (r - 1) : ℕ) : ℚ) by norm_cast,
      Rat.natCast_div_eq_divInt, Rat.divInt_ofNat, Rat.num_mkRat]
    simp [show 2 ^ (r - 1) ≠ 0 by positivity, hGpow.symm.gcd_eq_one]
  · have hcancel : Nat.gcd (m * b) G = Nat.gcd m G := hbG.gcd_mul_right_cancel m
    constructor
    · rw [Rat.natCast_div_eq_divInt, Rat.divInt_ofNat, Rat.den_mkRat]
      simp only [Int.natAbs_natCast, if_neg hG.ne', Nat.gcd_comm G (m * b), hcancel]
    · rw [Rat.natCast_div_eq_divInt, Rat.divInt_ofNat, Rat.num_mkRat]
      simp only [Int.natAbs_natCast, if_neg hG.ne', Nat.gcd_comm G (m * b), hcancel,
        Int.natCast_ediv]

#print axioms denominator_formula

end D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation
