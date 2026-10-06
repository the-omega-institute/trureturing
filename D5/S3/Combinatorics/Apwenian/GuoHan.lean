/- GID: D5/S3/Combinatorics/Apwenian/GuoHan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apwenian/GuoHan
   mirror-E: none(waiver:external-conjecture-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic]
   utility: none
   digest: Block contraction and descent prove Guo and Han's apwenian classification. -/

import D5.S3.Combinatorics.Apwenian.GuoHanPrefix
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Apwenian.GuoHan

open GuoHanDefs
open scoped BigOperators

/-- Two positive contractions exclude a least even zero by well-founded descent. -/
theorem power_two_even (b : ℕ → ZMod 2)
    (hrec : ∀ n, b n = b (2 * n + 1) + b (2 * n + 2))
    (hb0 : b 0 = 1) (hb2 : b 2 = 1)
    (p : ℕ) (hcopy : ∀ t n, b n = 1 → ∀ j < p ^ t, b (n * p ^ t + j) = b j)
    (v : ℕ) (hv : 0 < v) (hbase : p = 2 ^ v) : ∀ n, b (2 * n) = 1 := by
  have hbits (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  have contract (h H L r : ℕ)
      (hc : ∀ j < L, b (2 ^ h * H + j) = b j)
      (hr : 2 ^ h * (r + 2) - 2 < L) : b (H + r) = b r := by
    rw [dyadic_expansion b hrec h (H + r), dyadic_expansion b hrec h r]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hpos : 0 < 2 ^ h := pow_pos (by omega) _
    have hlo : 1 ≤ 2 ^ h * (r + 1) := by nlinarith
    have hu : 2 ^ h * (r + 2) = 2 ^ h * (r + 1) + 2 ^ h := by ring
    have hbound : 2 ^ h * (r + 1) - 1 + j < L := by omega
    have he : 2 ^ h * (H + r + 1) = 2 ^ h * H + 2 ^ h * (r + 1) := by ring
    have haddr : 2 ^ h * (H + r + 1) - 1 + j =
        2 ^ h * H + (2 ^ h * (r + 1) - 1 + j) := by omega
    rw [haddr, hc _ hbound]
  let e := 2 * v - 2
  let H := 2 ^ e
  let q := p ^ 2
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by omega)
  have hqeq : q = 4 * H := by
    dsimp [q, H, e]
    rw [hbase, ← pow_mul]
    have hexp : v * 2 = (2 * v - 2) + 2 := by omega
    rw [hexp, pow_add]
    norm_num
    ring
  have hq : 4 ≤ q := by omega
  have hD : 2 ^ (e + 1) = 2 * H := by dsimp [H]; rw [pow_succ, mul_comm]
  have hdouble (n : ℕ) (hn : b n = 1) : b (2 * n) = 1 := by
    have hc (j : ℕ) (hj : j < q) : b (2 ^ (e + 1) * (2 * n) + j) = b j := by
      have he : 2 ^ (e + 1) * (2 * n) = n * q := by rw [hD, hqeq]; ring
      rw [he]
      exact hcopy 2 n hn j hj
    have hr : 2 ^ (e + 1) * (0 + 2) - 2 < q := by rw [hD, hqeq]; omega
    have hcon := contract (e + 1) (2 * n) q 0 hc hr
    simpa only [add_zero, hb0] using hcon
  have hquad (n : ℕ) (hn : b n = 1) : b (4 * n + 2) = 1 := by
    have hc (j : ℕ) (hj : j < q) : b (2 ^ e * (4 * n) + j) = b j := by
      have he : 2 ^ e * (4 * n) = n * q := by change H * (4 * n) = n * q; rw [hqeq]; ring
      rw [he]
      exact hcopy 2 n hn j hj
    have hr : 2 ^ e * (2 + 2) - 2 < q := by change H * 4 - 2 < q; rw [hqeq]; omega
    exact (contract e (4 * n) q 2 hc hr).trans hb2
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_contra hn
      have hzero : b (2 * n) = 0 := (hbits _).resolve_right hn
      have hn2 : 2 ≤ n := by
        by_contra hsmall
        have hn0 : n = 0 ∨ n = 1 := by omega
        rcases hn0 with rfl | rfl
        · simpa using hn hb0
        · simpa using hn hb2
      have hbn : b n = 0 := by
        rcases hbits (b n) with h | h
        · exact h
        · exact False.elim (hn (hdouble n h))
      have hodd : n % 2 = 1 := by
        by_contra hne
        have heven : n = 2 * (n / 2) := by omega
        have hsmall : n / 2 < n := by omega
        have hb := ih (n / 2) hsmall
        rw [← heven, hbn] at hb
        exact zero_ne_one hb
      let r := n / 2
      have hnaddr : n = 2 * r + 1 := by dsimp [r]; omega
      have hsmall : r + 1 < n := by omega
      have hnext : b (2 * r + 2) = 1 := by
        simpa only [mul_add, mul_one] using ih (r + 1) hsmall
      have hbr : b r = 1 := by
        have hr := hrec r
        rw [← hnaddr, hbn, hnext, zero_add] at hr
        exact hr
      have hfinal := hquad r hbr
      have he : 4 * r + 2 = 2 * n := by omega
      rw [he] at hfinal
      exact hn hfinal

/-- Guo and Han, Conjecture 2, for the fixed public statement and actual natural letters. -/
theorem result : GuoHanDefs.claim := by
  intro Sigma h1 hodd p σ a hp hσ ha hfix
  constructor
  · intro hap
    let b : ℕ → ZMod 2 := fun n => a n
    have hbridge (n : ℕ) : b n = 1 ↔ a n = 1 := by
      constructor
      · intro hn
        apply hodd _ (ha n)
        exact (ZMod.natCast_eq_natCast_iff' (a n) 1 2).mp hn
      · intro hn
        simp only [b, hn, Nat.cast_one]
    have hrec (n : ℕ) : b n = b (2 * n + 1) + b (2 * n + 2) := by
      simpa only [b, Nat.cast_add] using
        (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr (hap.2 n)
    have hb0 : b 0 = 1 := by simp only [b, hap.1, Nat.cast_one]
    have hprefix := initial_prefix Sigma hodd p hp σ a ha hfix hap
    have hb1 : b 1 = 0 := hprefix.1
    have hb2 : b 2 = 1 := (hbridge 2).mpr hprefix.2
    have hcopy (t n : ℕ) (hn : b n = 1) (j : ℕ) (hj : j < p ^ t) :
        b (n * p ^ t + j) = b j := by
      have hletter : a n = a 0 := ((hbridge n).mp hn).trans hap.1.symm
      simpa only [zero_mul, zero_add, b] using
        congrArg (fun x : ℕ => (x : ZMod 2))
          (equal_blocks p (by omega) σ a hfix t n 0 hletter j hj)
    have exclude (v d0 : ℕ) (hbase : p = 2 ^ v * d0)
        (hodd : Odd d0) (hd0 : 3 ≤ d0) : False := by
      have contract (h H L r : ℕ)
          (hc : ∀ j < L, b (2 ^ h * H + j) = b j)
          (hr : 2 ^ h * (r + 2) - 2 < L) : b (H + r) = b r := by
        rw [dyadic_expansion b hrec h (H + r), dyadic_expansion b hrec h r]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hpos : 0 < 2 ^ h := pow_pos (by omega) _
        have hlo : 1 ≤ 2 ^ h * (r + 1) := by nlinarith
        have hu : 2 ^ h * (r + 2) = 2 ^ h * (r + 1) + 2 ^ h := by ring
        have hbound : 2 ^ h * (r + 1) - 1 + j < L := by omega
        have he : 2 ^ h * (H + r + 1) = 2 ^ h * H + 2 ^ h * (r + 1) := by ring
        have haddr : 2 ^ h * (H + r + 1) - 1 + j =
            2 ^ h * H + (2 ^ h * (r + 1) - 1 + j) := by omega
        rw [haddr, hc _ hbound]
      let s := 2 ^ (2 * v)
      let d := d0 ^ 2
      let q := p ^ 2
      have hs : 1 ≤ s := Nat.one_le_pow _ _ (by omega)
      have hd : 9 ≤ d := by dsimp [d]; nlinarith
      have hqeq : q = s * d := by
        dsimp [q, s, d]
        rw [hbase, mul_pow, ← pow_mul, Nat.mul_comm v 2]
      have hq9s : 9 * s ≤ q := by nlinarith
      have hq : 9 ≤ q := by nlinarith
      have hD : 2 ^ (2 * v + 1) = 2 * s := by
        dsimp [s]
        rw [pow_succ, mul_comm]
      have hfirst : 2 * s * (1 + 2) - 2 < q := by
        have hstrong : 2 * s * (1 + 2) < q := by nlinarith
        exact (Nat.sub_le _ _).trans_lt hstrong
      have copyq (j : ℕ) (hj : j < q) : b (2 * q + j) = b j := hcopy 2 2 hb2 j hj
      have copyD (j : ℕ) (hj : j < q) : b (2 ^ (2 * v + 1) * d + j) = b j := by
        have he : 2 ^ (2 * v + 1) * d = 2 * q := by rw [hD, hqeq]; ring
        rw [he, copyq j hj]
      have hbd : b d = 1 := by
        have hc := contract (2 * v + 1) d q 0 copyD (by rw [hD]; omega)
        simpa only [add_zero, hb0] using hc
      have hbd1 : b (d + 1) = 0 := by
        have hc := contract (2 * v + 1) d q 1 copyD (by rw [hD]; exact hfirst)
        exact hc.trans hb1
      have hoddD : Odd d := hodd.pow
      obtain ⟨m, hm⟩ := hoddD
      have hdaddr : d = 2 * m + 1 := by omega
      have hbm : b m = 1 := by
        have hr := hrec m
        rw [← hdaddr, show 2 * m + 2 = d + 1 by omega, hbd, hbd1, add_zero] at hr
        exact hr
      let N := m * q + q - 1
      have hN : b N = b (q - 1) := by
        have hc := hcopy 2 m hbm (q - 1) (by omega)
        have he : m * q + (q - 1) = N := by dsimp [N]; omega
        change b (m * q + (q - 1)) = b (q - 1) at hc
        rw [he] at hc
        exact hc
      have hbq : b q = 1 := by
        have hc := contract 1 q q 0 (by simpa using copyq) (by norm_num; omega)
        simpa only [add_zero, hb0] using hc
      have hfour : p ^ 4 = q ^ 2 := by dsimp [q]; rw [← pow_mul]
      have copyq2 (j : ℕ) (hj : j < q ^ 2) : b (2 * q ^ 2 + j) = b j := by
        simpa only [hfour] using hcopy 4 2 hb2 j (by simpa only [hfour] using hj)
      have copyD2 (j : ℕ) (hj : j < q ^ 2) :
          b (2 ^ (2 * v + 1) * (q * d) + j) = b j := by
        have he : 2 ^ (2 * v + 1) * (q * d) = 2 * q ^ 2 := by
          rw [hD]
          calc
            _ = 2 * q * (s * d) := by ring
            _ = 2 * q ^ 2 := by rw [← hqeq]; ring
        rw [he, copyq2 j hj]
      have hlarge : 2 * s * (q + 2) - 2 < q ^ 2 := by
        have hmul := Nat.mul_le_mul_right q hq9s
        have hmul' := Nat.mul_le_mul_left s hq
        have hstrong : 2 * s * (q + 2) < q ^ 2 := by nlinarith
        exact (Nat.sub_le _ _).trans_lt hstrong
      have hc1 : b (q * d + (q - 1)) = b (q - 1) :=
        contract (2 * v + 1) (q * d) (q ^ 2) (q - 1) copyD2 (by
          rw [hD]
          have hle : 2 * s * (q - 1 + 2) ≤ 2 * s * (q + 2) :=
            Nat.mul_le_mul_left _ (by omega)
          exact (Nat.sub_le_sub_right hle 2).trans_lt hlarge)
      have hc2 : b (q * d + q) = 1 := by
        have hc := contract (2 * v + 1) (q * d) (q ^ 2) q copyD2 (by rw [hD]; exact hlarge)
        exact hc.trans hbq
      have hNsum : N + 1 = m * q + q := by dsimp [N]; omega
      have he1 : 2 * N + 1 = q * d + (q - 1) := by
        have hqsub : q - 1 + 1 = q := by omega
        have hsum : (2 * N + 1) + 1 = (q * d + (q - 1)) + 1 := by
          rw [hdaddr]
          nlinarith only [hNsum, hqsub]
        omega
      have he2 : 2 * N + 2 = q * d + q := by rw [hdaddr]; nlinarith
      have hr := hrec N
      rw [he1, he2, hN, hc1, hc2] at hr
      have hz : (1 : ZMod 2) = 0 := add_eq_left.mp hr.symm
      exact one_ne_zero hz
    obtain ⟨v, d, hdodd, hbase⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : p ≠ 0)
    have hd1 : d = 1 := by
      by_contra hdne
      obtain ⟨k, hk⟩ := hdodd
      have hd3 : 3 ≤ d := by omega
      exact exclude v d hbase ⟨k, hk⟩ hd3
    have hpbase : p = 2 ^ v := by simpa only [hd1, mul_one] using hbase
    have hv : 0 < v := by
      by_contra hv0
      have : v = 0 := by omega
      simp only [this, pow_zero] at hpbase
      omega
    have heven := power_two_even b hrec hb0 hb2 p hcopy v hv hpbase
    have heq := identify_parity b hrec heven
    intro n
    have hbnd : periodDoubling n ≤ 1 := by
      rw [periodDoubling]
      split_ifs <;> omega
    have hcast : (a n : ZMod 2) = (periodDoubling n : ZMod 2) := heq n
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp hcast
    rwa [Nat.mod_eq_of_lt (by omega : periodDoubling n < 2)] at hmod
  · intro h
    have hb (n : ℕ) : periodDoubling n ≤ 1 := by
      rw [periodDoubling]
      split_ifs <;> omega
    have he (n : ℕ) : periodDoubling (2 * n) = 1 := by
      rw [periodDoubling]
      simp
    have ho (n : ℕ) : periodDoubling (2 * n + 1) = 1 - periodDoubling n := by
      rw [periodDoubling]
      simp [Nat.add_div]
    constructor
    · apply hodd _ (ha 0)
      have hz := he 0
      norm_num at hz
      rw [h 0, hz]
    · intro n
      rw [Nat.add_mod, h n, h (2 * n + 1), h (2 * n + 2), ho]
      rw [show 2 * n + 2 = 2 * (n + 1) by omega, he]
      have := hb n
      omega

end D5.S3.Combinatorics.Apwenian.GuoHan
