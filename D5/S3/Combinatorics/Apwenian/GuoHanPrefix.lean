/- GID: D5/S3/Combinatorics/Apwenian/GuoHanPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apwenian/GuoHanPrefix
   mirror-E: none(waiver:finite-alphabet-pattern-argument)
   anchors: []
   utility: none
   digest: Finite alphabets force prefix 101 without identifying distinct even letters. -/

import D5.S3.Combinatorics.Apwenian.GuoHanDyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Apwenian.GuoHan

open GuoHanDefs
open scoped BigOperators

/-- The alternative prefix 110 contradicts finiteness without identifying even letters. -/
theorem initial_prefix (Sigma : Finset ℕ)
    (hodd : ∀ x ∈ Sigma, x % 2 = 1 → x = 1)
    (p : ℕ) (hp : 2 ≤ p) (σ : ℕ → Fin p → ℕ) (a : ℕ → ℕ)
    (ha : ∀ n, a n ∈ Sigma)
    (hfix : ∀ n (r : Fin p), a (n * p + r) = σ (a n) r)
    (hap : IsApwenian a) : (a 1 : ZMod 2) = 0 ∧ a 2 = 1 := by
  classical
  let b : ℕ → ZMod 2 := fun n => a n
  have hbits (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
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
  have hcopy (t n : ℕ) (hn : a n = 1) (j : ℕ) (hj : j < p ^ t) :
      a (n * p ^ t + j) = a j := by
    simpa using equal_blocks p (by omega) σ a hfix t n 0 (hn.trans hap.1.symm) j hj
  have hzero : b 1 = 0 := by
    by_contra hnot
    have hb1 : b 1 = 1 := (hbits (b 1)).resolve_left hnot
    have ha1 : a 1 = 1 := (hbridge 1).mp hb1
    have hb2 : b 2 = 0 := by
      have hr := hrec 0
      norm_num only [mul_zero, zero_add] at hr
      rw [hb0, hb1] at hr
      exact add_eq_left.mp hr.symm
    have inv (t : ℕ) (hq : 3 ≤ p ^ t) :
        ∀ k, a (2 ^ (k + 1) - 1) = 1 ∧ b (2 ^ (k + 1)) = 0 ∧
          b (2 ^ (k + 1) * p ^ t) = 0 := by
      let q := p ^ t
      have hq' : 3 ≤ q := hq
      have copy (n : ℕ) (hn : a n = 1) (j : ℕ) (hj : j < q) :
          b (n * q + j) = b j := congrArg (fun x : ℕ => (x : ZMod 2))
            (hcopy t n hn j hj)
      have hlast (K : ℕ) (hK : 1 ≤ K) (hletter : a (K - 1) = 1) :
          b (K * q - 1) = b (q - 1) := by
        have hK' : K - 1 + 1 = K := by omega
        have hq'' : q - 1 + 1 = q := by omega
        have hprod : 1 ≤ K * q := by nlinarith
        have hsum : (K - 1) * q + (q - 1) + 1 = K * q := by
          calc
            _ = (K - 1) * q + q := by omega
            _ = (K - 1 + 1) * q := by ring
            _ = K * q := by rw [hK']
        have haddr : (K - 1) * q + (q - 1) = K * q - 1 := by omega
        simpa only [haddr] using copy (K - 1) hletter (q - 1) (by omega)
      intro k
      induction k with
      | zero =>
          have hl : b (q - 1) = b (2 * q - 1) := by
            have hc := copy 1 ha1 (q - 1) (by omega)
            have he : 1 * q + (q - 1) = 2 * q - 1 := by omega
            simpa only [he] using hc.symm
          have hr := hrec (q - 1)
          have he1 : 2 * (q - 1) + 1 = 2 * q - 1 := by omega
          have he2 : 2 * (q - 1) + 2 = 2 * q := by omega
          rw [he1, he2, ← hl] at hr
          have hz : b (2 * q) = 0 := add_eq_left.mp hr.symm
          exact ⟨by simpa using ha1, by simpa using hb2, by simpa using hz⟩
      | succ k ih =>
          let K := 2 ^ (k + 1)
          have hK : 1 ≤ K := Nat.one_le_pow _ _ (by omega)
          have hpow : 2 ^ (k + 1 + 1) = 2 * K := by simp [K, pow_succ, mul_comm]
          have hnletter : a (2 * K) ≠ 1 := by
            intro hn
            have h1 := copy (2 * K) hn 1 (by omega)
            have h2 := copy (2 * K) hn 2 (by omega)
            have hr := hrec (K * q)
            have he : 2 * (K * q) = (2 * K) * q := by ring
            rw [he, h1, h2, hb1, hb2, add_zero] at hr
            have hzeroK : b (K * q) = 0 := ih.2.2
            rw [hzeroK] at hr
            exact zero_ne_one hr
          have hnewzero : b (2 * K) = 0 :=
            (hbits (b (2 * K))).resolve_right (fun h => hnletter ((hbridge _).mp h))
          have hnewone : a (2 * K - 1) = 1 := by
            apply (hbridge _).mp
            have hr := hrec (K - 1)
            have he1 : 2 * (K - 1) + 1 = 2 * K - 1 := by omega
            have he2 : 2 * (K - 1) + 2 = 2 * K := by omega
            have hold : b (K - 1) = 1 := (hbridge _).mpr ih.1
            rw [he1, he2, hold, hnewzero, add_zero] at hr
            exact hr.symm
          have holdlast := hlast K hK ih.1
          have hnewlast := hlast (2 * K) (by omega) hnewone
          have hr := hrec (K * q - 1)
          have hKq : 1 ≤ K * q := by nlinarith
          have he1 : 2 * (K * q - 1) + 1 = (2 * K) * q - 1 := by
            have he : (2 * K) * q = 2 * (K * q) := by ring
            omega
          have he2 : 2 * (K * q - 1) + 2 = (2 * K) * q := by
            have he : (2 * K) * q = 2 * (K * q) := by ring
            omega
          rw [he1, he2, holdlast, hnewlast] at hr
          have hz : b ((2 * K) * q) = 0 := add_eq_left.mp hr.symm
          rw [hpow]
          exact ⟨hnewone, hnewzero, hz⟩
    have distinct (i j : ℕ) (hij : i < j) : a (2 ^ i) ≠ a (2 ^ j) := by
      intro heq
      let t := 2 ^ (i + 1) + 3
      let q := p ^ t
      have hlarge : t < q := Nat.lt_pow_self (by omega)
      have hDpos : 0 < 2 ^ i := pow_pos (by omega) _
      have htwice : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; omega
      change 2 ^ (i + 1) + 3 < q at hlarge
      rw [htwice] at hlarge
      have hq : 3 ≤ q := by omega
      have hbound : 2 ^ (i + 1) - 2 < q := by rw [htwice]; omega
      have hqone : b q = 1 := by
        have hc := hcopy t 1 ha1 0 (by omega)
        have hc' : a q = 1 := by simpa [hap.1] using hc
        exact (hbridge _).mpr hc'
      have hqzero : b (2 ^ (j - i) * q) = 0 := by
        have hk : j - i - 1 + 1 = j - i := by omega
        simpa only [hk] using (inv t hq (j - i - 1)).2.2
      have hpower : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ j)]
      have hsum : b q = b (2 ^ (j - i) * q) := by
        rw [dyadic_expansion b hrec i q, dyadic_expansion b hrec i (2 ^ (j - i) * q)]
        apply Finset.sum_congr rfl
        intro l hl
        have hl' := Finset.mem_range.mp hl
        have hD : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by omega)
        have htwice : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; omega
        have hoff : 2 ^ i - 1 + l < q := by omega
        have he1 : 2 ^ i * (q + 1) = 2 ^ i * q + 2 ^ i := by ring
        have he2 : 2 ^ i * (2 ^ (j - i) * q + 1) = 2 ^ j * q + 2 ^ i := by
          rw [hpower]
          ring
        have haddr1 : 2 ^ i * (q + 1) - 1 + l = 2 ^ i * q + (2 ^ i - 1 + l) := by
          omega
        have haddr2 : 2 ^ i * (2 ^ (j - i) * q + 1) - 1 + l =
            2 ^ j * q + (2 ^ i - 1 + l) := by omega
        rw [haddr1, haddr2]
        exact congrArg (fun x : ℕ => (x : ZMod 2))
          (equal_blocks p (by omega) σ a hfix t (2 ^ i) (2 ^ j) heq _ hoff)
      rw [hqone, hqzero] at hsum
      exact one_ne_zero hsum
    let f : ℕ → {x : ℕ // x ∈ Sigma} := fun i => ⟨a (2 ^ i), ha _⟩
    apply not_injective_infinite_finite f
    intro i j heq
    have he : a (2 ^ i) = a (2 ^ j) := congrArg Subtype.val heq
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim (distinct i j hij he)
    · exact hij
    · exact False.elim (distinct j i hij he.symm)
  refine ⟨hzero, (hbridge 2).mp ?_⟩
  have hr := hrec 0
  norm_num only [mul_zero, zero_add] at hr
  rw [hb0, hzero, zero_add] at hr
  exact hr.symm

end D5.S3.Combinatorics.Apwenian.GuoHan
