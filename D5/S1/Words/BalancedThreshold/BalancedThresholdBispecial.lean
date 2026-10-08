/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdBispecial
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdBispecial
   mirror-E: none(waiver:aperiodic-repetition-supplier)
   anchors: []
   utility: none
   digest: Maximal periodic stretches produce bispecial factors and short adjacent returns. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Complexity BalancedThresholdDefs

/-- Each occurring factor has a bounded gap to an occurrence in every suffix. -/
def UniformlyRecurrentWord {A : Type*} [Fintype A] (x : ℕ → A) : Prop :=
  ∀ n i, ∃ R, ∀ s, ∃ j, s ≤ j ∧ j ≤ s + R ∧ wordFactor x n j = wordFactor x n i

/-- A factor with two distinct left extensions and two distinct right extensions. -/
def BispecialFactor {A : Type*} [Fintype A] (x : ℕ → A) {n : ℕ}
    (w : Fin n → A) : Prop :=
  (∃ i j, 0 < i ∧ 0 < j ∧ wordFactor x n i = w ∧ wordFactor x n j = w ∧
    x (i - 1) ≠ x (j - 1)) ∧
  (∃ i j, wordFactor x n i = w ∧ wordFactor x n j = w ∧ x (i + n) ≠ x (j + n))

/-- Two successive occurrence starts, allowing overlapping occurrences. -/
def AdjacentOccurrences {A : Type*} [Fintype A] (x : ℕ → A) {n : ℕ}
    (w : Fin n → A) (i j : ℕ) : Prop :=
  i < j ∧ wordFactor x n i = w ∧ wordFactor x n j = w ∧
    ∀ k, i < k → k < j → wordFactor x n k ≠ w

/-- Bounded-gap recurrence permits maximal extension on both sides of a repetition. -/
theorem bispecial_return_period_bound {A : Type*} [Fintype A] (x : ℕ → A)
    (hrec : UniformlyRecurrentWord x) (haper : ¬ EventuallyPeriodicWord x)
    (C : ℝ) (hC : 0 < C)
    (hreturn : ∀ n (w : Fin n → A), 0 < n → BispecialFactor x w →
      ∀ i j, AdjacentOccurrences x w i j → C * (n : ℝ) ≤ (j - i : ℕ))
    (n i p : ℕ) (hp : 0 < p) (hperiod : HasPeriod x n i p) :
    (n : ℝ) ≤ (1 + 1 / C) * (p : ℝ) := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  by_cases hshort : n ≤ p
  · have hnR : (n : ℝ) ≤ p := by exact_mod_cast hshort
    have hpos : 0 ≤ (1 / C) * (p : ℝ) := by positivity
    nlinarith only [hnR, hpos]
  have hbad : ∃ k, x (k + p) ≠ x k := by
    by_contra hn
    push Not at hn
    apply haper
    refine ⟨0, p, hp, ?_⟩
    intro k
    simpa only [Nat.zero_add] using hn k
  obtain ⟨u, hu⟩ := hbad
  obtain ⟨R, hR⟩ := hrec (p + 1) u
  have mismatch : ∀ s, ∃ k, s ≤ k ∧ k ≤ s + R ∧ x (k + p) ≠ x k := by
    intro s
    obtain ⟨k, hsk, hkR, hf⟩ := hR s
    have h0 := congrFun hf (⟨0, by omega⟩ : Fin (p + 1))
    have hp' := congrFun hf (⟨p, by omega⟩ : Fin (p + 1))
    simp only [wordFactor, Nat.add_zero] at h0 hp'
    refine ⟨k, hsk, hkR, ?_⟩
    intro he
    exact hu (hp'.symm.trans (he.trans h0))
  have hfirst : ∃ r, x (i + r + p) ≠ x (i + r) := by
    obtain ⟨k, hik, _, hk⟩ := mismatch i
    exact ⟨k - i, by simpa only [Nat.add_sub_of_le hik] using hk⟩
  let r := Nat.find hfirst
  have hright : x (i + r + p) ≠ x (i + r) := Nat.find_spec hfirst
  have agree : ∀ k, k < r → x (i + k + p) = x (i + k) := by
    intro k hk
    by_contra hn
    exact Nat.find_min hfirst hk hn
  have hlength : n - p ≤ r := by
    by_contra hn
    exact hright (hperiod r (by omega)).symm
  obtain ⟨S, hS⟩ := hrec (r + p + 1) i
  obtain ⟨j, hj, _, hf⟩ := hS (R + 1)
  have transport : ∀ k, k ≤ r + p → x (j + k) = x (i + k) := by
    intro k hk
    exact congrFun hf (⟨k, by omega⟩ : Fin (r + p + 1))
  have jright : x (j + r + p) ≠ x (j + r) := by
    intro he
    apply hright
    have ht := transport (r + p) (by omega)
    rw [Nat.add_assoc] at he ⊢
    exact ht.symm.trans (he.trans (transport r (by omega)))
  have jagree : ∀ k, k < r → x (j + k + p) = x (j + k) := by
    intro k hk
    rw [Nat.add_assoc, transport (k + p) (by omega), ← Nat.add_assoc,
      agree k hk, ← transport k (by omega)]
  have hback : ∃ b, 0 < b ∧ b ≤ j ∧ x (j - b + p) ≠ x (j - b) := by
    obtain ⟨k, _, hk, hne⟩ := mismatch (j - (R + 1))
    have hkj : k < j := by omega
    refine ⟨j - k, by omega, by omega, ?_⟩
    simpa only [Nat.sub_sub_self hkj.le] using hne
  let b := Nat.find hback
  have hb : 0 < b ∧ b ≤ j ∧ x (j - b + p) ≠ x (j - b) := Nat.find_spec hback
  have back_agree : ∀ d, 0 < d → d < b → x (j - d + p) = x (j - d) := by
    intro d hd0 hdb
    by_contra hn
    exact Nat.find_min hback hdb ⟨hd0, by omega, hn⟩
  let a := j - b + 1
  let L := r + b - 1
  have ha : 0 < a := by dsimp [a]; omega
  have he : a + L = j + r := by dsimp [a, L]; omega
  have hL : n - p ≤ L := by dsimp [L]; omega
  have hLpos : 0 < L := by omega
  have interval_agree : ∀ k, k < L → x (a + k + p) = x (a + k) := by
    intro k hk
    by_cases hleft : a + k < j
    · have hd0 : 0 < j - (a + k) := by omega
      have hdb : j - (a + k) < b := by dsimp [a] at *; omega
      have hd := back_agree (j - (a + k)) hd0 hdb
      simpa only [Nat.sub_sub_self hleft.le] using hd
    · have hkr : a + k - j < r := by omega
      have hd := jagree (a + k - j) hkr
      simpa only [Nat.add_sub_of_le (by omega : j ≤ a + k)] using hd
  let w := wordFactor x L a
  have hpair : wordFactor x L (a + p) = w := by
    funext k
    have hk := interval_agree k k.isLt
    simpa only [w, wordFactor, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  have hleftne : x (a - 1) ≠ x (a + p - 1) := by
    have hidx : a - 1 = j - b := by dsimp [a]
    have hidxp : a + p - 1 = j - b + p := by dsimp [a]; omega
    rw [hidx, hidxp]
    exact hb.2.2.symm
  have hrightne : x (a + L) ≠ x (a + p + L) := by
    rw [he, show a + p + L = j + r + p by omega]
    exact jright.symm
  have hbis : BispecialFactor x w := by
    exact ⟨⟨a, a + p, ha, by omega, rfl, hpair, hleftne⟩,
      ⟨a, a + p, rfl, hpair, hrightne⟩⟩
  have hnext : ∃ q, 0 < q ∧ wordFactor x L (a + q) = w := ⟨p, hp, hpair⟩
  let q := Nat.find hnext
  have hq : 0 < q ∧ wordFactor x L (a + q) = w := Nat.find_spec hnext
  have hqp : q ≤ p := Nat.find_min' hnext ⟨hp, hpair⟩
  have hadj : AdjacentOccurrences x w a (a + q) := by
    refine ⟨by omega, rfl, hq.2, ?_⟩
    intro k hak hkq hkw
    have hk : k - a < q := by omega
    have heq : wordFactor x L (a + (k - a)) = w := by
      simpa only [Nat.add_sub_of_le hak.le] using hkw
    exact Nat.find_min hnext hk ⟨by omega, heq⟩
  have hbound := hreturn L w hLpos hbis a (a + q) hadj
  rw [Nat.add_sub_cancel_left] at hbound
  have hqpR : (q : ℝ) ≤ p := by exact_mod_cast hqp
  have hLR : (n - p : ℕ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hnp : (n - p : ℕ) = (n : ℝ) - (p : ℝ) := Nat.cast_sub (by omega)
  have hbound' := (mul_le_mul_of_nonneg_left hLR hC.le).trans (hbound.trans hqpR)
  rw [hnp] at hbound'
  rw [show (1 + 1 / C) * (p : ℝ) = ((C + 1) * (p : ℝ)) / C by
    field_simp]
  apply (le_div_iff₀ hC).mpr
  nlinarith only [hbound']

end D5.S1.Words.BalancedThreshold
