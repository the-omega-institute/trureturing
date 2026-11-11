/- GID: D5/S1/Digit/CoonsAdjacentGrowthRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/CoonsAdjacentGrowthRefutation
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim; result=D5/S1/Digit/CoonsAdjacentGrowthRefutation.result; claim=D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim
   digest: Radix four has equal adjacent bounded-digit logarithmic growth exponents. -/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

/-! # Equal adjacent bounded-digit growth at radix four -/

namespace D5.S1.Digit.CoonsAdjacentGrowthRefutation

open scoped BigOperators

noncomputable section

/-- Each function occurs once, independently of any zero padding. -/
def weight (ell : ℕ) (a : ℕ →₀ ℕ) : ℕ := a.sum (fun i d => d * ell ^ i)

def Partitions (k ell n : ℕ) :=
  {a : ℕ →₀ ℕ // (∀ i, a i ≤ k) ∧ weight ell a = n}

def count (k ell n : ℕ) : ℕ := Nat.card (Partitions k ell n)

/-- The values at zero and one do not enter any of the tails below. -/
def readout (k ell n : ℕ) : ℝ := Real.log (count k ell n) / Real.log n

/-- The literal extended-real, all-natural every-tail definition. -/
def exponent (k ell : ℕ) : EReal :=
  ⨅ (N : ℕ) (_ : 2 ≤ N), ⨆ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal)

def claim : Prop :=
  ∀ ell : ℕ, 2 ≤ ell → ∀ k : ℕ, ell - 1 ≤ k →
    exponent k ell < exponent (k + 1) ell

private def window (ell m : ℕ) (u : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, u i * ell ^ i

private lemma window_succ (ell m : ℕ) (u : ℕ → ℕ) :
    window ell (m + 1) u = u 0 + ell * window ell m (fun i => u (i + 1)) := by
  simp only [window, Finset.sum_range_succ', pow_zero, mul_one, pow_succ,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def pack (m : ℕ) (u : ℕ → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range m) (fun i => if i < m then u i else 0)
    (by intro i hi; simp only [Finset.mem_range]; by_contra h; simp [h] at hi)

private lemma pack_apply (m : ℕ) (u : ℕ → ℕ) (i : ℕ) :
    pack m u i = if i < m then u i else 0 := rfl

private lemma weight_window (ell m : ℕ) (a : ℕ →₀ ℕ)
    (h : ∀ i, m ≤ i → a i = 0) : weight ell a = window ell m a := by
  unfold weight window
  apply Finsupp.sum_of_support_subset
  · intro i hi
    simp only [Finset.mem_range]
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (h i (by omega))
  · simp

private lemma weight_pack (ell m : ℕ) (u : ℕ → ℕ) :
    weight ell (pack m u) = window ell m u := by
  rw [weight_window ell m _ (by intro i hi; simp [pack_apply, not_lt.mpr hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pack_apply, Finset.mem_range.mp hi]

private lemma term_le_weight (ell : ℕ) (a : ℕ →₀ ℕ) (i : ℕ) :
    a i * ell ^ i ≤ weight ell a := by
  by_cases hi : a i = 0
  · simp [hi]
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j * ell ^ j))
      (Finsupp.mem_support_iff.mpr hi)

private lemma support_bound {ell n m : ℕ} (hell : 2 ≤ ell) (hn : n < ell ^ m)
    (a : ℕ →₀ ℕ) (ha : weight ell a = n) : ∀ i, m ≤ i → a i = 0 := by
  intro i hi
  by_contra h
  have hp : ell ^ m ≤ ell ^ i := Nat.pow_le_pow_right (by omega) hi
  have ht := term_le_weight ell a i
  have : 1 ≤ a i := by omega
  rw [ha] at ht
  nlinarith

/-- Actual finite-support representations form a finite set for every admissible radix. -/
theorem partitions_finite (k ell n : ℕ) (hell : 2 ≤ ell) :
    Finite (Partitions k ell n) := by
  let m := n + 1
  have hn : n < ell ^ m := by
    have h := Nat.lt_pow_self (by omega : 1 < ell) (n := m)
    omega
  let f : Partitions k ell n → (Fin m → Fin (k + 1)) :=
    fun a i => ⟨a.val i, Nat.lt_succ_of_le (a.property.1 i)⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i < m
  · exact congrArg Fin.val (congrFun hab ⟨i, hi⟩)
  · rw [support_bound hell hn a.val a.property.2 i (by omega),
      support_bound hell hn b.val b.property.2 i (by omega)]

private lemma window_digits (ell : ℕ) (l : List ℕ) :
    window ell l.length (fun i => l[i]?.getD 0) = Nat.ofDigits ell l := by
  induction l with
  | nil => simp [window]
  | cons d l ih =>
    rw [List.length_cons, window_succ]
    simpa [Nat.ofDigits_cons] using congrArg (fun x => d + ell * x) ih

private lemma count_zero (k ell : ℕ) (hell : 2 ≤ ell) : count k ell 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨0, (by simp), (by simp [weight])⟩, ?_⟩
  intro a
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  have h := term_le_weight ell a.val i
  rw [a.property.2] at h
  have hp : 0 < ell ^ i := by positivity
  simpa using (show a.val i = 0 by nlinarith)

/-- Ordinary radix digits give positivity for the entire quantified parameter range. -/
theorem count_positive (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k) :
    0 < count k ell n := by
  by_cases hn : n = 0
  · subst n
    rw [count_zero k ell hell]
    norm_num
  let l := Nat.digits ell n
  let a := pack l.length (fun i => l[i]?.getD 0)
  have ha : ∀ i, a i ≤ k := by
    intro i
    dsimp [a]
    rw [pack_apply]
    split_ifs with hi
    · have hmem : l[i]?.getD 0 ∈ l := by
        simpa [List.getElem?_eq_getElem hi] using List.getElem_mem hi
      have hd := Nat.digits_lt_base (by omega : 1 < ell) hmem
      omega
    · omega
  have hw : weight ell a = n := by
    rw [weight_pack, window_digits, Nat.ofDigits_digits]
  letI := partitions_finite k ell n hell
  haveI : Nonempty (Partitions k ell n) := ⟨⟨a, ha, hw⟩⟩
  exact Nat.card_pos

private lemma quotient_injective (m : ℕ) (u v : ℕ → ℕ)
    (hs : window 4 m u = window 4 m v)
    (hq : ∀ i, i < m → u i / 4 = v i / 4) :
    ∀ i, i < m → u i = v i := by
  induction m generalizing u v with
  | zero => simp
  | succ m ih =>
    rw [window_succ, window_succ] at hs
    have h0 := hq 0 (by omega)
    have hmod : u 0 % 4 = v 0 % 4 := by omega
    have huv : u 0 = v 0 := by omega
    have ht : window 4 m (fun i => u (i+1)) = window 4 m (fun i => v (i+1)) := by omega
    have hh := ih (fun i => u (i+1)) (fun i => v (i+1)) ht
      (by intro i hi; exact hq (i+1) (by omega))
    intro i hi
    cases i with
    | zero => exact huv
    | succ i => exact hh i (by omega)

/-- Quotient digits give at most two choices at each non-top coordinate. -/
theorem count_upper (k m n : ℕ) (hk : k ≤ 6) (hn : n < 4 ^ (m + 1)) :
    count k 4 n ≤ 2 ^ m := by
  let f : Partitions k 4 n → (Fin m → Fin 2) :=
    fun a i => ⟨a.val i / 4, by have := a.property.1 i; omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hza := support_bound (by norm_num : 2 ≤ 4) hn a.val a.property.2
    have hzb := support_bound (by norm_num : 2 ≤ 4) hn b.val b.property.2
    have hs : window 4 (m+1) a.val = window 4 (m+1) b.val := by
      rw [← weight_window 4 (m+1) a.val hza, ← weight_window 4 (m+1) b.val hzb,
        a.property.2, b.property.2]
    have htop (c : Partitions k 4 n) : c.val m / 4 = 0 := by
      have ht := term_le_weight 4 c.val m
      rw [c.property.2] at ht
      rw [pow_succ] at hn
      have hp : 0 < 4 ^ m := by positivity
      have : c.val m < 4 := by nlinarith
      omega
    have heq := quotient_injective (m+1) a.val b.val hs (by
      intro i hi
      by_cases him : i < m
      · exact congrArg Fin.val (congrFun hab ⟨i, him⟩)
      · have : i = m := by omega
        subst i
        rw [htop a, htop b])
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : i < m+1
    · exact heq i hi
    · rw [hza i (by omega), hzb i (by omega)]
  have hcard := Nat.card_le_card_of_injective f hinj
  simpa [count, Nat.card_fun] using hcard

private lemma count_square_le (k n : ℕ) (hk : k ≤ 6) (hn : 1 ≤ n) :
    (count k 4 n) ^ 2 ≤ n := by
  have hu := count_upper k (Nat.log 4 n) n hk (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hl : 4 ^ Nat.log 4 n ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hp : (2 ^ Nat.log 4 n) ^ 2 = 4 ^ Nat.log 4 n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    (count k 4 n) ^ 2 ≤ (2 ^ Nat.log 4 n) ^ 2 := Nat.pow_le_pow_left hu 2
    _ = 4 ^ Nat.log 4 n := hp
    _ ≤ n := hl

/-- A repunit with `m+1` digits. -/
def repunit (m : ℕ) : ℕ := ∑ i ∈ Finset.range (m+1), 4 ^ i

private lemma repunit_bounds (m : ℕ) :
    4 ^ m ≤ repunit m ∧ repunit m < 4 ^ (m+1) := by
  induction m with
  | zero => norm_num [repunit]
  | succ m ih =>
    have hr : repunit (m+1) = repunit m + 4^(m+1) := by
      simp [repunit, Finset.sum_range_succ]
    rw [hr]
    constructor
    · omega
    · rw [pow_succ]
      have : 0 < 4^(m+1) := by positivity
      omega

private def carries {m : ℕ} (v : Fin m → Fin 2) (i : ℕ) : ℕ :=
  if hi : 0 < i ∧ i ≤ m then (v ⟨i-1, by omega⟩).val else 0

private lemma carries_le {m : ℕ} (v : Fin m → Fin 2) (i : ℕ) : carries v i ≤ 1 := by
  unfold carries
  split_ifs
  · exact Nat.le_of_lt_succ (v _).isLt
  · omega

private lemma carries_zero {m : ℕ} (v : Fin m → Fin 2) : carries v 0 = 0 := by
  simp [carries]

private lemma carries_end {m : ℕ} (v : Fin m → Fin 2) : carries v (m+1) = 0 := by
  simp [carries]

private def carryDigit {m : ℕ} (v : Fin m → Fin 2) (i : ℕ) : ℕ :=
  1 + 4 * carries v (i+1) - carries v i

private lemma carryDigit_balance {m : ℕ} (v : Fin m → Fin 2) (i : ℕ) :
    carryDigit v i + carries v i = 1 + 4 * carries v (i+1) := by
  have := carries_le v i
  unfold carryDigit
  omega

private lemma carryDigit_le {m : ℕ} (v : Fin m → Fin 2) (i : ℕ) : carryDigit v i ≤ 5 := by
  have := carries_le v (i+1)
  unfold carryDigit
  omega

private lemma carry_weight {m : ℕ} (v : Fin m → Fin 2) :
    weight 4 (pack (m+1) (carryDigit v)) = repunit m := by
  rw [weight_pack]
  have hbal : window 4 (m+1) (carryDigit v) + window 4 (m+1) (carries v) =
      repunit m + 4 * window 4 (m+1) (fun i => carries v (i+1)) := by
    simp only [window, repunit, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := carryDigit_balance v i
    calc
      carryDigit v i * 4^i + carries v i * 4^i =
          (carryDigit v i + carries v i) * 4^i := by ring
      _ = (1 + 4*carries v (i+1)) * 4^i := by rw [h]
      _ = 4^i + 4*(carries v (i+1)*4^i) := by ring
  have htail : window 4 (m+1) (fun i => carries v (i+1)) =
      window 4 m (fun i => carries v (i+1)) := by
    simp [window, Finset.sum_range_succ, carries_end]
  rw [window_succ 4 m (carries v), carries_zero, zero_add, htail] at hbal
  omega

private def carryPartition (k m : ℕ) (hk : 5 ≤ k) (v : Fin m → Fin 2) :
    Partitions k 4 (repunit m) :=
  ⟨pack (m+1) (carryDigit v), (by
    intro i
    rw [pack_apply]
    split_ifs
    · exact (carryDigit_le v i).trans hk
    · omega), carry_weight v⟩

private lemma carryPartition_injective (k m : ℕ) (hk : 5 ≤ k) :
    Function.Injective (carryPartition k m hk) := by
  intro u v huv
  have hd : ∀ i, i < m+1 → carryDigit u i = carryDigit v i := by
    intro i hi
    have h := congrArg (fun a : Partitions k 4 (repunit m) => a.val i) huv
    simpa [carryPartition, pack_apply, hi] using h
  have hc : ∀ i, i ≤ m+1 → carries u i = carries v i := by
    intro i
    induction i with
    | zero => simp [carries_zero]
    | succ i ih =>
      intro hi
      have h0 := ih (by omega)
      have h1 := hd i (by omega)
      have h2 := carryDigit_balance u i
      have h3 := carryDigit_balance v i
      omega
  funext i
  apply Fin.ext
  have h := hc (i.val+1) (by omega)
  simpa [carries, show 0 < i.val+1 ∧ i.val+1 ≤ m by omega] using h

/-- All binary interior carry choices are distinct actual finite-support partitions. -/
theorem count_repunit (k m : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 6) :
    count k 4 (repunit m) = 2 ^ m := by
  apply Nat.le_antisymm
  · exact count_upper k m (repunit m) hk' (repunit_bounds m).2
  · letI := partitions_finite k 4 (repunit m) (by norm_num)
    have h := Nat.card_le_card_of_injective (carryPartition k m hk)
      (carryPartition_injective k m hk)
    simpa [Nat.card_fun, count] using h

private lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h ⊢
  exact h

private lemma readout_bounds (k n : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 6) (hn : 2 ≤ n) :
    0 ≤ readout k 4 n ∧ readout k 4 n ≤ (1/2 : ℝ) := by
  have hb := count_positive k 4 n (by norm_num) (by omega)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hs : (count k 4 n : ℝ)^2 ≤ (n : ℝ) := by
    exact_mod_cast count_square_le k n hk' (by omega)
  have hl := Real.log_le_log (by positivity : 0 < (count k 4 n : ℝ)^2) hs
  rw [Real.log_pow] at hl
  constructor
  · exact div_nonneg (Real.log_natCast_nonneg _) hln.le
  · apply (div_le_iff₀ hln).mpr
    norm_num at hl ⊢
    linarith

private lemma readout_repunit_lower (k m : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 6)
    (hm : 1 ≤ m) : (m : ℝ) / (2 * (m+1)) ≤ readout k 4 (repunit m) := by
  have hpow : 4 ≤ 4 ^ m := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hm)
  have hn : 2 ≤ repunit m := by have := (repunit_bounds m).1; omega
  have hnpos : 0 < (repunit m : ℝ) := by positivity
  have hln : 0 < Real.log (repunit m : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : (repunit m : ℝ) ≤ (4 : ℝ) ^ (m+1) := by
    exact_mod_cast (repunit_bounds m).2.le
  have hlog := Real.log_le_log hnpos hp
  rw [Real.log_pow, log_four] at hlog
  unfold readout
  rw [count_repunit k m hk hk', Nat.cast_pow, Real.log_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) * (m+1)) hln).mpr
  norm_num at hlog ⊢
  nlinarith

/-- Every natural tail has exactly this extended-real supremum. -/
theorem tail_supremum (k N : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 6) (hN : 2 ≤ N) :
    (⨆ (n : ℕ) (_ : N ≤ n), (readout k 4 n : EReal)) = ((1/2 : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro hn
    exact EReal.coe_le_coe (readout_bounds k n hk hk' (by omega)).2
  · apply le_of_not_gt
    intro hlt
    obtain ⟨r, hsr, hrh⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hr : r < (1/2 : ℝ) := EReal.coe_lt_coe_iff.mp hrh
    have hd : 0 < 1 - 2*r := by linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (max (N : ℝ) (2*r / (1-2*r)))
    have hmN : N < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm)
    have hmr : 2*r / (1-2*r) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    have hfrac : r < (m : ℝ) / (2 * (m+1)) := by
      have hmul := (div_lt_iff₀ hd).mp hmr
      apply (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) * (m+1))).mpr
      nlinarith
    have hm1 : 1 ≤ m := by omega
    have hmn : m < 4^m := Nat.lt_pow_self (by norm_num)
    have htail : N ≤ repunit m := by have := (repunit_bounds m).1; omega
    have hlow := readout_repunit_lower k m hk hk' hm1
    have hval : (r : EReal) < (readout k 4 (repunit m) : EReal) :=
      EReal.coe_lt_coe (hfrac.trans_le hlow)
    have hsup : (readout k 4 (repunit m) : EReal) ≤
        ⨆ (n : ℕ) (_ : N ≤ n), (readout k 4 n : EReal) :=
      le_iSup_of_le (repunit m) (le_iSup_of_le htail le_rfl)
    exact (not_lt_of_ge hsup) (hsr.trans hval)

/-- The ordinary extended-real all-input exponent, including its finiteness bridge. -/
theorem exponent_eq_half (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 6) :
    exponent k 4 = ((1/2 : ℝ) : EReal) := by
  unfold exponent
  apply le_antisymm
  · exact iInf_le_of_le 2 (iInf_le_of_le (by norm_num : 2 ≤ 2)
      (le_of_eq (tail_supremum k 2 hk hk' (by norm_num))))
  · apply le_iInf
    intro N
    apply le_iInf
    intro hN
    exact le_of_eq (tail_supremum k N hk hk' hN).symm

/-- Literal negation of the complete same-radix strict adjacent-multiplicity event. -/
theorem result : Not claim := by
  intro h
  have hbad := h 4 (by norm_num) 5 (by norm_num)
  rw [exponent_eq_half 5 (by norm_num) (by norm_num),
    exponent_eq_half 6 (by norm_num) (by norm_num)] at hbad
  exact (lt_irrefl _ hbad)

end

end D5.S1.Digit.CoonsAdjacentGrowthRefutation
