/- GID: D5/S1/Digit/DigitCapSubcritical
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapSubcritical
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Caps k <= ell^r-2 give at most Q^(m mod 2) H^(m/2) representations below ell^(m+1). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#300)
escape_witness: pair_sum (two consecutive admissible digits have at most Q^2 - Q/ell joint
  choices), with count_rec (the lowest-digit recursion) and class_card.
proof_shape:
  tail, cons, low: definitions; consumers: the lemmas below.
  fiberEquiv: content (the shift bijection); consumer: count_rec.
  count_rec: content; consumers: count_le, DigitCapNearSquare.count_digit.
  class_card: content; consumer: low_card.
  pair_sum: content; consumer: count_le.
  count_le: content; consumer: subcritical.
  subcritical: content via count_le; the big-O and exponent parts are consequences.
  tail_apply: bind-only helper; consumers: cons_tail, tail_cons, fiberEquiv.
  cons_zero, cons_succ: bind-only helpers; consumers: cons_tail, tail_cons, fiberEquiv.
  cons_tail: bind-only helper; consumers: fiberEquiv, mem_low_of.
  tail_cons: bind-only helper; consumer: fiberEquiv.
  weight_cons: bind-only helper; consumers: mem_low_of, weight_iff.
  mem_low_of, weight_iff: bind-only helpers; consumers: fiberEquiv, count_rec.
  low_card: bind-only helper; consumer: pair_sum.
  mod_eq_pred_iff: bind-only helper; consumer: pred_iff.
  pred_iff, residue_count: bind-only helpers; consumer: pair_sum.
Direct frozen dependencies: D5/S1/Digit/CoonsAdjacentGrowthRefutation (weight, Partitions,
  count, partitions_finite; statement_id
  sha256:adc04d4c318958807e0c995604326199d16ca889d5bd0f774bec45e46b1859ac),
  D5/S1/Digit/DigitCapQuotientBound (count_le_pow, used for m = 0, 1; statement_id
  sha256:42d2c162c57dd56b82a21271074f17ced8b073d04c7ea0af96bef4ee50b37da4).
Search record (§3.1): no lowest-digit recursion exists in D5; the nearest is
  DigitCapMultipleCount.count_multiple (a quotient/remainder split, for caps a·ell − 1 only).
  DigitCapQuotientBound.count_le_pow gives Q^m; this module improves it to
  Q^(m mod 2) H^⌊m/2⌋ for caps at most ell^r − 2. Mathlib's Finsupp.cons/tail exist only on
  Fin (n+1); Mathlib's Nat.count_modEq_card gives the residue count.
-/

import D5.S1.Digit.DigitCapQuotientBound
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # A uniform subcritical bound for digit caps below `ell ^ r - 1`

For a radix `ell ≥ 2`, `r ≥ 2`, a digit cap `k ≤ ell ^ r - 2` and `n < ell ^ (m + 1)`, put
`Q = ell ^ (r - 1)` and `H = Q ^ 2 - Q / ell`. Then `b(k, ell, n) ≤ Q ^ (m mod 2) H ^ ⌊m/2⌋`.
Each lowest digit lies in the residue class of `n`, which has at most `Q` members up to the cap,
and the class `ell - 1` only `Q - 1`. Two consecutive digits therefore have at most `H` joint
choices: as the lower digit runs through its class, the class of the next digit runs through
every residue `Q / ell` times. Hence `b(k, ell, n) = O(n ^ ((log_ell H) / 2))` with
`(log_ell H) / 2 < r - 1`.
-/

set_option autoImplicit false

namespace D5.S1.Digit.DigitCapSubcritical

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open Finset

noncomputable section

/-- Dropping the lowest digit. -/
private def tail (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.comapDomain Nat.succ a Nat.succ_injective.injOn

private lemma tail_apply (a : ℕ →₀ ℕ) (i : ℕ) : tail a i = a (i + 1) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Prepending a lowest digit. -/
private def cons (d : ℕ) (b : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 d + Finsupp.mapDomain Nat.succ b

private lemma cons_zero (d : ℕ) (b : ℕ →₀ ℕ) : cons d b 0 = d := by
  unfold cons
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp), add_zero]

private lemma cons_succ (d : ℕ) (b : ℕ →₀ ℕ) (i : ℕ) : cons d b (i + 1) = b i := by
  unfold cons
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), zero_add]
  exact Finsupp.mapDomain_apply_of_injective Nat.succ_injective b i

private lemma cons_tail (a : ℕ →₀ ℕ) : cons (a 0) (tail a) = a := by
  ext i
  cases i with
  | zero => exact cons_zero _ _
  | succ i => rw [cons_succ, tail_apply]

private lemma tail_cons (d : ℕ) (b : ℕ →₀ ℕ) : tail (cons d b) = b := by
  ext i
  rw [tail_apply, cons_succ]

private lemma weight_cons (ell d : ℕ) (b : ℕ →₀ ℕ) :
    weight ell (cons d b) = d + ell * weight ell b := by
  unfold weight cons
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_mapDomain_index (fun _ => by simp)
      (fun _ _ _ => by ring), Finsupp.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  apply Finsupp.sum_congr
  intro i _
  ring

/-- The admissible lowest digits of `n`. -/
def low (k ell n : ℕ) : Finset ℕ :=
  (range (k + 1)).filter fun d => d ≤ n ∧ d % ell = n % ell

private lemma mem_low_of (k ell n : ℕ) (a : Partitions k ell n) : a.1 0 ∈ low k ell n := by
  simp only [low, mem_filter, mem_range]
  have hw := a.2.2
  rw [← cons_tail a.1, weight_cons] at hw
  refine ⟨Nat.lt_succ_of_le (a.2.1 0), by omega, ?_⟩
  exact (Nat.add_mul_mod_self_left _ _ _).symm.trans (congrArg (· % ell) hw)

private lemma weight_iff (k ell n : ℕ) (hell : 2 ≤ ell) (d : ℕ) (b : ℕ →₀ ℕ)
    (hd : d ∈ low k ell n) : weight ell b = (n - d) / ell ↔ weight ell (cons d b) = n := by
  simp only [low, mem_filter, mem_range] at hd
  have hdvd : ell ∣ n - d := (Nat.modEq_iff_dvd' hd.2.1).mp hd.2.2
  rw [weight_cons]
  constructor
  · intro h
    rw [h, Nat.mul_div_cancel' hdvd]
    omega
  · intro h
    have : ell * weight ell b = n - d := by omega
    rw [← this, Nat.mul_div_cancel_left _ (by omega)]

/-- The representations of `n` with lowest digit `d` are those of `(n - d) / ell`, shifted. -/
private def fiberEquiv (k ell n : ℕ) (hell : 2 ≤ ell) (d : low k ell n) :
    {a : Partitions k ell n // (⟨a.1 0, mem_low_of k ell n a⟩ : low k ell n) = d} ≃
      Partitions k ell ((n - d) / ell) where
  toFun a := ⟨tail a.1.1, fun i => by rw [tail_apply]; exact a.1.2.1 _, by
    have h0 : a.1.1 0 = d := congrArg Subtype.val a.2
    apply (weight_iff k ell n hell d _ d.2).mpr
    rw [← h0, cons_tail]
    exact a.1.2.2⟩
  invFun b := ⟨⟨cons d b.1, fun i => by
      cases i with
      | zero =>
        rw [cons_zero]
        have := d.2
        simp only [low, mem_filter, mem_range] at this
        omega
      | succ i => rw [cons_succ]; exact b.2.1 i,
    (weight_iff k ell n hell d b.1 d.2).mp b.2.2⟩, by
      apply Subtype.ext
      exact cons_zero _ _⟩
  left_inv a := by
    have h0 : a.1.1 0 = d := congrArg Subtype.val a.2
    apply Subtype.ext
    apply Subtype.ext
    simp only
    rw [← h0, cons_tail]
  right_inv b := by
    apply Subtype.ext
    exact tail_cons _ _

/-- The digit recursion `b(k, ell, n) = ∑_{d} b(k, ell, (n - d) / ell)` over the admissible
lowest digits `d`. -/
theorem count_rec (k ell n : ℕ) (hell : 2 ≤ ell) :
    count k ell n = ∑ d ∈ low k ell n, count k ell ((n - d) / ell) := by
  have : Finite (Partitions k ell n) := partitions_finite k ell n hell
  let f : Partitions k ell n → low k ell n := fun a => ⟨a.1 0, mem_low_of k ell n a⟩
  unfold count
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    ← Finset.sum_coe_sort (low k ell n)]
  apply Finset.sum_congr rfl
  intro d _
  exact Nat.card_congr (fiberEquiv k ell n hell d)

/-- A residue class of digits up to a cap `k ≤ ell ^ r - 2` has at most `ell ^ (r - 1)` members,
and the class `ell - 1` at most `ell ^ (r - 1) - 1`. -/
private lemma class_card (ell r k c : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2)
    (hc : c < ell) :
    ((range (k + 1)).filter fun d => d % ell = c).card + (if c = ell - 1 then 1 else 0) ≤
      ell ^ (r - 1) := by
  set Q := ell ^ (r - 1) with hQ
  have hpow : ell ^ r = ell * Q := by
    rw [hQ, ← pow_succ']; congr 1; omega
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hsub : ((range (k + 1)).filter fun d => d % ell = c).card ≤
      (range (Q - (if c = ell - 1 then 1 else 0))).card := by
    apply Finset.card_le_card_of_injOn (fun d => d / ell)
    · intro d hd
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hd
      simp only [coe_range, Set.mem_Iio]
      have hdm := Nat.div_add_mod d ell
      by_contra hlt
      push Not at hlt
      have hmul : ell * (Q - (if c = ell - 1 then 1 else 0)) ≤ ell * (d / ell) :=
        Nat.mul_le_mul_left _ hlt
      have hsub1 : ell * (Q - 1) = ell * Q - ell := Nat.mul_sub_one _ _
      have hle : ell ≤ ell * Q := Nat.le_mul_of_pos_right _ hQ1
      split_ifs at hmul with hce
      · rw [hsub1] at hmul
        omega
      · rw [Nat.sub_zero] at hmul
        omega
    · intro d hd d' hd' h
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hd hd'
      have := Nat.div_add_mod d ell
      have := Nat.div_add_mod d' ell
      simp only at h
      rw [← Nat.div_add_mod d ell, ← Nat.div_add_mod d' ell, h, hd.2, hd'.2]
  rw [card_range] at hsub
  split_ifs at hsub ⊢ <;> omega

/-- The admissible lowest digits of `n` number at most `ell ^ (r - 1)`, one fewer when
`n ≡ -1`. -/
private lemma low_card (ell r k n : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2) :
    (low k ell n).card + (if n % ell = ell - 1 then 1 else 0) ≤ ell ^ (r - 1) := by
  have h := class_card ell r k (n % ell) hell hr hk (Nat.mod_lt _ (by omega))
  have hsub : low k ell n ⊆ (range (k + 1)).filter fun d => d % ell = n % ell := by
    intro d hd
    simp only [low, mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.2⟩
  have := Finset.card_le_card hsub
  omega

/-- `x ≡ -1 (mod ell)` exactly when `ell` divides `x + 1`. -/
private lemma mod_eq_pred_iff (ell x : ℕ) (hell : 2 ≤ ell) :
    x % ell = ell - 1 ↔ ell ∣ x + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < ell by omega)]
  have hy := Nat.mod_lt x (show 0 < ell by omega)
  constructor
  · intro h
    rw [h, Nat.sub_add_cancel (by omega), Nat.mod_self]
  · intro h
    by_contra hne
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- For `t ≤ A`, `A - t ≡ -1 (mod ell)` exactly when `t ≡ A + 1`. -/
private lemma pred_iff (ell A t : ℕ) (hell : 2 ≤ ell) (ht : t ≤ A) :
    (A - t) % ell = ell - 1 ↔ t % ell = (A + 1) % ell := by
  rw [mod_eq_pred_iff ell _ hell, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff']
  push_cast [Nat.cast_sub ht]
  constructor <;> intro h <;> linear_combination (-1 : ZMod ell) * h

/-- Each residue occurs `Q / ell` times below a multiple `Q` of `ell`. -/
private lemma residue_count (ell Q v : ℕ) (hell : 0 < ell) (hd : ell ∣ Q) :
    ((range Q).filter fun t => t % ell = v % ell).card = Q / ell := by
  rw [← Nat.count_eq_card_filter_range]
  have := Nat.count_modEq_card (r := ell) (b := Q) hell v
  rw [Nat.mod_eq_zero_of_dvd hd] at this
  simp only [Nat.not_lt_zero, ↓reduceIte, add_zero] at this
  rw [← this]
  rfl

/-- Two consecutive digits have at most `Q ^ 2 - Q / ell` joint choices. -/
private lemma pair_sum (ell r k n : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2) :
    ∑ d ∈ low k ell n, (low k ell ((n - d) / ell)).card ≤
      ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell := by
  set Q := ell ^ (r - 1) with hQ
  set A := n / ell with hA
  have hpow : ell ^ r = Q * ell := by rw [hQ, ← pow_succ]; congr 1; omega
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  let g : ℕ → ℕ := fun t => Q - (if t % ell = (A + 1) % ell then 1 else 0)
  have hpt : ∀ d ∈ low k ell n, (low k ell ((n - d) / ell)).card ≤ g (d / ell) := by
    intro d hd
    have hc := low_card ell r k ((n - d) / ell) hell hr hk
    rw [← hQ] at hc
    have hd' := hd
    simp only [low, mem_filter, mem_range] at hd'
    have hle : d / ell ≤ A := Nat.div_le_div_right hd'.2.1
    have heq : (n - d) / ell = A - d / ell := by
      have h1 := Nat.div_add_mod n ell
      have h2 := Nat.div_add_mod d ell
      have hm : ell * (d / ell) ≤ ell * A := Nat.mul_le_mul_left _ hle
      have : n - d = ell * (A - d / ell) := by
        rw [Nat.mul_sub]
        have hdm := hd'.2.2
        generalize ell * (d / ell) = P at h2 hm ⊢
        generalize ell * A = O at h1 hm ⊢
        omega
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [heq] at hc ⊢
    by_cases hcase : (A - d / ell) % ell = ell - 1
    · have h' := (pred_iff ell A (d / ell) hell hle).mp hcase
      simp only [g, h', ↓reduceIte]
      simp only [hcase, ↓reduceIte] at hc
      omega
    · have h' : ¬ (d / ell) % ell = (A + 1) % ell :=
        fun h => hcase ((pred_iff ell A (d / ell) hell hle).mpr h)
      simp only [g, h', ↓reduceIte]
      simp only [hcase, ↓reduceIte] at hc
      omega
  have hinj : Set.InjOn (fun d => d / ell) (low k ell n : Set ℕ) := by
    intro d hd d' hd' h
    simp only [coe_filter, low, mem_range, Set.mem_ofPred_eq] at hd hd'
    simp only at h
    rw [← Nat.div_add_mod d ell, ← Nat.div_add_mod d' ell, h, hd.2.2, hd'.2.2]
  have himg : (low k ell n).image (fun d => d / ell) ⊆ range Q := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
    simp only [low, mem_filter, mem_range] at hd
    rw [mem_range]
    have hdk : d < ell * Q := by
      have h1 : d < k + 1 := hd.1
      have h2 : ell * Q = ell ^ r := by rw [Nat.mul_comm]; exact hpow.symm
      have h3 : 2 ≤ ell ^ r := le_trans hell (Nat.le_self_pow (by omega) ell)
      omega
    exact Nat.div_lt_of_lt_mul hdk
  have htotal : ∑ t ∈ range Q, g t + ((range Q).filter fun t => t % ell = (A + 1) % ell).card =
      Q * Q := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun t _ => show g t + (if t % ell = (A + 1) % ell then 1 else 0) = Q
      by simp only [g]; split_ifs <;> omega), Finset.sum_const, card_range, smul_eq_mul]
  have hres := residue_count ell Q (A + 1) (by omega) (dvd_pow_self ell (by omega))
  calc ∑ d ∈ low k ell n, (low k ell ((n - d) / ell)).card
      ≤ ∑ d ∈ low k ell n, g (d / ell) := Finset.sum_le_sum hpt
    _ = ∑ t ∈ (low k ell n).image (fun d => d / ell), g t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ range Q, g t :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => Nat.zero_le _)
    _ = Q * Q - Q / ell := by omega

/-- For `r ≥ 2`, a cap `k ≤ ell ^ r - 2` and `n < ell ^ (m + 1)`, the bounded-digit
representations number at most `Q ^ (m mod 2) H ^ ⌊m/2⌋`, with `Q = ell ^ (r-1)` and
`H = Q ^ 2 - Q / ell`. -/
private lemma count_le (ell r k : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2) :
    ∀ m n, n < ell ^ (m + 1) → count k ell n ≤
      (ell ^ (r - 1)) ^ (m % 2) *
        (ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell) ^ (m / 2) := by
  set Q := ell ^ (r - 1) with hQ
  have hpow : ell ^ r = Q * ell := by rw [hQ, ← pow_succ]; congr 1; omega
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hkq : k ≤ Q * ell - 1 := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hn
    match m, ih, hn with
    | 0, _, hn =>
      have := DigitCapQuotientBound.count_le_pow ell Q 0 k n hell hQ1 hkq hn
      simpa using this
    | 1, _, hn =>
      have := DigitCapQuotientBound.count_le_pow ell Q 1 k n hell hQ1 hkq hn
      simpa using this
    | m + 2, ih, hn =>
      have hdiv : ∀ x, x < ell ^ (m + 3) → x / ell / ell < ell ^ (m + 1) := by
        intro x hx
        rw [Nat.div_div_eq_div_mul]
        apply Nat.div_lt_of_lt_mul
        calc x < ell ^ (m + 3) := hx
          _ = ell * ell * ell ^ (m + 1) := by ring
      set B := Q ^ (m % 2) * (Q * Q - Q / ell) ^ (m / 2)
      have hstep : ∀ d ∈ low k ell n,
          count k ell ((n - d) / ell) ≤ (low k ell ((n - d) / ell)).card * B := by
        intro d _
        rw [count_rec k ell _ hell, ← smul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_le_sum
        intro d' _
        apply ih m (by omega)
        calc ((n - d) / ell - d') / ell ≤ (n - d) / ell / ell :=
              Nat.div_le_div_right (Nat.sub_le _ _)
          _ ≤ n / ell / ell := Nat.div_le_div_right (Nat.div_le_div_right (Nat.sub_le _ _))
          _ < ell ^ (m + 1) := hdiv n (by simpa [show m + 2 + 1 = m + 3 by ring] using hn)
      rw [count_rec k ell n hell]
      calc ∑ d ∈ low k ell n, count k ell ((n - d) / ell)
          ≤ ∑ d ∈ low k ell n, (low k ell ((n - d) / ell)).card * B := Finset.sum_le_sum hstep
        _ = (∑ d ∈ low k ell n, (low k ell ((n - d) / ell)).card) * B := by
            rw [Finset.sum_mul]
        _ ≤ (Q * Q - Q / ell) * B := Nat.mul_le_mul_right _ (pair_sum ell r k n hell hr hk)
        _ = Q ^ ((m + 2) % 2) * (Q * Q - Q / ell) ^ ((m + 2) / 2) := by
            rw [show (m + 2) % 2 = m % 2 by omega, show (m + 2) / 2 = m / 2 + 1 by omega,
              pow_succ]
            ring

/-- For a radix `ell ≥ 2`, `r ≥ 2` and a digit cap `k ≤ ell ^ r - 2`, put `Q = ell ^ (r - 1)`
and `H = Q ^ 2 - Q / ell`. Every `n < ell ^ (m + 1)` has at most `Q ^ (m mod 2) H ^ ⌊m/2⌋`
representations with digits at most `k`; consequently `b(k, ell, n) = O(n ^ ((log_ell H) / 2))`,
and `(log_ell H) / 2 < r - 1`. -/
theorem subcritical (ell r k : ℕ) (hell : 2 ≤ ell) (hr : 2 ≤ r) (hk : k ≤ ell ^ r - 2) :
    (∀ m n, n < ell ^ (m + 1) → count k ell n ≤
      (ell ^ (r - 1)) ^ (m % 2) *
        (ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell) ^ (m / 2)) ∧
    (fun n : ℕ => (count k ell n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^
      (Real.logb ell ((ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell : ℕ) : ℝ) / 2)) ∧
    Real.logb ell ((ell ^ (r - 1) * ell ^ (r - 1) - ell ^ (r - 1) / ell : ℕ) : ℝ) / 2 <
      (r : ℝ) - 1 := by
  have hbound := count_le ell r k hell hr hk
  set Q := ell ^ (r - 1) with hQ
  set H := Q * Q - Q / ell with hH
  have hQell : ell ≤ Q := by
    rw [hQ]
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ (r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hdivpos : 1 ≤ Q / ell := (Nat.one_le_div_iff (by omega)).mpr hQell
  have hdivle : Q / ell ≤ Q := Nat.div_le_self _ _
  have hQQ : Q ≤ Q * Q := Nat.le_mul_of_pos_left _ (by omega)
  have hH1 : 1 ≤ H := by
    have h2 : 2 * Q ≤ Q * Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have hHlt : H < Q * Q := by omega
  have hellR : (1 : ℝ) < ell := by exact_mod_cast (show 1 < ell by omega)
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  refine ⟨hbound, ?_, ?_⟩
  · apply Asymptotics.IsBigO.of_bound (Q : ℝ)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    set m := Nat.log ell n
    have hn1 : n < ell ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) n
    have hn2 : ell ^ m ≤ n := Nat.pow_log_le_self ell (by omega)
    have hc := hbound m n hn1
    have hqm : Q ^ (m % 2) ≤ Q := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h, pow_zero]; omega
      · rw [h, pow_one]
    have hcQ : count k ell n ≤ Q * H ^ (m / 2) :=
      hc.trans (Nat.mul_le_mul_right _ hqm)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hpow : ((H : ℝ) ^ (m / 2 : ℕ)) ≤ (n : ℝ) ^ (Real.logb ell H / 2) := by
      have hHpos : (0 : ℝ) < H := by linarith
      calc ((H : ℝ) ^ (m / 2 : ℕ)) = (H : ℝ) ^ (((m / 2 : ℕ) : ℝ)) :=
            (Real.rpow_natCast _ _).symm
        _ ≤ (H : ℝ) ^ ((m : ℝ) / 2) := by
            apply Real.rpow_le_rpow_of_exponent_le hHR
            rw [le_div_iff₀ (by norm_num)]
            exact_mod_cast (show m / 2 * 2 ≤ m by omega)
        _ = ((ell : ℝ) ^ (m : ℝ)) ^ (Real.logb ell H / 2) := by
            conv_lhs => rw [← Real.rpow_logb (by positivity) hellR.ne' hHpos]
            rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
            ring_nf
        _ ≤ (n : ℝ) ^ (Real.logb ell H / 2) := by
            apply Real.rpow_le_rpow (by positivity) _
              (div_nonneg (Real.logb_nonneg hellR hHR) (by norm_num))
            rw [Real.rpow_natCast]
            exact_mod_cast hn2
    calc (count k ell n : ℝ) ≤ (Q : ℝ) * (H : ℝ) ^ (m / 2 : ℕ) := by exact_mod_cast hcQ
      _ ≤ (Q : ℝ) * (n : ℝ) ^ (Real.logb ell H / 2) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  · have hHpos : (0 : ℝ) < H := by linarith
    have hlt : Real.logb ell H < 2 * ((r : ℝ) - 1) := by
      rw [Real.logb_lt_iff_lt_rpow hellR hHpos]
      have hQQR : ((Q * Q : ℕ) : ℝ) = (ell : ℝ) ^ (2 * ((r : ℝ) - 1)) := by
        rw [show (2 : ℝ) * ((r : ℝ) - 1) = ((r - 1 + (r - 1) : ℕ) : ℝ) by
          push_cast [Nat.cast_sub (show 1 ≤ r by omega)]; ring, Real.rpow_natCast, pow_add, hQ]
        push_cast
        ring
      rw [← hQQR]
      exact_mod_cast hHlt
    linarith

end

end D5.S1.Digit.DigitCapSubcritical
