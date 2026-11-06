/- GID: D5/S3/Combinatorics/Circle/Orbit/RadixFourDigitBalance
   generality: I
   mirror-B: none(source-preparation-only)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin,
     mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Centered radix-four balance and the full binomial actual even-trace spectrum. -/

import D5.S3.Combinatorics.Circle.Orbit.RadixFourNonunitZeroSubsets
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Abel

/-!
UNCOMPILED SOURCE CANDIDATE. This file has not been elaborated or kernel checked.
The accompanying visibility.patch exposes only existing arithmetic used below
in the immutable radix-four source. It changes no proof or theorem statement.

The live source is SourceWidth.actualSource at the original evenLabel inclusion
into Fin (2*n). All natural seeds are allowed, including zero and nonunits.
The spectrum counts DISTINCT SEEDS in every literal integer even-trace fibre.
Its central specialization counts the seeds whose trace is zero. It makes no
assertion about the number of physical zero subsets, full_J, or the centered
doubleStep period in TwoRunSource.

Word arithmetic: a word's centered representative is its value minus N precisely
when its top digit is at least two. The all-three word has value N, and this
formula gives zero, so it is retained throughout the word trace argument.
Digit combinatorics: d=u+2*v is sent to the bit pair (u,1-v), in two labelled
copies of Fin n. These are length 2*n bits through finSumFinEquiv and
finCongr (Nat.two_mul n).symm. Their weight is n+balance. Delete exactly the
all-three word AFTER counting words of each weight r; every remaining value
is < N. This word has weight n, so the correction is exactly if r=n then 1
else 0. The powersetCard count covers every natural r, also r>2*n.

Library reuse: finFunctionFinEquiv supplies BOTH radix-value injectivity and
the exact inverse (a / 4^i) % 4. power_rotation, pow_four, digitSum_three and
modulus_three come from RadixFourNonunitZeroSubsets, not copied proofs.
centered_unique/centered_mod/centered_bounds are SourceWidth's existing laws.
source_cycle is used for modulus positivity; no unsigned coboundary or
actual_recurrence is re-proved. Every private helper feeds the public laws.
The original zero-trace seed count is derived from the full spectrum at r=n.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.RadixFourDigitBalance

open SourceWidth RadixFourNonunitZeroSubsets
open scoped BigOperators

/-- The integer trace at the actual even physical labels. -/
def evenTrace (n t : ℕ) : ℤ :=
  ∑ i : Fin n, actualSource (2 * n) t (evenLabel i)

private abbrev Word (n : ℕ) := Fin n → Fin 4

private def value {n : ℕ} (d : Word n) : ℕ :=
  (finFunctionFinEquiv d).val

private theorem value_formula {n : ℕ} (d : Word n) :
    value d = ∑ j : Fin n, (d j).val * 4 ^ j.val :=
  finFunctionFinEquiv_apply d

private theorem modulus_nat (n : ℕ) :
    ((4 ^ n - 1 : ℕ) : ℤ) = modulus (2 * n) := by
  rw [RadixFourNonunitZeroSubsets.pow_four n, Nat.cast_sub Nat.one_le_two_pow]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, modulus]

private theorem modulus_pos {n : ℕ} (hn : 0 < n) :
    0 < modulus (2 * n) :=
  (ZeroSumSubsets.source_cycle (by omega : 0 < 2 * n) 0).1

private theorem nat_modulus_pos {n : ℕ} (hn : 0 < n) :
    0 < 4 ^ n - 1 := by
  have h := modulus_pos hn
  rw [← modulus_nat] at h
  exact_mod_cast h

private def high (a : Fin 4) : ℤ := if 2 ≤ a.val then 1 else 0

private def charge (a : Fin 4) : ℤ :=
  (if a.val = 1 then 1 else 0) - (if a.val = 2 then 1 else 0)

private def balance {n : ℕ} (d : Word n) : ℤ := ∑ j : Fin n, charge (d j)

private theorem digit_charge (a : Fin 4) :
    (a.val : ℤ) = charge a + 3 * high a := by
  have ha := a.isLt
  dsimp [charge, high]
  split_ifs <;> omega

private theorem card_filter_int {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((Finset.univ.filter p).card : ℤ) =
      ∑ j : Fin n, if p j then (1 : ℤ) else 0 := by
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> norm_num

private theorem balance_counts {n : ℕ} (d : Word n) :
    balance d =
      ((Finset.univ.filter (fun j : Fin n => (d j).val = 1)).card : ℤ) -
      ((Finset.univ.filter (fun j : Fin n => (d j).val = 2)).card : ℤ) := by
  rw [card_filter_int, card_filter_int, ← Finset.sum_sub_distrib]
  rfl

private def top {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- The endpoint value N is allowed: for the all-three word the RHS is N-N. -/
private theorem centered_value {n : ℕ} (hn : 0 < n) (d : Word n) :
    centered (modulus (2 * n)) (value d) =
      (value d : ℤ) - modulus (2 * n) * high (d (top hn)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  let p : Word m := fun j => d j.castSucc
  have hp0 : (0 : ℤ) ≤ value p := Nat.cast_nonneg _
  have hp : (value p : ℤ) < (4 : ℤ) ^ m := by
    exact_mod_cast (finFunctionFinEquiv p).isLt
  have hv : (value d : ℤ) =
      (value p : ℤ) + ((d (Fin.last m)).val : ℤ) * (4 : ℤ) ^ m := by
    simp only [value_formula, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, p]
  have hfour : (4 : ℤ) ^ (m + 1) = (2 : ℤ) ^ (2 * (m + 1)) := by
    exact_mod_cast RadixFourNonunitZeroSubsets.pow_four (m + 1)
  have hNform : modulus (2 * (m + 1)) = 4 * (4 : ℤ) ^ m - 1 := by
    rw [modulus, ← hfour, pow_succ]
    ring
  have hN := modulus_pos hn
  have hodd : modulus (2 * (m + 1)) % 2 = 1 := by rw [hNform]; omega
  have hhalf : 2 * (modulus (2 * (m + 1)) / 2) + 1 =
      modulus (2 * (m + 1)) := by
    have h := Int.emod_add_mul_ediv (modulus (2 * (m + 1))) 2
    omega
  have hq : (0 : ℤ) ≤ (4 : ℤ) ^ m := le_of_lt (pow_pos (by norm_num) _)
  have hv0 : (0 : ℤ) ≤ value d := Nat.cast_nonneg _
  have hvN : (value d : ℤ) ≤ modulus (2 * (m + 1)) := by
    have hvNat : value d ≤ 4 ^ (m + 1) - 1 := by
      have h := (finFunctionFinEquiv d).isLt
      change value d < 4 ^ (m + 1) at h
      omega
    rw [← modulus_nat]
    exact_mod_cast hvNat
  have htop : top hn = Fin.last m := by apply Fin.ext; simp [top]
  have hb : -(modulus (2 * (m + 1)) / 2) ≤
      (value d : ℤ) - modulus (2 * (m + 1)) * high (d (top hn)) ∧
      (value d : ℤ) - modulus (2 * (m + 1)) * high (d (top hn)) ≤
        modulus (2 * (m + 1)) / 2 := by
    rw [htop]
    unfold high
    split_ifs with hd
    · have hd2 : (2 : ℤ) ≤ (d (Fin.last m)).val := by exact_mod_cast hd
      have hlo := mul_le_mul_of_nonneg_right hd2 hq
      constructor <;> nlinarith
    · have hd1 : ((d (Fin.last m)).val : ℤ) ≤ 1 := by omega
      have hhi := mul_le_mul_of_nonneg_right hd1 hq
      constructor <;> nlinarith
  apply centered_unique hN hodd (centered_bounds hN hodd _) hb
  rw [centered_mod]
  simp [Int.sub_emod, Int.mul_emod]

private def rotated {n : ℕ} (d : Word n) (i : Fin n) : Word n :=
  fun j => d ((finCycle i).symm j)

private theorem rotated_value {n : ℕ} (d : Word n) (i : Fin n) :
    (value (rotated d i) : ℤ) =
      ∑ j : Fin n, ((d j).val : ℤ) * (4 : ℤ) ^ (finCycle i j).val := by
  rw [value_formula]
  push_cast
  have h := Equiv.sum_comp (finCycle i)
    (fun j : Fin n => ((d ((finCycle i).symm j)).val : ℤ) * (4 : ℤ) ^ j.val)
  simpa only [rotated, Equiv.symm_apply_apply] using h.symm

private theorem actual_word_value {n : ℕ} (d : Word n) (i : Fin n) :
    actualSource (2 * n) (value d) (evenLabel i) =
      centered (modulus (2 * n)) (value (rotated d i)) := by
  have hs (s : Finset (Fin n)) :
      (∑ j ∈ s, ((d j).val : ℤ) * (4 : ℤ) ^ (finCycle i j).val) ≡
        ∑ j ∈ s, ((d j).val : ℤ) *
          ((4 : ℤ) ^ i.val * (4 : ℤ) ^ j.val) [ZMOD modulus (2 * n)] := by
    induction s using Finset.induction_on with
    | empty => exact Int.ModEq.refl _
    | @insert j s hj ih =>
      simpa only [Finset.sum_insert hj] using
        ((Int.ModEq.refl ((d j).val : ℤ)).mul (power_rotation i j)).add ih
  have hr : (∑ j : Fin n, ((d j).val : ℤ) *
      ((4 : ℤ) ^ i.val * (4 : ℤ) ^ j.val)) = (4 : ℤ) ^ i.val * value d := by
    rw [value_formula]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he := hs Finset.univ
  rw [← rotated_value d i, hr] at he
  have hpow : (4 : ℤ) ^ i.val = (2 : ℤ) ^ (evenLabel i).val := by
    dsimp [evenLabel]
    exact_mod_cast RadixFourNonunitZeroSubsets.pow_four i.val
  rw [hpow] at he
  exact centered_congr he.symm

private theorem rotated_sum {n : ℕ} (d : Word n) :
    (∑ i : Fin n, (value (rotated d i) : ℤ)) =
      (digitSum n : ℤ) * ∑ j : Fin n, ((d j).val : ℤ) := by
  simp_rw [rotated_value]
  rw [Finset.sum_comm]
  have hc (j : Fin n) :
      (∑ i : Fin n, (4 : ℤ) ^ (finCycle i j).val) = (digitSum n : ℤ) := by
    have h := Equiv.sum_comp (finCycle j) (fun i : Fin n => (4 : ℤ) ^ i.val)
    simpa only [finCycle_apply, add_comm, digitSum, Nat.cast_sum,
      Nat.cast_pow, Nat.cast_ofNat] using h
  simp_rw [← Finset.mul_sum, hc]
  rw [← Finset.sum_mul]
  ring

private theorem rotated_high_sum {n : ℕ} (hn : 0 < n) (d : Word n) :
    (∑ i : Fin n, high (rotated d i (top hn))) = ∑ j : Fin n, high (d j) := by
  letI : NeZero n := ⟨ne_of_gt hn⟩
  let e : Equiv.Perm (Fin n) :=
    { toFun := fun i => top hn - i
      invFun := fun i => top hn - i
      left_inv := by intro i; exact sub_sub_cancel _ _
      right_inv := by intro i; exact sub_sub_cancel _ _ }
  change (∑ i : Fin n, high (d (e i))) = ∑ j : Fin n, high (d j)
  exact Equiv.sum_comp e (fun j => high (d j))

private theorem actual_word_trace {n : ℕ} (hn : 0 < n) (d : Word n) :
    3 * evenTrace n (value d) = modulus (2 * n) * balance d := by
  have ha (i : Fin n) : actualSource (2 * n) (value d) (evenLabel i) =
      (value (rotated d i) : ℤ) - modulus (2 * n) * high (rotated d i (top hn)) := by
    rw [actual_word_value, centered_value hn]
  have hd : (∑ j : Fin n, ((d j).val : ℤ)) =
      balance d + 3 * ∑ j : Fin n, high (d j) := by
    simp_rw [digit_charge]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  unfold evenTrace
  simp_rw [ha]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, rotated_sum,
    rotated_high_sum hn, hd]
  simp only [modulus_three]
  ring

private def wordForSeed {n : ℕ} (t : Fin (4 ^ n - 1)) : Word n :=
  finFunctionFinEquiv.symm ⟨t.val, lt_of_lt_of_le t.isLt (Nat.sub_le _ _)⟩

private theorem value_wordForSeed {n : ℕ} (t : Fin (4 ^ n - 1)) :
    value (wordForSeed t) = t.val := by
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply _)

private theorem wordForSeed_digit {n : ℕ} (t : Fin (4 ^ n - 1)) (i : Fin n) :
    (wordForSeed t i).val = (t.val / 4 ^ i.val) % 4 := rfl

private theorem evenTrace_mod (n t : ℕ) :
    evenTrace n t = evenTrace n (t % (4 ^ n - 1)) := by
  unfold evenTrace
  apply Finset.sum_congr rfl
  intro i _
  apply centered_congr
  have hs : (t : ℤ) ≡ ((t % (4 ^ n - 1) : ℕ) : ℤ) [ZMOD modulus (2 * n)] := by
    change (t : ℤ) % modulus (2 * n) =
      ((t % (4 ^ n - 1) : ℕ) : ℤ) % modulus (2 * n)
    rw [← modulus_nat]
    simp only [← Int.natCast_mod, Nat.mod_mod]
  exact (Int.ModEq.refl ((2 : ℤ) ^ (evenLabel i).val)).mul hs

/-- All natural seeds, with the literal fixed-length digits of t modulo 4^n-1.
No gcd, unit, nonzero, or lower-bound-on-n-except-positive condition occurs. -/
theorem actual_even_digit_balance {n : ℕ} (hn : 0 < n) (t : ℕ) :
    3 * evenTrace n t = modulus (2 * n) *
      (((Finset.univ.filter (fun i : Fin n =>
        ((t % (4 ^ n - 1)) / 4 ^ i.val) % 4 = 1)).card : ℤ) -
       ((Finset.univ.filter (fun i : Fin n =>
        ((t % (4 ^ n - 1)) / 4 ^ i.val) % 4 = 2)).card : ℤ)) := by
  let s : Fin (4 ^ n - 1) := ⟨t % (4 ^ n - 1), Nat.mod_lt _ (nat_modulus_pos hn)⟩
  have h := actual_word_trace hn (wordForSeed s)
  rw [value_wordForSeed, balance_counts] at h
  simp_rw [wordForSeed_digit] at h
  rw [evenTrace_mod n t]
  exact h

private theorem seed_trace_iff {n : ℕ} (hn : 0 < n)
    (t : Fin (4 ^ n - 1)) (r : ℕ) :
    3 * evenTrace n t.val = modulus (2 * n) * ((r : ℤ) - (n : ℤ)) ↔
      balance (wordForSeed t) = (r : ℤ) - (n : ℤ) := by
  have h := actual_word_trace hn (wordForSeed t)
  rw [value_wordForSeed] at h
  rw [h]
  constructor
  · exact mul_left_cancel₀ (ne_of_gt (modulus_pos hn))
  · intro hb
    rw [hb]

/- The explicit map (u,v) -> (u,1-v). Sum.inl and Sum.inr are labelled
   halves, so this is an actual bijection of words, not an equinumerosity guess. -/
private def bits {n : ℕ} (d : Word n) : Finset (Fin n ⊕ Fin n) :=
  (Finset.univ.filter (fun i : Fin n => (d i).val % 2 = 1)).disjSum
    (Finset.univ.filter (fun i : Fin n => (d i).val / 2 = 0))

private def fromBits {n : ℕ} (A : Finset (Fin n ⊕ Fin n)) : Word n :=
  fun i => ⟨(if Sum.inl i ∈ A then 1 else 0) +
    2 * (if Sum.inr i ∈ A then 0 else 1), by split_ifs <;> omega⟩

private theorem fromBits_bits {n : ℕ} (d : Word n) : fromBits (bits d) = d := by
  funext i
  apply Fin.ext
  change (if Sum.inl i ∈ bits d then 1 else 0) +
    2 * (if Sum.inr i ∈ bits d then 0 else 1) = (d i).val
  simp only [bits, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hd := (d i).isLt
  split_ifs <;> omega

private theorem bits_fromBits {n : ℕ} (A : Finset (Fin n ⊕ Fin n)) :
    bits (fromBits A) = A := by
  ext x
  rcases x with i | i
  · by_cases hl : Sum.inl i ∈ A <;> by_cases hr : Sum.inr i ∈ A <;>
      simp [bits, fromBits, hl, hr]
  · by_cases hl : Sum.inl i ∈ A <;> by_cases hr : Sum.inr i ∈ A <;>
      simp [bits, fromBits, hl, hr]

private def wordBitsEquiv (n : ℕ) : Word n ≃ Finset (Fin n ⊕ Fin n) where
  toFun := bits
  invFun := fromBits
  left_inv := fromBits_bits
  right_inv := bits_fromBits

private theorem bits_weight {n : ℕ} (d : Word n) :
    ((bits d).card : ℤ) = (n : ℤ) + balance d := by
  have hp (i : Fin n) :
      (if (d i).val % 2 = 1 then (1 : ℤ) else 0) +
      (if (d i).val / 2 = 0 then (1 : ℤ) else 0) = 1 + charge (d i) := by
    have hd := (d i).isLt
    dsimp [charge]
    split_ifs <;> omega
  unfold bits
  rw [Finset.card_disjSum, Nat.cast_add, card_filter_int, card_filter_int,
    ← Finset.sum_add_distrib]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp [balance]

private theorem words_balance_card (n r : ℕ) :
    (Finset.univ.filter (fun d : Word n =>
      balance d = (r : ℤ) - (n : ℤ))).card = Nat.choose (2 * n) r := by
  classical
  let labels : (Fin n ⊕ Fin n) ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (Nat.two_mul n).symm)
  let e : Word n ≃ Finset (Fin (2 * n)) :=
    (wordBitsEquiv n).trans (Equiv.finsetCongr labels)
  calc
    _ = ((Finset.univ : Finset (Fin (2 * n))).powersetCard r).card := by
      apply Finset.card_equiv e
      intro d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_powersetCard, Finset.subset_univ]
      change balance d = (r : ℤ) - (n : ℤ) ↔ (e d).card = r
      have hcard : (e d).card = (bits d).card := by
        change ((bits d).map labels.toEmbedding).card = (bits d).card
        exact Finset.card_map _
      rw [hcard]
      have hw := bits_weight d
      constructor
      · intro hb
        have hc : ((bits d).card : ℤ) = (r : ℤ) := by omega
        exact_mod_cast hc
      · intro hc
        rw [hc] at hw
        omega
    _ = Nat.choose (2 * n) r := by
      rw [Finset.card_powersetCard]
      simp

private def topWord (n : ℕ) : Word n := fun _ => ⟨3, by decide⟩

private theorem value_topWord (n : ℕ) : value (topWord n) = 4 ^ n - 1 := by
  rw [value_formula]
  simp only [topWord, Fin.val_mk]
  rw [← Finset.mul_sum]
  change 3 * digitSum n = 4 ^ n - 1
  rw [RadixFourNonunitZeroSubsets.pow_four n]
  exact digitSum_three n

private theorem value_eq_top {n : ℕ} (d : Word n) :
    value d = 4 ^ n - 1 ↔ d = topWord n := by
  constructor
  · intro h
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    change value d = value (topWord n)
    rw [value_topWord]
    exact h
  · rintro rfl
    exact value_topWord n

private theorem seedWord_ne_top {n : ℕ} (t : Fin (4 ^ n - 1)) :
    wordForSeed t ≠ topWord n := by
  intro he
  have hv := (value_eq_top (wordForSeed t)).mpr he
  rw [value_wordForSeed] at hv
  exact (ne_of_lt t.isLt) hv

/-- The full binomial spectrum of the literal integer trace at the actual
physical even labels, over all distinct residue seeds including zero and
nonunits. Only the central fibre loses the all-three word. Every natural r
is allowed, including both endpoints and all r beyond 2*n. -/
theorem even_trace_seed_spectrum {n : ℕ} (hn : 0 < n) (r : ℕ) :
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) =>
      3 * evenTrace n t.val = modulus (2 * n) * ((r : ℤ) - (n : ℤ)))).card +
      (if r = n then 1 else 0) = Nat.choose (2 * n) r := by
  classical
  let W : Finset (Word n) := Finset.univ.filter
    (fun d => balance d = (r : ℤ) - (n : ℤ))
  have htop : topWord n ∈ W ↔ r = n := by
    have hz : balance (topWord n) = 0 := by simp [balance, charge, topWord]
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, hz]
    omega
  have hb : (Finset.univ.filter (fun t : Fin (4 ^ n - 1) =>
      3 * evenTrace n t.val = modulus (2 * n) * ((r : ℤ) - (n : ℤ)))).card =
        (W.erase (topWord n)).card := by
    apply Finset.card_bij (fun t _ => wordForSeed t)
    · intro t ht
      have htrace := (Finset.mem_filter.mp ht).2
      have hbal := (seed_trace_iff hn t r).mp htrace
      simp [Finset.mem_erase, seedWord_ne_top t, W, hbal]
    · intro t _ s _ he
      apply Fin.ext
      have hv := congrArg value he
      simpa only [value_wordForSeed] using hv
    · intro d hd
      have hne : d ≠ topWord n := (Finset.mem_erase.mp hd).1
      have hbal : balance d = (r : ℤ) - (n : ℤ) :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hd).2).2
      have hlt : value d < 4 ^ n - 1 := by
        have hv := (finFunctionFinEquiv d).isLt
        have hnot : value d ≠ 4 ^ n - 1 := mt (value_eq_top d).mp hne
        change value d < 4 ^ n at hv
        omega
      let t : Fin (4 ^ n - 1) := ⟨value d, hlt⟩
      have he : wordForSeed t = d := by
        apply finFunctionFinEquiv.injective
        apply Fin.ext
        exact value_wordForSeed t
      refine ⟨t, ?_, he⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (seed_trace_iff hn t r).mpr
      rw [he]
      exact hbal
  rw [hb]
  by_cases hr : r = n
  · rw [if_pos hr, Finset.card_erase_add_one (htop.mpr hr)]
    exact words_balance_card n r
  · rw [if_neg hr, Finset.erase_eq_of_notMem (fun h => hr (htop.mp h)),
      Nat.add_zero]
    exact words_balance_card n r

/-- Distinct residue seeds with actual even-label trace zero. This is NOT the
cardinality of physical zero subsets of a single source. The extra one is the
balanced all-three word, which represents the same residue zero as all-zero. -/
theorem zero_even_trace_seed_count {n : ℕ} (hn : 0 < n) :
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) => evenTrace n t.val = 0)).card + 1 =
      Nat.choose (2 * n) n := by
  classical
  have hz (t : Fin (4 ^ n - 1)) :
      3 * evenTrace n t.val = modulus (2 * n) * ((n : ℤ) - (n : ℤ)) ↔
        evenTrace n t.val = 0 := by
    simp only [sub_self, mul_zero]
    omega
  simpa [hz] using even_trace_seed_spectrum hn n

end D5.S3.Combinatorics.Circle.RadixFourDigitBalance
