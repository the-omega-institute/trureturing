/- GID: D5/S3/Combinatorics/Sequenceability/OriginalSignedCyclicQuotientSharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalSignedCyclicQuotientSharpness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Even-padded odd residues give quadratic cyclic original-support carriers. -/

import D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped Classical BigOperators

namespace D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness

open OriginalFiniteOrderSharpness (Index Coordinate q p a b triple coordinate_sum)
open OriginalCyclicOrderSharpness (chosenA chosenB epsilon)

def modulus (s : ℕ) : ℕ := 2 * s + 1
def quotientModulus (s k : ℕ) : ℕ := 4 * modulus s - 6 + 2 * k
abbrev PairIndex (s : ℕ) := Index (modulus s)
abbrev QuotientGroup (s k : ℕ) := ZMod (quotientModulus s k)
abbrev WitnessGroup (s k : ℕ) := ZMod (modulus s) × QuotientGroup s k

def point (s k : ℕ) (i : PairIndex s) : QuotientGroup s k := (2 * i.val + 1 : ℕ)

def label (s k : ℕ) : Coordinate (modulus s) → WitnessGroup s k
  | Sum.inl none => (1, 0)
  | Sum.inl (some i) => (s, point s k i)
  | Sum.inr none => (-1, 2)
  | Sum.inr (some i) => (s, -point s k i)

private lemma quotient_pos (s k : ℕ) (hs : 1 ≤ s) : 2 < quotientModulus s k := by
  unfold quotientModulus modulus
  omega

private lemma point_bounds (s k : ℕ) (hs : 1 ≤ s) (i : PairIndex s) :
    0 < 2 * i.val + 1 ∧ 2 * (2 * i.val + 1) ≤ quotientModulus s k := by
  have hi := i.isLt
  dsimp [Index, modulus] at hi
  unfold quotientModulus modulus
  omega

private lemma point_injective (s k : ℕ) (hs : 1 ≤ s) : Function.Injective (point s k) := by
  intro i j he
  have hi := point_bounds s k hs i
  have hj := point_bounds s k hs j
  have hv := congrArg ZMod.val he
  have hi' : 2 * i.val + 1 < quotientModulus s k := by omega
  have hj' : 2 * j.val + 1 < quotientModulus s k := by omega
  change ((2 * i.val + 1 : ℕ) : ZMod (quotientModulus s k)).val =
    ((2 * j.val + 1 : ℕ) : ZMod (quotientModulus s k)).val at hv
  rw [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] at hv
  apply Fin.ext
  omega

/-- Different indices occupy different negation orbits, including the unique
possibly self-negative final point. -/
private lemma point_eq_neg_imp_eq (s k : ℕ) (hs : 1 ≤ s) (i j : PairIndex s)
    (he : point s k i = -point s k j) : i = j := by
  have hi := point_bounds s k hs i
  have hj := point_bounds s k hs j
  have hi' : 2 * i.val + 1 < quotientModulus s k := by omega
  have hj' : 2 * j.val + 1 < quotientModulus s k := by omega
  have he' : ((2 * i.val + 1 : ℕ) : ZMod (quotientModulus s k)) =
      ((quotientModulus s k - (2 * j.val + 1) : ℕ) : ZMod (quotientModulus s k)) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    exact he
  have hv := congrArg ZMod.val he'
  rw [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt (by omega)] at hv
  have hiv := i.isLt
  have hjv := j.isLt
  dsimp [Index, modulus] at hiv hjv
  unfold quotientModulus modulus at hv
  apply Fin.ext
  omega

private def parity (s k : ℕ) (hs : 1 ≤ s) : QuotientGroup s k →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ quotientModulus s k from
    ⟨4 * s + k - 1, by unfold quotientModulus modulus; omega⟩) (ZMod 2)

private lemma parity_point (s k : ℕ) (hs : 1 ≤ s) (i : PairIndex s) :
    parity s k hs (point s k i) = 1 := by
  unfold point
  rw [map_natCast]
  push_cast
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo]
  simp

private lemma chosen_bounds (s : ℕ) (C : Finset (Coordinate (modulus s))) :
    (chosenA (modulus s) C).card ≤ 2 * s ∧
      (chosenB (modulus s) C).card ≤ 2 * s := by
  constructor
  · simpa [Index, modulus] using Finset.card_le_univ (chosenA (modulus s) C)
  · simpa [Index, modulus] using Finset.card_le_univ (chosenB (modulus s) C)

private lemma quotient_sum (s k : ℕ) (C : Finset (Coordinate (modulus s))) :
    (∑ x ∈ C, label s k x).2 =
      (if p (modulus s) ∈ C then (2 : QuotientGroup s k) else 0) +
      (∑ i ∈ chosenA (modulus s) C, point s k i) -
      ∑ i ∈ chosenB (modulus s) C, point s k i := by
  rw [Prod.snd_sum, coordinate_sum]
  change ((if q (modulus s) ∈ C then 0 else 0) +
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then point s k i else 0)) +
    ((if p (modulus s) ∈ C then (2 : QuotientGroup s k) else 0) +
      ∑ i : PairIndex s, if b (modulus s) i ∈ C then -point s k i else 0) = _
  have ha : (∑ i : PairIndex s, if a (modulus s) i ∈ C then point s k i else 0) =
      ∑ i ∈ chosenA (modulus s) C, point s k i := by
    simp [chosenA, Finset.sum_filter]
  have hb : (∑ i : PairIndex s, if b (modulus s) i ∈ C then -point s k i else 0) =
      -(∑ i ∈ chosenB (modulus s) C, point s k i) := by
    rw [chosenB, Finset.sum_filter, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  simp only [ite_self, zero_add, ha, hb]
  abel

private lemma torsion_sum (s k : ℕ) (C : Finset (Coordinate (modulus s))) :
    (∑ x ∈ C, label s k x).1 = (epsilon (modulus s) C : ZMod (modulus s)) -
      (if p (modulus s) ∈ C then 1 else 0) +
      (s : ZMod (modulus s)) *
        (((chosenA (modulus s) C).card + (chosenB (modulus s) C).card : ℕ) :
          ZMod (modulus s)) := by
  have ha : (∑ i : PairIndex s, if a (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) =
      ((chosenA (modulus s) C).card : ZMod (modulus s)) * s := by
    calc
      _ = ∑ i ∈ chosenA (modulus s) C, (s : ZMod (modulus s)) := by
        rw [chosenA, Finset.sum_filter]
      _ = _ := by simp [nsmul_eq_mul]
  have hb : (∑ i : PairIndex s, if b (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) =
      ((chosenB (modulus s) C).card : ZMod (modulus s)) * s := by
    calc
      _ = ∑ i ∈ chosenB (modulus s) C, (s : ZMod (modulus s)) := by
        rw [chosenB, Finset.sum_filter]
      _ = _ := by simp [nsmul_eq_mul]
  rw [Prod.fst_sum, coordinate_sum]
  change ((if q (modulus s) ∈ C then (1 : ZMod (modulus s)) else 0) +
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0)) +
    ((if p (modulus s) ∈ C then -1 else 0) +
      ∑ i : PairIndex s, if b (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) = _
  rw [ha, hb]
  by_cases hq : q (modulus s) ∈ C <;>
    by_cases hp : p (modulus s) ∈ C <;>
    simp [epsilon, hq, hp] <;> ring

private lemma paired_count_even (s k : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s))) (hz : (∑ x ∈ C, label s k x) = 0) :
    Even ((chosenA (modulus s) C).card + (chosenB (modulus s) C).card) := by
  have hq : parity s k hs (∑ x ∈ C, label s k x).2 = 0 := by
    simpa using congrArg (fun z : WitnessGroup s k => parity s k hs z.2) hz
  rw [quotient_sum, map_sub, map_add, map_sum, map_sum] at hq
  simp only [parity_point, Finset.sum_const, nsmul_eq_mul, mul_one] at hq
  have hpar : (((chosenA (modulus s) C).card +
      (chosenB (modulus s) C).card : ℕ) : ZMod 2) = 0 := by
    have hp2 : parity s k hs (2 : QuotientGroup s k) = 0 := by
      rw [map_ofNat]
      decide
    by_cases hp : p (modulus s) ∈ C <;>
      simpa [hp, hp2, Nat.cast_add, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using hq
  exact ZMod.natCast_eq_zero_iff_even.mp hpar

private lemma no_pairs (s : ℕ) (C : Finset (Coordinate (modulus s)))
    (hc : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 0) :
    chosenA (modulus s) C = ∅ ∧ chosenB (modulus s) C = ∅ := by
  constructor <;> apply Finset.card_eq_zero.mp <;> omega

private lemma all_pairs (s : ℕ) (C : Finset (Coordinate (modulus s)))
    (hc : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 4 * s) :
    chosenA (modulus s) C = Finset.univ ∧ chosenB (modulus s) C = Finset.univ := by
  have hb := chosen_bounds s C
  constructor <;> apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  · have he : (chosenA (modulus s) C).card = 2 * s := by omega
    rw [he, Finset.card_univ]
    simp [Index, modulus]
  · have he : (chosenB (modulus s) C).card = 2 * s := by omega
    rw [he, Finset.card_univ]
    simp [Index, modulus]

private lemma two_selected (s k : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s)))
    (hq : q (modulus s) ∈ C) (hp : p (modulus s) ∉ C)
    (hc : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 2)
    (hz : (∑ i ∈ chosenA (modulus s) C, point s k i) -
        (∑ i ∈ chosenB (modulus s) C, point s k i) = 0) :
    ∃ i : PairIndex s, C = triple (modulus s) i := by
  rcases (show ((chosenA (modulus s) C).card = 0 ∧ (chosenB (modulus s) C).card = 2) ∨
      ((chosenA (modulus s) C).card = 1 ∧ (chosenB (modulus s) C).card = 1) ∨
      ((chosenA (modulus s) C).card = 2 ∧ (chosenB (modulus s) C).card = 0) by omega)
    with hh | hh | hh
  · have ha := Finset.card_eq_zero.mp hh.1
    obtain ⟨i, j, hij, hb⟩ := Finset.card_eq_two.mp hh.2
    have he : point s k i + point s k j = 0 := by
      have hn : -(point s k i + point s k j) = 0 := by simpa [ha, hb, hij] using hz
      exact neg_eq_zero.mp hn
    exact (hij (point_eq_neg_imp_eq s k hs i j (eq_neg_of_add_eq_zero_left he))).elim
  · obtain ⟨i, ha⟩ := Finset.card_eq_one.mp hh.1
    obtain ⟨j, hb⟩ := Finset.card_eq_one.mp hh.2
    have he : point s k i = point s k j := by
      apply sub_eq_zero.mp
      simpa [ha, hb] using hz
    have hij := point_injective s k hs he
    subst j
    refine ⟨i, ?_⟩
    ext x
    rcases x with (_ | j) | (_ | j)
    · change q (modulus s) ∈ C ↔ q (modulus s) ∈ triple (modulus s) i
      simp [hq, triple]
    · have hm : a (modulus s) j ∈ C ↔ j = i := by
        have h : j ∈ chosenA (modulus s) C ↔ j = i := by rw [ha]; simp
        simpa [chosenA] using h
      simpa [triple, q, a, b] using hm
    · change p (modulus s) ∈ C ↔ p (modulus s) ∈ triple (modulus s) i
      simp only [hp, false_iff]
      simp [triple, q, p, a, b]
    · have hm : b (modulus s) j ∈ C ↔ j = i := by
        have h : j ∈ chosenB (modulus s) C ↔ j = i := by rw [hb]; simp
        simpa [chosenB] using h
      simpa [triple, q, a, b] using hm
  · obtain ⟨i, j, hij, ha⟩ := Finset.card_eq_two.mp hh.1
    have hb := Finset.card_eq_zero.mp hh.2
    have he : point s k i + point s k j = 0 := by simpa [ha, hb, hij] using hz
    exact (hij (point_eq_neg_imp_eq s k hs i j (eq_neg_of_add_eq_zero_left he))).elim

private lemma triple_zero (s k : ℕ) (i : PairIndex s) :
    (triple (modulus s) i).Nonempty ∧ (∑ x ∈ triple (modulus s) i, label s k x) = 0 := by
  refine ⟨⟨q (modulus s), by simp [triple]⟩, ?_⟩
  apply Prod.ext
  · change (∑ x ∈ triple (modulus s) i, label s k x).1 = 0
    simp [Prod.fst_sum, triple, q, a, b, label, add_assoc]
    have h := ZMod.natCast_self (modulus s)
    unfold modulus at h
    push_cast at h
    change (2 * (s : ZMod (modulus s)) + 1 = 0) at h
    linear_combination h
  · simp [Prod.snd_sum, triple, q, a, b, label, add_assoc]

private lemma zero_support_iff (s k : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s))) :
    (C.Nonempty ∧ (∑ x ∈ C, label s k x) = 0) ↔
      ∃ i : PairIndex s, C = triple (modulus s) i := by
  constructor
  · rintro ⟨hC, hz⟩
    have hb := chosen_bounds s C
    obtain ⟨r, hr⟩ := paired_count_even s k hs C hz
    have hcount : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 2 * r := by
      omega
    have hrlt : r < modulus s := by unfold modulus; omega
    have heps : epsilon (modulus s) C ≤ 1 := by unfold epsilon; split_ifs <;> omega
    have hepslt : epsilon (modulus s) C < modulus s := by
      change epsilon (modulus s) C < 2 * s + 1
      omega
    have ht := congrArg (fun z : WitnessGroup s k => z.1) hz
    change (∑ x ∈ C, label s k x).1 = 0 at ht
    rw [torsion_sum, hcount] at ht
    have hscale : (s : ZMod (modulus s)) * ((2 * r : ℕ) : ZMod (modulus s)) = -r := by
      have h := ZMod.natCast_self (modulus s)
      unfold modulus at h
      push_cast at h ⊢
      change (2 * (s : ZMod (modulus s)) + 1 = 0) at h
      linear_combination (r : ZMod (modulus s)) * h
    rw [hscale] at ht
    have hqsum := congrArg (fun z : WitnessGroup s k => z.2) hz
    change (∑ x ∈ C, label s k x).2 = 0 at hqsum
    rw [quotient_sum] at hqsum
    have htwo : (2 : QuotientGroup s k) ≠ 0 := by
      have hlt := quotient_pos s k hs
      intro he
      have hd := (ZMod.natCast_eq_zero_iff 2 (quotientModulus s k)).mp
        (show ((2 : ℕ) : QuotientGroup s k) = 0 by simpa using he)
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    by_cases hp : p (modulus s) ∈ C
    · have hc : (epsilon (modulus s) C : ZMod (modulus s)) = ((r + 1 : ℕ) : ZMod (modulus s)) := by
        simp only [hp, if_pos] at ht
        push_cast
        linear_combination ht
      by_cases hsmall : r + 1 < modulus s
      · have he := congrArg ZMod.val hc
        rw [ZMod.val_natCast_of_lt hepslt, ZMod.val_natCast_of_lt hsmall] at he
        have hzero : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 0 := by omega
        have hempty := no_pairs s C hzero
        apply (htwo ?_).elim
        simpa [hp, hempty.1, hempty.2] using hqsum
      · have hrm : r + 1 = modulus s := by omega
        have hfull : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 4 * s := by
          unfold modulus at hrm
          omega
        have hall := all_pairs s C hfull
        apply (htwo ?_).elim
        simpa [hp, hall.1, hall.2] using hqsum
    · have hc : (epsilon (modulus s) C : ZMod (modulus s)) = (r : ZMod (modulus s)) := by
        apply sub_eq_zero.mp
        simpa [hp, sub_eq_add_neg] using ht
      have he := congrArg ZMod.val hc
      rw [ZMod.val_natCast_of_lt hepslt, ZMod.val_natCast_of_lt hrlt] at he
      have hq : q (modulus s) ∈ C := by
        by_contra hq
        have he0 : epsilon (modulus s) C = 0 := by simp [epsilon, hq]
        have hzero : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 0 := by omega
        have hempty := no_pairs s C hzero
        have ha (i : PairIndex s) : a (modulus s) i ∉ C := by
          intro hi
          have hm : i ∈ chosenA (modulus s) C := by simp [chosenA, hi]
          simpa [hempty.1] using hm
        have hb (i : PairIndex s) : b (modulus s) i ∉ C := by
          intro hi
          have hm : i ∈ chosenB (modulus s) C := by simp [chosenB, hi]
          simpa [hempty.2] using hm
        obtain ⟨x, hx⟩ := hC
        rcases x with (_ | i) | (_ | i)
        · exact hq hx
        · exact ha i hx
        · exact hp hx
        · exact hb i hx
      have hc2 : (chosenA (modulus s) C).card + (chosenB (modulus s) C).card = 2 := by
        have he1 : epsilon (modulus s) C = 1 := by simp [epsilon, hq]
        omega
      apply two_selected s k hs C hq hp hc2
      simpa [hp] using hqsum
  · rintro ⟨i, rfl⟩
    exact triple_zero s k i

private lemma cyclic_carrier (s k : ℕ)
    (hc : (modulus s).Coprime (quotientModulus s k)) :
    IsAddCyclic (WitnessGroup s k) := by
  let e := (ZMod.chineseRemainder hc).toAddEquiv
  exact isAddCyclic_of_surjective e e.surjective

/-- An explicit quadratic carrier for every odd original order at least three.
Even padding preserves the support family; coprime factors supply cyclicity. -/
theorem sharpness (k s : ℕ) (hs : 1 ≤ s) :
    Finite (WitnessGroup s k) ∧
    Nat.card (WitnessGroup s k) = modulus s * (4 * modulus s - 6 + 2 * k) ∧
    addOrderOf (label s k (q (modulus s))) = modulus s ∧
    ((modulus s).Coprime (quotientModulus s k) → IsAddCyclic (WitnessGroup s k)) ∧
    (∀ C : Finset (Coordinate (modulus s)),
      (C.Nonempty ∧ (∑ x ∈ C, label s k x) = 0) ↔
        ∃ i : PairIndex s, C = triple (modulus s) i) := by
  letI : NeZero (modulus s) := ⟨by unfold modulus; omega⟩
  letI : NeZero (quotientModulus s k) := ⟨by have h := quotient_pos s k hs; omega⟩
  refine ⟨inferInstance, ?_, ?_, cyclic_carrier s k, zero_support_iff s k hs⟩
  · simp [WitnessGroup, QuotientGroup, Nat.card_prod, Nat.card_zmod, quotientModulus]
  · simp [label, q, Prod.addOrderOf_mk]

end D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
