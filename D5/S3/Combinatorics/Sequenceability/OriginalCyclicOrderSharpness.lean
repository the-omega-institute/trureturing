/- GID: D5/S3/Combinatorics/Sequenceability/OriginalCyclicOrderSharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalCyclicOrderSharpness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Cyclic labels attain the original all-support component bound at every finite order. -/

import D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
For m ≥ 2, let L = 2^m. In ZMod(m*L), label q by L, p by 2^(m-1),
a_j by 2^j, and b_j by -2^j-L. Reduction modulo L and uniqueness of binary
subset sums classify every nonempty zero support as one original triple.
Equality of the full minimal-support families transports the existing graph
lower bound, and the canonical component theorem gives the matching upper bound.
The construction and proof route are caller supplied. This proof adapts the
three-module cyclic source candidate from 2026-10-27, retaining its full statement
and making consumed arithmetic helpers private in one owner module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Classical BigOperators
namespace D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness

open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)

def block (m : ℕ) : ℕ := 2 ^ m
def modulus (m : ℕ) : ℕ := m * block m
abbrev WitnessGroup (m : ℕ) := ZMod (modulus m)

def label (m : ℕ) : Coordinate m → WitnessGroup m
  | Sum.inl none => (block m : ℕ)
  | Sum.inl (some j) => (2 ^ j.val : ℕ)
  | Sum.inr none => (2 ^ (m - 1) : ℕ)
  | Sum.inr (some j) => -((2 ^ j.val : ℕ) : WitnessGroup m) - (block m : ℕ)

private lemma block_pos (m : ℕ) : 0 < block m := by
  exact pow_pos (by decide : 0 < (2 : ℕ)) m

private lemma block_eq_twice (m : ℕ) (hm : 2 ≤ m) : block m = 2 * 2 ^ (m - 1) := by
  have he : m = (m - 1) + 1 := by omega
  unfold block
  conv_lhs => rw [he]
  rw [pow_succ, Nat.mul_comm]

private lemma digit_lt (m : ℕ) (j : Index m) : 2 ^ j.val < 2 ^ (m - 1) := by
  exact pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) j.isLt

private lemma modulus_pos (m : ℕ) (hm : 2 ≤ m) : 0 < modulus m := by
  exact Nat.mul_pos (by omega) (block_pos m)

def reduction (m : ℕ) : WitnessGroup m →+* ZMod (block m) :=
  ZMod.castHom (show block m ∣ modulus m from
    ⟨m, by simp [modulus, Nat.mul_comm]⟩) (ZMod (block m))

/-- Canonical natural representatives after reduction modulo L. -/
def residue (m : ℕ) : Coordinate m → ℕ
  | Sum.inl none => 0
  | Sum.inl (some j) => 2 ^ j.val
  | Sum.inr none => 2 ^ (m - 1)
  | Sum.inr (some j) => block m - 2 ^ j.val

private lemma residue_lt (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) :
    residue m x < block m := by
  have hL := block_eq_twice m hm
  have hP : 0 < 2 ^ (m - 1) := by positivity
  rcases x with (_ | j) | (_ | j)
  · exact block_pos m
  · have hd := digit_lt m j
    change 2 ^ j.val < block m
    omega
  · change 2 ^ (m - 1) < block m
    omega
  · have hd : 0 < 2 ^ j.val := by positivity
    change block m - 2 ^ j.val < block m
    omega

private lemma residue_pos (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) (hx : x ≠ q m) :
    0 < residue m x := by
  rcases x with (_ | j) | (_ | j)
  · exact (hx rfl).elim
  · change 0 < 2 ^ j.val
    positivity
  · change 0 < 2 ^ (m - 1)
    positivity
  · have hd := digit_lt m j
    have hL := block_eq_twice m hm
    change 0 < block m - 2 ^ j.val
    omega

private lemma reduction_label (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) :
    reduction m (label m x) = (residue m x : ZMod (block m)) := by
  rcases x with (_ | j) | (_ | j)
  · simp [label, residue, map_natCast]
  · simp only [label, residue, map_natCast]
  · simp only [label, residue, map_natCast]
  · have hd : 2 ^ j.val ≤ block m := by
      have := digit_lt m j
      have := block_eq_twice m hm
      omega
    simp only [label, residue, map_sub, map_neg, map_natCast]
    rw [Nat.cast_sub hd]
    simp

private lemma residue_injective (m : ℕ) (hm : 2 ≤ m) : Function.Injective (residue m) := by
  have hL := block_eq_twice m hm
  have hP : 0 < 2 ^ (m - 1) := by positivity
  have hd (j : Index m) : 0 < 2 ^ j.val ∧ 2 ^ j.val < 2 ^ (m - 1) :=
    ⟨by positivity, digit_lt m j⟩
  have hpow : Function.Injective (fun j : Index m => 2 ^ j.val) := by
    intro i j he
    exact Fin.ext ((pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))).injective he)
  intro x y he
  rcases x with (_ | i) | (_ | i) <;> rcases y with (_ | j) | (_ | j)
  · rfl
  · have := hd j
    simp only [residue] at he
    omega
  · simp only [residue] at he
    omega
  · have := hd j
    simp only [residue] at he
    omega
  · have := hd i
    simp only [residue] at he
    omega
  · have hij : i = j := hpow he
    subst j
    rfl
  · have := hd i
    simp only [residue] at he
    omega
  · have := hd i
    have := hd j
    simp only [residue] at he
    omega
  · simp only [residue] at he
    omega
  · have := hd j
    simp only [residue] at he
    omega
  · rfl
  · have := hd j
    simp only [residue] at he
    omega
  · have := hd i
    simp only [residue] at he
    omega
  · have := hd i
    have := hd j
    simp only [residue] at he
    omega
  · have := hd i
    simp only [residue] at he
    omega
  · have hi := hd i
    have hj := hd j
    have he' : 2 ^ i.val = 2 ^ j.val := by
      simp only [residue] at he
      omega
    have hij := hpow he'
    subst j
    rfl

private lemma label_injective (m : ℕ) (hm : 2 ≤ m) : Function.Injective (label m) := by
  intro x y he
  apply residue_injective m hm
  have hr := congrArg (reduction m) he
  rw [reduction_label m hm x, reduction_label m hm y] at hr
  have hv := congrArg ZMod.val hr
  simpa only [ZMod.val_natCast_of_lt (residue_lt m hm x),
    ZMod.val_natCast_of_lt (residue_lt m hm y)] using hv

private lemma label_order (m : ℕ) (hm : 2 ≤ m) : addOrderOf (label m (q m)) = m := by
  have hL := block_pos m
  have hdiv : block m ∣ modulus m := ⟨m, by simp [modulus, Nat.mul_comm]⟩
  have hg : Nat.gcd (modulus m) (block m) = block m := by
    exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdiv (dvd_refl _))
  change addOrderOf ((block m : ℕ) : ZMod (modulus m)) = m
  rw [ZMod.addOrderOf_coe _ (ne_of_gt (modulus_pos m hm)), hg]
  exact Nat.mul_div_cancel m hL

private lemma label_nonzero (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) : label m x ≠ 0 := by
  intro hz
  by_cases hx : x = q m
  · subst x
    have he := label_order m hm
    rw [hz, addOrderOf_zero] at he
    omega
  · have hr := congrArg (reduction m) hz
    rw [reduction_label m hm x, map_zero] at hr
    have hv := congrArg ZMod.val hr
    rw [ZMod.val_natCast_of_lt (residue_lt m hm x), ZMod.val_zero] at hv
    have := residue_pos m hm x hx
    omega

end D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness


namespace D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness

open scoped BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)

def chosenA (m : ℕ) (C : Finset (Coordinate m)) : Finset (Index m) :=
  Finset.univ.filter (fun j => a m j ∈ C)

def chosenB (m : ℕ) (C : Finset (Coordinate m)) : Finset (Index m) :=
  Finset.univ.filter (fun j => b m j ∈ C)

def aDigits (m : ℕ) (C : Finset (Coordinate m)) : Finset ℕ :=
  (chosenA m C).image Fin.val

def bDigits (m : ℕ) (C : Finset (Coordinate m)) : Finset ℕ :=
  (chosenB m C).image Fin.val

def leftDigits (m : ℕ) (C : Finset (Coordinate m)) : Finset ℕ :=
  if p m ∈ C then insert (m - 1) (aDigits m C) else aDigits m C

def epsilon (m : ℕ) (C : Finset (Coordinate m)) : ℕ := if q m ∈ C then 1 else 0

private lemma mem_aDigits (m : ℕ) (C : Finset (Coordinate m)) (j : Index m) :
    j.val ∈ aDigits m C ↔ a m j ∈ C := by
  constructor
  · intro hj
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
    have hij : i = j := Fin.ext he
    subst i
    exact (Finset.mem_filter.mp hi).2
  · intro hj
    exact Finset.mem_image.mpr ⟨j, by simp [chosenA, hj], rfl⟩

private lemma mem_bDigits (m : ℕ) (C : Finset (Coordinate m)) (j : Index m) :
    j.val ∈ bDigits m C ↔ b m j ∈ C := by
  constructor
  · intro hj
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
    have hij : i = j := Fin.ext he
    subst i
    exact (Finset.mem_filter.mp hi).2
  · intro hj
    exact Finset.mem_image.mpr ⟨j, by simp [chosenB, hj], rfl⟩

private lemma aDigits_lt (m : ℕ) (C : Finset (Coordinate m))
    (i : ℕ) (hi : i ∈ aDigits m C) : i < m - 1 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact j.isLt

private lemma bDigits_lt (m : ℕ) (C : Finset (Coordinate m))
    (i : ℕ) (hi : i ∈ bDigits m C) : i < m - 1 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact j.isLt

private lemma a_digit_sum (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ i ∈ aDigits m C, 2 ^ i) =
      ∑ j : Index m, if a m j ∈ C then 2 ^ j.val else 0 := by
  rw [aDigits, Finset.sum_image]
  · simp [chosenA, Finset.sum_filter]
  · intro i _ j _ he
    exact Fin.ext he

private lemma b_digit_sum (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ i ∈ bDigits m C, 2 ^ i) =
      ∑ j : Index m, if b m j ∈ C then 2 ^ j.val else 0 := by
  rw [bDigits, Finset.sum_image]
  · simp [chosenB, Finset.sum_filter]
  · intro i _ j _ he
    exact Fin.ext he

private lemma left_digit_sum (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ i ∈ leftDigits m C, 2 ^ i) =
      (if p m ∈ C then 2 ^ (m - 1) else 0) +
        ∑ j : Index m, if a m j ∈ C then 2 ^ j.val else 0 := by
  have hn : m - 1 ∉ aDigits m C := by
    intro h
    have := aDigits_lt m C (m - 1) h
    omega
  by_cases hp : p m ∈ C <;> simp [leftDigits, hp, hn, a_digit_sum]

private lemma left_code_lt (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m)) :
    (∑ i ∈ leftDigits m C, 2 ^ i) < block m := by
  apply Nat.geomSum_lt (by decide)
  intro i hi
  by_cases hp : p m ∈ C
  · have hi' : i = m - 1 ∨ i ∈ aDigits m C := by simpa [leftDigits, hp] using hi
    rcases hi' with rfl | hi
    · omega
    · have := aDigits_lt m C i hi
      omega
  · have hi' : i ∈ aDigits m C := by simpa [leftDigits, hp] using hi
    have := aDigits_lt m C i hi'
    omega

private lemma right_code_lt (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ i ∈ bDigits m C, 2 ^ i) < 2 ^ (m - 1) :=
  Nat.geomSum_lt (by decide) (bDigits_lt m C)

private lemma sum_label (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ x ∈ C, label m x) =
      ((∑ i ∈ leftDigits m C, 2 ^ i : ℕ) : WitnessGroup m) +
        (epsilon m C : WitnessGroup m) * (block m : ℕ) -
      ((∑ i ∈ bDigits m C, 2 ^ i : ℕ) : WitnessGroup m) -
        ((chosenB m C).card : WitnessGroup m) * (block m : ℕ) := by
  classical
  have hleft : ((∑ i ∈ leftDigits m C, 2 ^ i : ℕ) : WitnessGroup m) =
      (if p m ∈ C then ((2 ^ (m - 1) : ℕ) : WitnessGroup m) else 0) +
        ∑ j : Index m, if a m j ∈ C then ((2 ^ j.val : ℕ) : WitnessGroup m) else 0 := by
    simpa only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using
      congrArg (fun z : ℕ => (z : WitnessGroup m)) (left_digit_sum m C)
  have hright : ((∑ i ∈ bDigits m C, 2 ^ i : ℕ) : WitnessGroup m) =
      ∑ j : Index m, if b m j ∈ C then ((2 ^ j.val : ℕ) : WitnessGroup m) else 0 := by
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using
      congrArg (fun z : ℕ => (z : WitnessGroup m)) (b_digit_sum m C)
  have hconstant : (∑ j : Index m,
      if b m j ∈ C then ((block m : ℕ) : WitnessGroup m) else 0) =
        ((chosenB m C).card : WitnessGroup m) * (block m : ℕ) := by
    calc
      _ = ∑ _j ∈ chosenB m C, ((block m : ℕ) : WitnessGroup m) := by
        simp only [chosenB, Finset.sum_filter]
      _ = _ := by simp [nsmul_eq_mul]
  have hneg : (∑ j : Index m,
      if b m j ∈ C then
        (-((2 ^ j.val : ℕ) : WitnessGroup m) - (block m : ℕ)) else 0) =
      -((∑ i ∈ bDigits m C, 2 ^ i : ℕ) : WitnessGroup m) -
        ((chosenB m C).card : WitnessGroup m) * (block m : ℕ) := by
    calc
      _ = ∑ j : Index m,
          (-(if b m j ∈ C then ((2 ^ j.val : ℕ) : WitnessGroup m) else 0) -
            (if b m j ∈ C then ((block m : ℕ) : WitnessGroup m) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← hright, hconstant]
  have heps : (if q m ∈ C then ((block m : ℕ) : WitnessGroup m) else 0) =
      (epsilon m C : WitnessGroup m) * (block m : ℕ) := by
    by_cases hq : q m ∈ C <;> simp [epsilon, hq]
  -- Expand the original sum over the original Sum/Option IDs directly.
  rw [← Finset.sum_ite_mem_eq C (label m), Fintype.sum_sum_type]
  simp only [Fintype.sum_option]
  change
    ((if q m ∈ C then ((block m : ℕ) : WitnessGroup m) else 0) +
      (∑ j : Index m, if a m j ∈ C then ((2 ^ j.val : ℕ) : WitnessGroup m) else 0)) +
    ((if p m ∈ C then ((2 ^ (m - 1) : ℕ) : WitnessGroup m) else 0) +
      (∑ j : Index m, if b m j ∈ C then
        (-((2 ^ j.val : ℕ) : WitnessGroup m) - (block m : ℕ)) else 0)) = _
  rw [hneg, heps, hleft]
  ring

/-- The missing binary inference, consumed by the full zero-support classifier.
It derives absence of p, matched a/b bits, and the exact number of b bits from
the actual cyclic zero equation; none of these are endpoint premises. -/
private lemma zero_coordinates (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m))
    (hz : (∑ x ∈ C, label m x) = 0) :
    p m ∉ C ∧ (∀ j : Index m, a m j ∈ C ↔ b m j ∈ C) ∧
      (chosenB m C).card = epsilon m C := by
  classical
  let A : ℕ := ∑ i ∈ leftDigits m C, 2 ^ i
  let B : ℕ := ∑ i ∈ bDigits m C, 2 ^ i
  let k : ℕ := (chosenB m C).card
  have hA : A < block m := left_code_lt m hm C
  have hBsmall : B < 2 ^ (m - 1) := right_code_lt m C
  have hB : B < block m := by
    have := block_eq_twice m hm
    omega
  have heps : epsilon m C < m := by
    unfold epsilon
    split_ifs <;> omega
  have hk : k < m := by
    have hb := Finset.card_le_univ (chosenB m C)
    simp only [Fintype.card_fin] at hb
    dsimp [k]
    omega
  have hcast : ((A + epsilon m C * block m : ℕ) : WitnessGroup m) =
      ((B + k * block m : ℕ) : WitnessGroup m) := by
    have he := (sum_label m C).symm.trans hz
    change (A : WitnessGroup m) + (epsilon m C : WitnessGroup m) * (block m : ℕ) -
      (B : WitnessGroup m) - (k : WitnessGroup m) * (block m : ℕ) = 0 at he
    push_cast
    linear_combination he
  have hsmall : (A : ZMod (block m)) = (B : ZMod (block m)) := by
    have he := congrArg (reduction m) hcast
    simpa only [map_add, map_mul, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      mul_zero, add_zero] using he
  have hAB : A = B := by
    have he := congrArg ZMod.val hsmall
    simpa only [ZMod.val_natCast_of_lt hA, ZMod.val_natCast_of_lt hB] using he
  have hsets : leftDigits m C = bDigits m C :=
    Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ)) hAB
  have hp : p m ∉ C := by
    intro hp
    have hn : m - 1 ∈ leftDigits m C := by simp [leftDigits, hp]
    rw [hsets] at hn
    have := bDigits_lt m C (m - 1) hn
    omega
  have hbalance (j : Index m) : a m j ∈ C ↔ b m j ∈ C := by
    have he : aDigits m C = bDigits m C := by simpa [leftDigits, hp] using hsets
    rw [← mem_aDigits m C j, ← mem_bDigits m C j, he]
  have hlarge : ((epsilon m C * block m : ℕ) : WitnessGroup m) =
      ((k * block m : ℕ) : WitnessGroup m) := by
    have he : (B : WitnessGroup m) + ((epsilon m C * block m : ℕ) : WitnessGroup m) =
        (B : WitnessGroup m) + ((k * block m : ℕ) : WitnessGroup m) := by
      simpa only [Nat.cast_add, hAB] using hcast
    exact add_left_cancel he
  have hepsL : epsilon m C * block m < modulus m :=
    Nat.mul_lt_mul_of_pos_right heps (block_pos m)
  have hkL : k * block m < modulus m :=
    Nat.mul_lt_mul_of_pos_right hk (block_pos m)
  have hnat : epsilon m C * block m = k * block m := by
    have he := congrArg ZMod.val hlarge
    simpa only [ZMod.val_natCast_of_lt hepsL, ZMod.val_natCast_of_lt hkL] using he
  have hcount : k = epsilon m C :=
    (mul_right_cancel₀ (ne_of_gt (block_pos m)) hnat).symm
  exact ⟨hp, hbalance, hcount⟩

/-- Every nonempty zero support is exactly one original triple. -/
private lemma zero_support_iff (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m)) :
    (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
      ∃ j : Index m, C = triple m j := by
  classical
  constructor
  · rintro ⟨hC, hz⟩
    obtain ⟨hp, hbalance, hcount⟩ := zero_coordinates m hm C hz
    have hq : q m ∈ C := by
      by_contra hq
      have hJ : chosenB m C = ∅ :=
        Finset.card_eq_zero.mp (by simpa [epsilon, hq] using hcount)
      have hnob (j : Index m) : b m j ∉ C := by
        intro hj
        have hjJ : j ∈ chosenB m C := by simp [chosenB, hj]
        rw [hJ] at hjJ
        exact Finset.notMem_empty j hjJ
      obtain ⟨x, hx⟩ := hC
      rcases x with (_ | j) | (_ | j)
      · exact hq hx
      · exact hnob j ((hbalance j).mp hx)
      · exact hp hx
      · exact hnob j hx
    have hcard : (chosenB m C).card = 1 := by simpa [epsilon, hq] using hcount
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hmem (i : Index m) : b m i ∈ C ↔ i = j := by
      have he : i ∈ chosenB m C ↔ i = j := by simp only [hj, Finset.mem_singleton]
      simpa [chosenB] using he
    refine ⟨j, ?_⟩
    ext x
    rcases x with (_ | i) | (_ | i)
    · change q m ∈ C ↔ q m ∈ triple m j
      simp [triple, hq]
    · simpa [triple, q, a, b] using (hbalance i).trans (hmem i)
    · change p m ∈ C ↔ p m ∈ triple m j
      have hnot : p m ∉ triple m j := by simp [triple, q, p, a, b]
      simp only [hp, hnot]
    · simpa [triple, q, a, b] using hmem i
  · rintro ⟨j, rfl⟩
    refine ⟨⟨q m, by simp [triple]⟩, ?_⟩
    simp [triple, q, a, b, label]
    ring

end D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness


namespace D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness

open scoped BigOperators
open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)
open DisjointMinimalZeroOrdering (MinimalZeroSupport)
open BooleanRowChargeConnectivity (supportIntersectionGraph)
open OriginalFiniteOrderComponentBound (q_containing_component_card_lt)

/-- The actual family of ALL proper original minimal cyclic zero supports. -/
def supports (m : ℕ) : Finset (Finset (Coordinate m)) := by
  classical
  exact (full m).powerset.filter
    (fun B => B ⊂ full m ∧ MinimalZeroSupport (label m) B)

/-- Minimality is transported through the proved full zero-support equivalence.
The product classification comes from its public theorem, not a private helper
copied into a new owner. This is a consumed transport lemma. -/
private lemma minimal_support_equiv (m : ℕ) (hm : 2 ≤ m) (B : Finset (Coordinate m)) :
    MinimalZeroSupport (label m) B ↔
      MinimalZeroSupport (OriginalFiniteOrderSharpness.label m) B := by
  have hproduct := (OriginalFiniteOrderSharpness.sharpness m hm).2.2.2.2.2.1
  have he (C : Finset (Coordinate m)) :
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        (C.Nonempty ∧ (∑ x ∈ C, OriginalFiniteOrderSharpness.label m x) = 0) :=
    (zero_support_iff m hm C).trans (hproduct C).symm
  constructor
  · rintro ⟨hn, hz, hmin⟩
    have hB := (he B).mp ⟨hn, hz⟩
    refine ⟨hB.1, hB.2, ?_⟩
    intro C hsub hCn hCz
    exact hmin C hsub hCn ((he C).mpr ⟨hCn, hCz⟩).2
  · rintro ⟨hn, hz, hmin⟩
    have hB := (he B).mpr ⟨hn, hz⟩
    refine ⟨hB.1, hB.2, ?_⟩
    intro C hsub hCn hCz
    exact hmin C hsub hCn ((he C).mp ⟨hCn, hCz⟩).2

private lemma supports_eq_product (m : ℕ) (hm : 2 ≤ m) :
    supports m = OriginalFiniteOrderSharpness.supports m := by
  classical
  ext B
  simp only [supports, OriginalFiniteOrderSharpness.supports, Finset.mem_filter,
    minimal_support_equiv m hm B]

set_option maxHeartbeats 800000 in
/-- For EVERY m ≥ 2 the explicit FINITE CYCLIC label group ZMod(m*2^m)
attains the original canonical component bound. The entire original coordinate
set is retained, all labels are nonzero and injective, q has exact order m,
and EVERY nonempty coefficient-one zero support is precisely an original
triple. The component count uses ALL proper original minimal zero supports. -/
theorem sharpness (m : ℕ) (hm : 2 ≤ m) :
    Finite (WitnessGroup m) ∧
    IsAddCyclic (WitnessGroup m) ∧
    Function.Injective (label m) ∧
    (∀ x : Coordinate m, label m x ≠ 0) ∧
    q m ∈ full m ∧
    addOrderOf (label m (q m)) = m ∧
    (∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        ∃ j : Index m, C = triple m j) ∧
    (∀ B : Finset (Coordinate m),
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B) ∧
    (supports m).card = m - 1 ∧
    (∀ B ∈ supports m, q m ∈ B) ∧
    (∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m))) ∧
    (((Finset.univ : Finset (supports m)).filter (fun B : supports m => q m ∈ B.val)).image
      (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card = m - 1 := by
  classical
  letI : NeZero (modulus m) := ⟨ne_of_gt (modulus_pos m hm)⟩
  have hfinite : Finite (WitnessGroup m) := by infer_instance
  have hcyclic : IsAddCyclic (WitnessGroup m) := by infer_instance
  obtain ⟨_, _, _, _, _, _, hmemP, hcardP, hqP, hdisP, hgraphP⟩ :=
    OriginalFiniteOrderSharpness.sharpness m hm
  have hE := supports_eq_product m hm
  have hmem (B : Finset (Coordinate m)) :
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B := by
    rw [hE, hmemP B, minimal_support_equiv m hm B]
  have hcard : (supports m).card = m - 1 := by rw [hE]; exact hcardP
  have hq : ∀ B ∈ supports m, q m ∈ B := by simpa only [hE] using hqP
  have hdis : ∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m)) := by
    simpa only [hE] using hdisP
  -- Equality of actual ALL-support families transports the existing graph
  -- lower bound; no chosen-triple proxy or duplicate connectivity proof.
  have hlower : m - 1 ≤
      (((Finset.univ : Finset (supports m)).filter (fun B : supports m => q m ∈ B.val)).image
        (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card := by
    rw [hE]
    exact Nat.le_of_eq hgraphP.symm
  have hmzero : m • label m (q m) = 0 := by
    simpa only [label_order m hm] using addOrderOf_nsmul_eq_zero (label m (q m))
  -- Genuine direct application to THIS cyclic label group and ALL-support
  -- family. The existing upper-bound proof is neither restated nor duplicated.
  have hcanonical :=
    q_containing_component_card_lt (α := Coordinate m) (G := WitnessGroup m)
      (label m) (full m) (supports m) hmem (q m) m hm hmzero
  have hupper :
      (((Finset.univ : Finset (supports m)).filter (fun B : supports m => q m ∈ B.val)).image
        (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card < m := by
    refine lt_of_eq_of_lt ?_ hcanonical
    congr 1
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount := Nat.le_antisymm (Nat.le_sub_one_of_lt hupper) hlower
  refine ⟨hfinite, hcyclic, label_injective m hm, label_nonzero m hm,
    Finset.mem_univ _, label_order m hm, zero_support_iff m hm, hmem,
    hcard, hq, hdis, ?_⟩
  refine Eq.trans ?_ hcount
  congr 1

end D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness
