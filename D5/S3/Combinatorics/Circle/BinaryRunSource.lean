/- GID: D5/S3/Combinatorics/Circle/BinaryRunSource
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/BinaryRunSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Physical cyclic binary coding preserves labelled positions and forces a separated-run lower bound. -/

import D5.S3.Combinatorics.Circle.SourceWidth
import D5.S3.Combinatorics.Circle.ExpandingSourcePath
import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import D5.S1.Words.AssociatedMersenne.CircularWords
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-! # Physical cyclic binary runs for the centered doubling source

This file keeps the carrier `Fin k` physical.  Numerical collisions and
proper numerical periods are allowed.  The universal run estimate is the
new content; the carry telescope is consumed from `ZeroSumSubsets`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.BinaryRunSource

open scoped BigOperators
open D5.S3.Combinatorics.Circle.SourceWidth
open D5.S3.Combinatorics.Circle.ExpandingSourcePath
open D5.S3.Combinatorics.Circle.ZeroSumSubsets
open D5.S1.Words.AssociatedMersenne.CircularWords

def falseTrueEdge {k : ℕ} (c : Fin k → Bool) (i : Fin k) : Prop :=
  c i = false ∧ c (finRotate k i) = true

noncomputable def physicalRunCount {k : ℕ} (c : Fin k → Bool) : ℕ :=
  by classical exact (Finset.univ.filter (falseTrueEdge c)).card

def binaryRunTops (e : ℕ) : Finset ℕ :=
  e.bitIndices.toFinset.filter (fun j => e.testBit (j + 1) = false)

def binaryRunCount (e : ℕ) : ℕ :=
  (binaryRunTops e).card

def forwardDigit {k : ℕ} (c : Fin k → Bool) (a i : Fin k) : Bool :=
  c (finCycle a i)

def lsbDigit {k : ℕ} (c : Fin k → Bool) (a i : Fin k) : Bool :=
  forwardDigit c a i.rev

def wordValue {k : ℕ} (c : Fin k → Bool) (a : Fin k) : ℕ :=
  ∑ i : Fin k, (lsbDigit c a i).toNat * 2 ^ i.val

private def finiteBinaryRunTops (k x : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => x.testBit i.val = true ∧
    x.testBit (i.val + 1) = false)

private theorem binaryRunTops_card_eq (k x : ℕ) (hx : x < 2 ^ (k - 1)) :
    (finiteBinaryRunTops k x).card = binaryRunCount x := by
  classical
  have htop (j : ℕ) (hj : j ∈ binaryRunTops x) : j < k := by
    by_contra h
    have hkj : k ≤ j := Nat.le_of_not_gt h
    have hpow : 2 ^ (k - 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hbit := Nat.two_pow_le_of_mem_bitIndices
      (List.mem_toFinset.mp (Finset.mem_filter.mp hj).1)
    exact (Nat.not_lt_of_ge (hpow.trans hbit)) hx
  have himage : (finiteBinaryRunTops k x).image Fin.val = binaryRunTops x := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have hi' := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      exact ⟨List.mem_toFinset.mpr (Nat.mem_bitIndices.mpr hi'.2.1), hi'.2.2⟩
    · intro hj
      have hj' := htop j hj
      apply Finset.mem_image.mpr
      refine ⟨⟨j, hj'⟩, ?_, rfl⟩
      simp only [finiteBinaryRunTops, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Nat.mem_bitIndices.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hj).1),
        Finset.mem_filter.mp hj |>.2⟩
  change (finiteBinaryRunTops k x).card = (binaryRunTops x).card
  rw [← himage]
  simpa only [Finset.card_image_of_injOn] using
    (Finset.card_image_of_injOn (s := finiteBinaryRunTops k x)
      (by intro i hi j hj hij; exact Fin.ext hij)).symm

private theorem physicalRunCount_forward (k : ℕ) (c : Fin k → Bool) (a : Fin k) :
    physicalRunCount c =
      (Finset.univ.filter (fun i : Fin k =>
        forwardDigit c a i = false ∧
          forwardDigit c a (finRotate k i) = true)).card := by
  classical
  letI : NeZero k := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)⟩
  change (Finset.univ.filter (falseTrueEdge c)).card = _
  apply Finset.card_bijective (finCycle a).symm (finCycle a).symm.bijective
  intro i
  have hcycle : finCycle a ((finCycle a).symm i) = i :=
    (finCycle a).apply_symm_apply i
  have hcomm : finCycle a (finRotate k ((finCycle a).symm i)) =
      finRotate k i := by
    have hcancel : (finCycle a).symm i + a = i := by
      simpa [finCycle_apply] using hcycle
    apply Fin.ext
    simpa [finCycle_apply, finRotate_apply, add_assoc] using
      congrArg Fin.val (congrArg (fun z : Fin k => z + 1) hcancel)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change falseTrueEdge c i ↔
    (c (finCycle a ((finCycle a).symm i)) = false ∧
      c (finCycle a (finRotate k ((finCycle a).symm i))) = true)
  rw [hcycle, hcomm]
  simp [falseTrueEdge]

private theorem physicalRunCount_binaryRunCount {k : ℕ} (hk : 2 ≤ k)
    (c : Fin k → Bool) (a : Fin k) (x : ℕ)
    (hx : x < 2 ^ (k - 1))
    (hbits : ∀ i, forwardDigit c a i = x.testBit i.rev.val) :
    physicalRunCount c = binaryRunCount x := by
  letI : NeZero k := ⟨by omega⟩
  let phi : Equiv.Perm (Fin k) := (finRotate k).trans Fin.revPerm
  have htopfalse : x.testBit (k - 1) = false := by
    exact Nat.testBit_lt_two_pow hx
  have hcard :
      (Finset.univ.filter (fun i : Fin k =>
        forwardDigit c a i = false ∧
          forwardDigit c a (finRotate k i) = true)).card =
      (finiteBinaryRunTops k x).card := by
    apply Finset.card_bijective phi phi.bijective
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      finiteBinaryRunTops]
    have hnext : (phi i).val = (finRotate k i).rev.val := rfl
    let lastK : Fin k := ⟨k - 1, by omega⟩
    by_cases hi : i = lastK
    · rw [hi]
      rw [hbits lastK, hbits (finRotate k lastK)]
      have hlast : finRotate k lastK = 0 := by
        apply Fin.ext
        simp [finRotate_apply, Fin.add_def]
        have h : k - 1 + 1 = k := by omega
        rw [h]
        simp
      rw [hlast]
      have hlastrev : lastK.rev = 0 := by
        apply Fin.ext
        simp [Fin.rev, lastK]
        have h : k - 1 + 1 = k := by omega
        rw [h]
        simp
      have hzerorev : (0 : Fin k).rev = lastK := by
        apply Fin.ext
        simp [Fin.rev, lastK]
      have hplus : (lastK + 1).val = 0 := by
        have hv := congrArg Fin.val hlast
        rw [finRotate_apply] at hv
        exact hv
      simp [phi, lastK, hlastrev, hzerorev, hplus, htopfalse]
    · have hnotlast : i.val + 1 < k := by
        have hne : i.val ≠ k - 1 := by
          intro h
          apply hi
          apply Fin.ext
          omega
        omega
      have hirho : (finRotate k i).val = i.val + 1 := by
        rw [finRotate_apply, Fin.val_add]
        norm_num
        exact Nat.mod_eq_of_lt hnotlast
      have hphi : (phi i).val + 1 = i.rev.val := by
        change (finRotate k i).rev.val + 1 = i.rev.val
        rw [Fin.val_rev, hirho, Fin.val_rev]
        omega
      rw [hbits i, hbits (finRotate k i)]
      rw [hnext]
      have hphi' : (finRotate k i).rev.val + 1 = i.rev.val := by
        simpa [phi] using hphi
      rw [hphi']
      constructor <;> intro h
      · exact ⟨h.2, h.1⟩
      · exact ⟨h.2, h.1⟩
  rw [physicalRunCount_forward, hcard, binaryRunTops_card_eq k x hx]

private theorem bits_of_wordValue {k : ℕ} (c : Fin k → Bool) (a : Fin k)
    (x : ℕ) (hvalue : wordValue c a = x) :
    ∀ i, lsbDigit c a i = x.testBit i.val := by
  classical
  let support : Finset (Fin k) :=
    Finset.univ.filter (fun i => lsbDigit c a i = true)
  have hsum : ∑ i ∈ support, 2 ^ i.val = x := by
    calc
      ∑ i ∈ support, 2 ^ i.val =
          ∑ i : Fin k, if lsbDigit c a i = true then 2 ^ i.val else 0 := by
            simp [support, Finset.sum_filter]
      _ = ∑ i : Fin k, (lsbDigit c a i).toNat * 2 ^ i.val := by
        apply Finset.sum_congr rfl
        intro i hi
        cases hb : lsbDigit c a i <;> simp [hb]
      _ = wordValue c a := rfl
      _ = x := hvalue
  have himage : support.image Fin.val = x.bitIndices.toFinset := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
    change (∑ j ∈ support.image Fin.val, 2 ^ j) =
      ∑ j ∈ x.bitIndices.toFinset, 2 ^ j
    rw [Finset.sum_image]
    · simpa only [Finset.sum_toFinset_bitIndices_two_pow] using hsum
    · intro i hi j hj hij
      exact Fin.ext hij
  intro i
  have hmem : i ∈ support ↔ i.val ∈ x.bitIndices.toFinset := by
    constructor
    · intro hi
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · intro hi
      rw [← himage] at hi
      obtain ⟨j, hj, hv⟩ := Finset.mem_image.mp hi
      have heq : j = i := Fin.ext hv
      simpa [heq] using hj
  have htest : x.testBit i.val = true ↔ i.val ∈ x.bitIndices.toFinset := by
    simp
  by_cases hb : lsbDigit c a i = true
  · rw [hb]
    have hi : i ∈ support := by simp [support, hb]
    exact (htest.mpr (hmem.mp hi)).symm
  · have hb' : lsbDigit c a i = false := Bool.eq_false_of_not_eq_true hb
    have : x.testBit i.val ≠ true := by
      intro hxbit
      apply hb
      have hi : i.val ∈ x.bitIndices.toFinset := htest.mp hxbit
      simpa [support] using hmem.mpr hi
    cases hbit : x.testBit i.val with
    | false => simp [hb', hbit]
    | true => exact False.elim (this hbit)

private theorem forward_bits_of_wordValue {k : ℕ} (c : Fin k → Bool) (a : Fin k)
    (x : ℕ) (hvalue : wordValue c a = x) :
    ∀ i, forwardDigit c a i = x.testBit i.rev.val := by
  intro i
  simpa [lsbDigit, Fin.rev_rev] using bits_of_wordValue c a x hvalue i.rev

private theorem binaryRunTops_shift (e : ℕ) :
    binaryRunTops (4 * e + 1) =
      {0} ∪ (binaryRunTops e).image (fun j => j + 2) := by
  classical
  ext j
  constructor
  · intro hj
    have hjbit : (4 * e + 1).testBit j = true :=
      Nat.mem_bitIndices.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hj).1)
    have hjzero : (4 * e + 1).testBit (j + 1) = false :=
      Finset.mem_filter.mp hj |>.2
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hj1 : 1 ≤ j := by omega
      have hnot1 : j ≠ 1 := by
        intro hj1'
        subst j
        rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
          Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) 1] at hjbit
        have hz : (1 : ℕ).testBit 1 = false := by decide
        exact Bool.noConfusion (hz.symm.trans hjbit)
      have hj2 : 2 ≤ j := by omega
      have hq : (4 * e + 1).testBit j = e.testBit (j - 2) := by
        rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
          Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) j]
        split
        · omega
        · simp [show ¬ j < 2 by omega]
      have hq1 : (4 * e + 1).testBit (j + 1) = e.testBit (j - 1) := by
        rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
          Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) (j + 1)]
        split
        · omega
        · simp [show ¬ j + 1 < 2 by omega]
      have htop : j - 2 ∈ binaryRunTops e := by
        apply Finset.mem_filter.mpr
        constructor
        · apply List.mem_toFinset.mpr
          exact Nat.mem_bitIndices.mpr (by simpa [hq] using hjbit)
        · have heq : j - 2 + 1 = j - 1 := by omega
          simpa [hq1, heq] using hjzero
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨j - 2, htop, by omega⟩
  · intro hj
    rcases Finset.mem_union.mp hj with hj0 | hj
    · have hj0' : j = 0 := by simpa using hj0
      subst j
      apply Finset.mem_filter.mpr
      constructor
      · apply List.mem_toFinset.mpr
        have hbit : (4 * e + 1).testBit 0 = true := by
          rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
            Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) 0]
          simp
        exact Nat.mem_bitIndices.mpr hbit
      · rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
          Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) 1]
        norm_num
        decide
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      have hqbit : e.testBit q = true :=
        Nat.mem_bitIndices.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hq).1)
      have hqzero : e.testBit (q + 1) = false := Finset.mem_filter.mp hq |>.2
      apply Finset.mem_filter.mpr
      constructor
      · apply List.mem_toFinset.mpr
        have hbit : (4 * e + 1).testBit (q + 2) = true := by
          rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
            Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) (q + 2)]
          have hnot : ¬ q + 2 < 2 := by omega
          simp [hnot, hqbit]
        exact Nat.mem_bitIndices.mpr hbit
      · rw [show 4 * e + 1 = 2 ^ 2 * e + 1 by ring,
          Nat.testBit_two_pow_mul_add e (b := 1) (i := 2) (by decide) (q + 3)]
        have hnot : ¬ q + 3 < 2 := by omega
        simp [hnot, hqzero]

private theorem binaryRunCount_shift (e : ℕ) :
    binaryRunCount (4 * e + 1) = binaryRunCount e + 1 := by
  classical
  have hd : Disjoint ({0} : Finset ℕ)
      ((binaryRunTops e).image (fun j => j + 2)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    have hx0 : x = 0 := by simpa using hx
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hy
    omega
  rw [binaryRunCount, binaryRunTops_shift, Finset.card_union_of_disjoint hd,
    Finset.card_singleton, Finset.card_image_iff.mpr]
  · change 1 + (binaryRunTops e).card = (binaryRunTops e).card + 1
    omega
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij

private theorem cycle_rev_succ {k : ℕ} (hk : 0 < k) (a i : Fin k) :
    finCycle a ((finRotate k).symm i).rev =
      finRotate k (finCycle a i.rev) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  by_cases hk1 : k = 1
  · subst k
    exact Subsingleton.elim _ _
  have hk2 : 2 ≤ k := by omega
  apply Fin.ext
  simp only [finCycle_apply, finRotate_apply, finRotate_symm_apply, Fin.val_add,
    Fin.val_rev, Fin.val_sub]
  norm_num
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hi : i = 0
  · subst i
    have hkm1 : k - 1 < k := by omega
    simp [h1, Nat.mod_eq_of_lt hkm1]
    have hl : k - (k - 1 + 1) + a.val = a.val := by omega
    have hr : k - 1 + a.val + 1 = k + a.val := by omega
    rw [hl, hr]
    rw [Nat.add_mod]
    simp [h1]
  · have hi0 : i.val ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    have hsub : i.val - 1 + 1 = i.val :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)
    have hkm1 : k - 1 + i.val = k + (i.val - 1) := by omega
    have him1 : i.val - 1 < k := by omega
    have hmod : (k - 1 % k + i.val) % k + 1 = i.val := by
      rw [h1, hkm1, Nat.add_mod]
      simp [Nat.mod_eq_of_lt him1, hsub]
    rw [hmod]
    have heq : k - i.val + a.val = k - (i.val + 1) + a.val + 1 := by omega
    rw [heq]

theorem recurrence_wordValue {k : ℕ} (hk : 0 < k)
    (u : Fin k → ℕ) (c : Fin k → Bool) (a : Fin k)
    (hrec : ∀ i, (u (finRotate k i) : ℤ) =
      2 * (u i : ℤ) - ((2 ^ k - 1 : ℕ) : ℤ) * (c i).toNat) :
    wordValue c a = u a := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let m : Fin k → ℕ := fun i => u (finCycle a i.rev)
  let n : Fin k → ℕ := fun i => (2 ^ k - 1) * (c (finCycle a i.rev)).toNat
  have hcarry : ∀ i, (n i : ℤ) =
      2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ) := by
    intro i
    have hr := hrec (finCycle a i.rev)
    dsimp [m, n]
    rw [← cycle_rev_succ hk a i] at hr
    linarith
  have hw := carry_weight hk n m (∅ : Finset (Fin k)) (by
    intro i
    simpa using hcarry i)
  have hN : 0 < 2 ^ k - 1 := by
    have : 1 < 2 ^ k := Nat.one_lt_two_pow (ne_of_gt hk)
    omega
  have hlast : m ⟨k - 1, by omega⟩ = u a := by
    have hrev : (⟨k - 1, by omega⟩ : Fin k).rev = ⟨0, hk⟩ := by
      apply Fin.ext
      simp [Fin.rev]
      omega
    have hzero : (⟨0, hk⟩ : Fin k) + a = a := by simp
    simp [m, hrev, finCycle_apply, hzero]
  have hsum : (2 ^ k - 1) * wordValue c a = (2 ^ k - 1) * u a := by
    have hw' := hw
    simp only [ZeroSumSubsets.mask, Finset.sum_empty, Nat.zero_add] at hw'
    have hw'' : (2 ^ k - 1) * wordValue c a =
        (2 ^ k - 1) * m ⟨k - 1, by omega⟩ := by
      calc
        (2 ^ k - 1) * wordValue c a =
            ∑ i : Fin k, (2 ^ k - 1) *
              ((c (finCycle a i.rev)).toNat * 2 ^ i.val) := by
          change (2 ^ k - 1) *
            (∑ i : Fin k, (c (finCycle a i.rev)).toNat * 2 ^ i.val) = _
          rw [Finset.mul_sum]
        _ = ∑ i : Fin k, n i * 2 ^ i.val := by
          simp [n, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = (2 ^ k - 1) * m ⟨k - 1, by omega⟩ := hw'
    simpa [hlast] using hw''
  exact Nat.eq_of_mul_eq_mul_left hN hsum


theorem binaryRunTops_separated {e : ℕ} {a b : ℕ}
    (ha : a ∈ binaryRunTops e) (hb : b ∈ binaryRunTops e) (hab : a < b) :
    a + 1 < b := by
  by_contra h
  have hba : b = a + 1 := by omega
  have hbitA : e.testBit a = true := Nat.mem_bitIndices.mp (by
    exact List.mem_toFinset.mp (Finset.mem_filter.mp ha).1)
  have hzeroA : e.testBit (a + 1) = false := (Finset.mem_filter.mp ha).2
  have hbitB : e.testBit b = true := Nat.mem_bitIndices.mp (by
    exact List.mem_toFinset.mp (Finset.mem_filter.mp hb).1)
  rw [hba] at hbitB
  exact Bool.noConfusion (hzeroA.symm.trans hbitB)

theorem separated_run_bound (e : ℕ) :
    4 ^ binaryRunCount e ≤ 3 * e + 1 := by
  classical
  let s := binaryRunTops e
  let m := s.card
  by_cases hm : m = 0
  · change 4 ^ m ≤ 3 * e + 1
    rw [hm]
    norm_num
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let emb : Fin m ↪o ℕ := s.orderEmbOfFin (by rfl)
    let b : Fin m → ℕ := emb
    have hbmem (i : Fin m) : b i ∈ s := by
      exact s.orderEmbOfFin_mem _ _
    have hstep (i : Fin m) (hi1 : i.val + 1 < m) :
        b i + 2 ≤ b ⟨i.val + 1, hi1⟩ := by
      have hi := hbmem i
      have hj := hbmem ⟨i.val + 1, hi1⟩
      have hlt := emb.strictMono (show
        i < (⟨i.val + 1, hi1⟩ : Fin m) by
          exact Fin.mk_lt_mk.mpr (by omega))
      have hsep := binaryRunTops_separated hi hj (by exact hlt)
      omega
    have hlower (i : Fin m) : 2 * i.val ≤ b i := by
      induction i using Fin.strong_induction_on with
      | h i ih =>
          by_cases hi0 : i.val = 0
          · simp [hi0]
          · let p : Fin m := ⟨i.val - 1, by omega⟩
            have hpi : p < i := by
              exact Fin.mk_lt_mk.mpr (by simp [p]; omega)
            have hp : 2 * p.val ≤ b p := ih p hpi
            have hsp : b p + 2 ≤ b i := by
              have hpm : p.val + 1 < m := by simp [p]; omega
              have hs := hstep p hpm
              have heq : (⟨p.val + 1, by omega⟩ : Fin m) = i := by
                apply Fin.ext
                exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by simpa using hi0))
              calc
                b p + 2 ≤ b ⟨p.val + 1, by omega⟩ := by
                  simpa [p] using hs
                _ = b i := by rw [heq]
            have hp' : 2 * (i.val - 1) ≤ b p := by simpa [p] using hp
            omega
    have hsum : ∑ i : Fin m, 2 ^ b i ≤ e := by
      have hsub : Finset.image b Finset.univ ⊆ e.bitIndices.toFinset := by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        have hi := hbmem i
        exact (Finset.mem_filter.mp hi).1
      have hle : ∑ x ∈ Finset.image b Finset.univ, 2 ^ x ≤
          ∑ x ∈ e.bitIndices.toFinset, 2 ^ x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro x hx _
          exact Nat.zero_le _)
      rw [Finset.sum_image] at hle
      · simpa only [Finset.sum_toFinset_bitIndices_two_pow] using hle
      · intro i hi j hj hij
        exact emb.injective hij
    have hgeom : 4 ^ m ≤ 3 * (∑ i : Fin m, 2 ^ b i) + 1 := by
      have hterm (i : Fin m) : 4 ^ i.val ≤ 2 ^ b i := by
        calc
          4 ^ i.val = (2 ^ 2) ^ i.val := by norm_num
          _ = 2 ^ (2 * i.val) := by rw [pow_mul]
        exact Nat.pow_le_pow_right (by decide) (hlower i)
      have hgeom' : 4 ^ m = 3 * (∑ i : Fin m, 4 ^ i.val) + 1 := by
        have hg := geom_sum_mul_add (3 : ℕ) m
        simpa only [Fin.sum_univ_eq_sum_range, Nat.add_comm, Nat.mul_comm] using hg.symm
      calc
        4 ^ m = 3 * (∑ i : Fin m, 4 ^ i.val) + 1 := hgeom'
        _ ≤ 3 * (∑ i : Fin m, 2 ^ b i) + 1 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 3
              (Finset.sum_le_sum (fun i _ => hterm i))) 1
    have hfinal : 4 ^ m ≤ 3 * e + 1 :=
      hgeom.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hsum) 1)
    simpa [binaryRunCount, s, m] using hfinal


theorem cyclic_binary_run_bound {k : ℕ} (hk : 2 ≤ k)
    (u : Fin k → ℕ) (c : Fin k → Bool)
    (hu : ∀ i, u i < 2 ^ k - 1)
    (hrec : ∀ i, (u (finRotate k i) : ℤ) =
      2 * (u i : ℤ) - ((2 ^ k - 1 : ℕ) : ℤ) * (c i).toNat)
    (a : Fin k) (e : ℕ) (ha : u a = 4 * e + 1)
    (hhalf : u a < 2 ^ (k - 1)) :
    physicalRunCount c = binaryRunCount e + 1 ∧
      4 ^ (physicalRunCount c - 1) ≤ 3 * e + 1 := by
  have hvalue : wordValue c a = 4 * e + 1 := by
    rw [recurrence_wordValue (by omega) u c a hrec, ha]
  have hbits := forward_bits_of_wordValue c a (4 * e + 1) hvalue
  have hhalf' : 4 * e + 1 < 2 ^ (k - 1) := by simpa [ha] using hhalf
  have hrx := physicalRunCount_binaryRunCount hk c a (4 * e + 1) hhalf' hbits
  have hrun : physicalRunCount c = binaryRunCount e + 1 := by
    rw [hrx, binaryRunCount_shift]
  refine ⟨hrun, ?_⟩
  rw [hrun, Nat.add_sub_cancel]
  exact separated_run_bound e

def nativeUnsigned (k t : ℕ) (i : Fin k) : ℕ :=
  ((-actualSource k t i) +
    if -actualSource k t i < 0 then modulus k else 0).toNat

def nativeCarry (k t : ℕ) (i : Fin k) : Bool :=
  decide (0 < actualSource k t i)

theorem actualSource_binary_run_bound {k t : ℕ} (hk : 3 ≤ k)
    (a : Fin k) (e : ℕ)
    (ha : actualSource k t a = -(4 * e + 1))
    (hstrict : 3 * e + 1 < quarter k) :
    physicalRunCount (nativeCarry k t) = binaryRunCount e + 1 ∧
      4 ^ (physicalRunCount (nativeCarry k t) - 1) ≤ 3 * e + 1 := by
  obtain ⟨hQ, hN, hhalf, hNpos, hodd⟩ := source_geometry hk
  let g : Fin k → ℤ := fun i => -actualSource k t i
  let U : Fin k → ℤ := fun i => g i + if g i < 0 then modulus k else 0
  have hg (i : Fin k) : -(modulus k / 2) ≤ g i ∧ g i ≤ modulus k / 2 := by
    have hf := centered_bounds hNpos hodd ((2 : ℤ) ^ i.val * (t : ℤ))
    change -(modulus k / 2) ≤ actualSource k t i ∧
      actualSource k t i ≤ modulus k / 2 at hf
    dsimp [g]
    omega
  have hU (i : Fin k) : 0 ≤ U i ∧ U i < modulus k := by
    have hgi := hg i
    dsimp [U]
    split_ifs <;> omega
  have hto (i : Fin k) : (nativeUnsigned k t i : ℤ) = U i := by
    rw [nativeUnsigned, Int.toNat_of_nonneg (hU i).1]
  have hstep (i : Fin k) :
      actualSource k t (finRotate k i) = doubleStep (modulus k) (actualSource k t i) := by
    have he : phase (by omega) i 1 = finRotate k i := by
      apply Fin.ext
      simp only [phase, finRotate_apply, Fin.val_add]
      norm_num
    have hs := phase_step hk t i 0
    rw [show 0 + 1 = 1 by omega, he] at hs
    have hzero : phase (by omega) i 0 = i := phase_zero (by omega) i
    rw [hzero] at hs
    exact hs
  have hUstep (i : Fin k) : U (finRotate k i) - U i = g i := by
    have hgstep : g (finRotate k i) = doubleStep (modulus k) (g i) := by
      dsimp [g]
      rw [hstep, doubleStep_neg (le_of_lt hNpos)]
    have hu := unsigned_step hNpos hodd (by
      have := hg i
      exact this)
    dsimp [U]
    rw [hgstep]
    exact hu
  have hrec : ∀ i, (nativeUnsigned k t (finRotate k i) : ℤ) =
      2 * (nativeUnsigned k t i : ℤ) -
        ((2 ^ k - 1 : ℕ) : ℤ) * (nativeCarry k t i).toNat := by
    intro i
    have hd := hUstep i
    have hNmod : modulus k = ((2 ^ k - 1 : ℕ) : ℤ) := by
      dsimp [modulus]
      norm_num
    rw [hto (finRotate k i), hto i]
    rw [← hNmod]
    have hc : (nativeCarry k t i).toNat = if g i < 0 then 1 else 0 := by
      by_cases hp : 0 < actualSource k t i
      · simp [nativeCarry, g, hp]
      · simp [nativeCarry, g, hp]
    rw [hc]
    dsimp [U] at hd ⊢
    split_ifs at hd ⊢ <;> omega
  have haU : nativeUnsigned k t a = 4 * e + 1 := by
    have hga : g a = 4 * e + 1 := by simp [g, ha]
    have hge : 0 ≤ (4 * e + 1 : ℤ) := by omega
    have hUa : U a = 4 * e + 1 := by simp [U, hga, hge]
    exact_mod_cast (hto a).trans hUa
  have hhalfNat : nativeUnsigned k t a < 2 ^ (k - 1) := by
    have hpow : (2 : ℤ) ^ (k - 1) = 2 * quarter k := by
      dsimp [quarter]
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
      ring_nf
    have hs : (3 * e + 1 : ℤ) < quarter k := hstrict
    have he : (4 * e + 1 : ℤ) < 2 * quarter k := by omega
    have he' : (4 * e + 1 : ℤ) < (2 : ℤ) ^ (k - 1) := by omega
    have heNat : 4 * e + 1 < 2 ^ (k - 1) := by exact_mod_cast he'
    simpa [haU] using heNat
  apply cyclic_binary_run_bound (by omega) (nativeUnsigned k t) (nativeCarry k t)
    (fun i => by
      have hi := hU i
      have hiN : (nativeUnsigned k t i : ℤ) < ((2 ^ k - 1 : ℕ) : ℤ) := by
        rw [hto i, ← show modulus k = ((2 ^ k - 1 : ℕ) : ℤ) by
        dsimp [modulus]; norm_num]
        exact hi.2
      exact_mod_cast hiN) hrec a e haU hhalfNat


def BinaryRunProfile (k : ℕ) (c : Fin k → Bool) (a : Fin k) (e : ℕ) : Prop :=
  wordValue c a = 4 * e + 1 ∧
  physicalRunCount c = binaryRunCount e + 1 ∧
  4 * e + 1 < 2 ^ (k - 1)

theorem binary_run_profile_bound {k : ℕ} {c : Fin k → Bool} {a : Fin k} {e : ℕ}
    (h : BinaryRunProfile k c a e) :
    physicalRunCount c = binaryRunCount e + 1 ∧
      4 ^ (physicalRunCount c - 1) ≤ 3 * e + 1 := by
  rcases h with ⟨_, hr, hs⟩
  refine ⟨hr, ?_⟩
  rw [hr]
  simpa [Nat.add_sub_cancel] using separated_run_bound e

end D5.S3.Combinatorics.Circle.BinaryRunSource
