/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Physical
   generality: I
   mirror-B: none(waiver:consumed-physical-inventory)
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal one-deferred-label inventory and its marked physical ear. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! Exact natural-label inventories, their physical realizations and the literal ear. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth PeriodicShortening RunFirstEarTransport
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-- The physical size, including the long gap and all short gaps. -/
def size (a p d : ℕ) : ℕ := d + a * (p - 1)

/-- The exact old labels: at most one long-positive label is deferred. -/
def rawWord (a p d : ℕ) : List ℕ :=
  let k := size a p d
  let t := d - a - 1
  if d ≤ a + 1 then List.range k else
    List.range t ++ List.range' (t + 1) (k - a - (t + 1)) ++ [t] ++
      List.range' (k - a) a

/-- The same literal word, realized by actual physical `Fin` labels. -/
def physicalWord (a p d : ℕ) (hk : 0 < size a p d) : List (Fin (size a p d)) :=
  (rawWord a p d).map (label (size a p d) hk)

/-- The unique fresh physical occurrence is inserted at this old-word cut. -/
def cut (a p d : ℕ) : ℕ := if d = a then a - 1 else size a p d - 1

private theorem raw_inventory (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    (rawWord a p d).Perm (List.range (size a p d)) := by
  unfold rawWord
  dsimp only
  split_ifs with h
  · exact List.Perm.refl _
  · let k := size a p d
    let t := d - a - 1
    have hkd : d ≤ k := by dsimp [k, size]; omega
    have ht : t + 1 ≤ k - a := by dsimp [t]; omega
    have hta : t + 1 + (k - a - (t + 1)) = k - a := by omega
    have hka : k - a + a = k := by omega
    have h1 : List.range t ++ [t] = List.range (t + 1) := by
      simpa only [Nat.succ_eq_add_one] using (List.range_succ (n := t)).symm
    have h2 : List.range (t + 1) ++ List.range' (t + 1) (k - a - (t + 1)) =
        List.range (k - a) := by
      simp only [List.range_eq_range']
      simpa only [Nat.zero_add, hta] using
        List.range'_append_1 (s := 0) (m := t + 1) (n := k - a - (t + 1))
    have h3 : List.range (k - a) ++ List.range' (k - a) a = List.range k := by
      simp only [List.range_eq_range']
      simpa only [Nat.zero_add, hka] using
        List.range'_append_1 (s := 0) (m := k - a) (n := a)
    change (List.range t ++ List.range' (t + 1) (k - a - (t + 1)) ++ [t] ++
      List.range' (k - a) a).Perm (List.range k)
    rw [← h3, ← h2, ← h1]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl

private theorem ascending_physical (a p d : ℕ) (hk : 0 < size a p d)
    (hd : d ≤ a + 1) : physicalWord a p d hk = List.finRange (size a p d) := by
  unfold physicalWord rawWord
  simp only [hd, ite_true]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    apply Fin.ext
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, label]
    exact Nat.mod_eq_of_lt (by simpa using hi)

private theorem unit_physical (a d : ℕ) (ha : 2 ≤ a) (hd : a ≤ d)
    (hk : 0 < size a 1 d) : physicalWord a 1 d hk = List.finRange d := by
  have hr : rawWord a 1 d = List.range d := by
    unfold rawWord
    simp only [size, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    split_ifs with h
    · rfl
    · have hs : d - a - 1 + 1 = d - a := by omega
      have hlen : d - a - (d - a - 1 + 1) = 0 := by omega
      rw [hlen, List.range'_zero, List.append_nil, ← List.range_succ]
      simp only [Nat.succ_eq_add_one, hs, List.range_eq_range']
      simpa only [Nat.zero_add, show d - a + a = d by omega] using
        List.range'_append_1 (s := 0) (m := d - a) (n := a)
  unfold physicalWord
  rw [hr]
  change (List.range d).map (label d hk) = List.finRange d
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_finRange]
  · intro i hi hi'
    apply Fin.ext
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange,
      Fin.val_cast, Fin.val_mk, label]
    exact Nat.mod_eq_of_lt (by simpa only [List.length_map, List.length_range] using hi)

private theorem unit_cut (a d : ℕ) : cut a 1 d = d - 1 := by
  unfold cut size
  split_ifs with h
  · omega
  · simp

private def preWord (a p d : ℕ) : List ℕ :=
  let k := size a p d
  let t := d - a - 1
  if d ≤ a + 1 then List.range (k - 1) else
    List.range t ++ List.range' (t + 1) (k - a - (t + 1)) ++ [t] ++
      List.range' (k - a) (a - 1)

private theorem raw_last (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    rawWord a p d = preWord a p d ++ [size a p d - 1] := by
  have hkd : d ≤ size a p d := by dsimp [size]; omega
  unfold rawWord preWord
  dsimp only
  split_ifs with h
  · simpa only [show size a p d - 1 + 1 = size a p d by omega,
      Nat.succ_eq_add_one] using (List.range_succ (n := size a p d - 1))
  · have h := (List.range'_1_concat (s := size a p d - a) (n := a - 1)).symm
    rw [show a - 1 + 1 = a by omega,
      show size a p d - a + (a - 1) = size a p d - 1 by omega] at h
    rw [← h]
    simp only [List.append_assoc]

private theorem pre_length (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    (preWord a p d).length = size a p d - 1 := by
  have h := (raw_inventory a p d ha hp hd).length_eq
  rw [raw_last a p d ha hp hd] at h
  simp only [List.length_append, List.length_singleton, List.length_range] at h
  omega

private def initialWord (a d : ℕ) : List ℕ :=
  if d ≤ a + 1 then List.range (d - 1) else
    List.range (d - a - 1) ++ List.range' (d - a) (a - 1)

private def reserveWord (a d : ℕ) : List ℕ :=
  if d ≤ a + 1 then [] else [d - a - 1]

private def middleWord (a p d : ℕ) : List ℕ :=
  (List.range (p - 2)).flatMap (fun j =>
    (d - 1 + a * j) :: List.range' (d + a * j) (a - 1)) ++
      [d - 1 + a * (p - 2)]

private theorem middle_range (a p d : ℕ) (ha : 2 ≤ a) (hp : 2 ≤ p) (hd : a ≤ d) :
    middleWord a p d = List.range' (d - 1) (a * (p - 2) + 1) := by
  have blocks (n : ℕ) :
      (List.range n).flatMap (fun j =>
        (d - 1 + a * j) :: List.range' (d + a * j) (a - 1)) =
        List.range' (d - 1) (a * n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_singleton]
      have hb : (d - 1 + a * n) :: List.range' (d + a * n) (a - 1) =
          List.range' (d - 1 + a * n) a := by
        simpa only [show a - 1 + 1 = a by omega,
          show d - 1 + a * n + 1 = d + a * n by omega] using
          (List.range'_succ (s := d - 1 + a * n) (n := a - 1) (step := 1)).symm
      rw [hb]
      simpa only [Nat.mul_succ] using
        List.range'_append_1 (s := d - 1) (m := a * n) (n := a)
  unfold middleWord
  rw [blocks]
  simpa only [Nat.add_comm] using
    (List.range'_1_concat (s := d - 1) (n := a * (p - 2))).symm

private theorem initial_inventory (a d : ℕ) (ha : 2 ≤ a) (hd : a ≤ d) :
    (initialWord a d ++ reserveWord a d).Perm (List.range (d - 1)) := by
  unfold initialWord reserveWord
  split_ifs with h
  · simp
  · have hs : d - a - 1 + 1 = d - a := by omega
    have he : List.range (d - a - 1) ++ [d - a - 1] ++
        List.range' (d - a) (a - 1) = List.range (d - 1) := by
      rw [← List.range_succ]
      simp only [Nat.succ_eq_add_one, hs, List.range_eq_range']
      simpa only [Nat.zero_add, show d - a + (a - 1) = d - 1 by omega] using
        List.range'_append_1 (s := 0) (m := d - a) (n := a - 1)
    rw [← he]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl

private theorem physical_decomposition (a p d : ℕ) (ha : 2 ≤ a)
    (hp : 2 ≤ p) (hd : a ≤ d) :
    rawWord a p d = initialWord a d ++ middleWord a p d ++ reserveWord a d ++
      List.range' (size a p d - a) (a - 1) ++ [size a p d - 1] := by
  let k := size a p d
  have hk : k = d + a * (p - 2) + a := by
    dsimp [k, size]
    have h : p - 1 = (p - 2) + 1 := by omega
    rw [h, Nat.mul_add]
    omega
  rw [middle_range a p d ha hp hd]
  have hs : d - 1 + (a * (p - 2) + 1) = k - a := by omega
  have htail : List.range' (k - a) (a - 1) ++ [k - 1] = List.range' (k - a) a := by
    simpa only [show a - 1 + 1 = a by omega,
      show k - a + (a - 1) = k - 1 by omega] using
      (List.range'_1_concat (s := k - a) (n := a - 1)).symm
  change rawWord a p d = initialWord a d ++ List.range' (d - 1) (a * (p - 2) + 1) ++
    reserveWord a d ++ List.range' (k - a) (a - 1) ++ [k - 1]
  rw [List.append_assoc _ _ [k - 1], htail]
  unfold rawWord initialWord reserveWord
  dsimp only
  split_ifs with h
  · simp only [List.append_nil]
    have h1 : List.range (d - 1) ++ List.range' (d - 1) (a * (p - 2) + 1) =
        List.range (k - a) := by
      simp only [List.range_eq_range']
      simpa only [Nat.zero_add, hs] using
        List.range'_append_1 (s := 0) (m := d - 1) (n := a * (p - 2) + 1)
    rw [h1]
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add, show k - a + a = k by omega] using
      (List.range'_append_1 (s := 0) (m := k - a) (n := a)).symm
  · have h1 : List.range' (d - a) (a - 1) ++
        List.range' (d - 1) (a * (p - 2) + 1) =
        List.range' (d - a) (k - a - (d - a)) := by
      simpa only [show d - a + (a - 1) = d - 1 by omega,
        show a - 1 + (a * (p - 2) + 1) = k - a - (d - a) by omega] using
        List.range'_append_1 (s := d - a) (m := a - 1) (n := a * (p - 2) + 1)
    simp only [show d - a - 1 + 1 = d - a by omega, List.append_assoc]
    rw [← List.append_assoc (List.range' (d - a) (a - 1)), h1]

private theorem lift_last_joint (a p d E : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (hne : d ≠ a)
    (hold : InStrip (fun i => centered (modulus (size a p d)) ((2 : ℤ) ^ i * E))
      (modulus (size a p d) / 2) 0 (rawWord a p d))
    (hnew : InStrip (fun i => centered (modulus (size a p d + 1)) ((2 : ℤ) ^ i * (2 * E)))
      (modulus (size a p d + 1) / 2) 0
      (preWord a p d ++ [size a p d, size a p d - 1])) :
    OriginalOrder (size a p d) E (physicalWord a p d (by dsimp [size]; omega)) ∧
    OriginalOrder (size a p d + 1) (2 * E)
      (earWord (size a p d) (physicalWord a p d (by dsimp [size]; omega)) (cut a p d)) := by
  let k := size a p d
  have hk : 0 < k := by dsimp [k, size]; omega
  have hinv := raw_inventory a p d ha hp hd
  have hz (n w : ℕ) (hn : 0 < n) :
      ((List.range n).map (fun i => centered (modulus n) ((2 : ℤ) ^ i * w))).sum = 0 := by
    have h := (ZeroSumSubsets.source_cycle hn w).2.1
    change (∑ i : Fin n, centered (modulus n) ((2 : ℤ) ^ i.val * w)) = 0 at h
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => centered (modulus n) ((2 : ℤ) ^ i * w)) n] at h
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    exact h
  have hnp : (preWord a p d ++ [k, k - 1]).Perm (List.range (k + 1)) := by
    have he : (preWord a p d ++ [k, k - 1]).Perm (rawWord a p d ++ [k]) := by
      rw [raw_last a p d ha hp hd]
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add, List.cons_append, List.singleton_append]
      ac_rfl
    exact he.trans (by simpa only [List.range_succ, Nat.succ_eq_add_one] using hinv.append_right [k])
  have hraw : rawWord a p d = preWord a p d ++ [k - 1] := raw_last a p d ha hp hd
  have hpre : (preWord a p d ++ [k - 1]).Perm (List.range k) := by
    rw [← hraw]
    exact hinv
  have he := marked_word k (k - 1) hk (preWord a p d) [k - 1]
    (pre_length a p d ha hp hd) hpre
  rw [← hraw] at he
  refine ⟨lift_order k E hk _ hinv hold (hz k E hk), ?_⟩
  simp only [cut, hne, ite_false]
  change OriginalOrder (k + 1) (2 * E)
    (earWord k ((rawWord a p d).map (label k hk)) (k - 1))
  rw [he]
  exact lift_order (k + 1) (2 * E) (by omega) _ hnp hnew
    (hz (k + 1) (2 * E) (by omega))

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
