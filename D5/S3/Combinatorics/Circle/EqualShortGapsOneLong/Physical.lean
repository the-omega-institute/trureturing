/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Physical
   generality: I
   mirror-B: none(waiver:consumed-physical-inventory)
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal one-deferred-label inventory and its marked physical ear. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

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
  · rw [show a = (a - 1) + 1 by omega, List.range'_succ]
    simp only [show size a p d - a + (a - 1) = size a p d - 1 by omega,
      List.append_assoc]

private theorem pre_length (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    (preWord a p d).length = size a p d - 1 := by
  have h := (raw_inventory a p d ha hp hd).length_eq
  rw [raw_last a p d ha hp hd] at h
  simp only [List.length_append, List.length_singleton, List.length_range] at h
  omega

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
    rw [Fin.sum_univ_eq_sum_range] at h
    simpa only [List.sum_map_range, actualSource] using h
  have hnp : (preWord a p d ++ [k, k - 1]).Perm (List.range (k + 1)) := by
    have he : (preWord a p d ++ [k, k - 1]).Perm (rawWord a p d ++ [k]) := by
      rw [raw_last a p d ha hp hd]
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add, List.cons_append, List.singleton_append]
      ac_rfl
    exact he.trans (by simpa only [List.range_succ, Nat.succ_eq_add_one] using hinv.append_right [k])
  have he := marked_word k (k - 1) hk (preWord a p d) [k - 1]
    (pre_length a p d ha hp hd) (by simpa only [← raw_last a p d ha hp hd] using hinv)
  rw [← raw_last a p d ha hp hd] at he
  refine ⟨lift_order k E hk _ hinv hold (hz k E hk), ?_⟩
  simpa only [cut, hne, ite_false, physicalWord, he, List.cons_append,
    List.singleton_append] using
    lift_order (k + 1) (2 * E) (by omega) _ hnp hnew (hz (k + 1) (2 * E) (by omega))

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
