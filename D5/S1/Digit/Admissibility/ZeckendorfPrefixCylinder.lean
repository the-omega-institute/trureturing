/- GID: D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder
   generality: I
   mirror-B: none(waiver:canonical-input-transport)
   mirror-E: none(waiver:canonical-input-transport)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Actual padded Zeckendorf prefix cylinders, canonical inverse, composition, and density. -/

import D5.S1.Digit.GoldenBase4AutomataOracle
import D5.S1.Digit.Raw
import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf
import D5.S1.Deficit.Displacement.GoldenSubstStartSharpness
import Mathlib.Data.Matrix.Reflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder

open D5.S0.Conventions
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf
open scoped BigOperators
open scoped Matrix

noncomputable section

/-- The source's actual padded low digit predicate. -/
def prefixCylinder {m : Nat} (w : Fin m → Fin 2) (n : Nat) : Prop :=
  ∀ j : Fin m, zeckendorfBit n j.val = w j

/-- Internal non-adjacency of a finite binary prefix. -/
def legalPrefix {m : Nat} (w : Fin m → Fin 2) : Prop :=
  ∀ i : Fin (m - 1),
    ¬(w ⟨i.val, by omega⟩ = 1 ∧ w ⟨i.val + 1, by omega⟩ = 1)

/-- The literal Fibonacci value of the finite prefix. -/
def prefixValue {m : Nat} (w : Fin m → Fin 2) : Nat :=
  ∑ j : Fin m, (w j).val * Nat.fib (j.val + 2)

/-- The final prefix bit, with the empty-prefix convention from source 116.4. -/
def prefixSigma {m : Nat} (w : Fin m → Fin 2) : Nat :=
  if hm : m = 0 then 0 else (w ⟨m - 1, by omega⟩).val

/-- The seam-adjusted shift exponent from source 116.4. -/
def prefixHeight {m : Nat} (w : Fin m → Fin 2) : Nat :=
  m + prefixSigma w

/-- The literal composition substitution matrix in source 116.1. -/
def prefixMatrix : Matrix (Fin 2) (Fin 2) Int := !![0, 1; 1, 1]

/-- The unit-digit composition vector in source 116.1. -/
def prefixSeed : Fin 2 → Int := ![-1, 1]

/-- Actual occupied-index composition coordinates, including the unit digit. -/
def prefixIota (n : Nat) : Fin 2 → Int :=
  ((wdigits n).map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum

/-- Literal finite cardinality of the actual prefix cylinder below a real cutoff. -/
def prefixCount {m : Nat} (w : Fin m → Fin 2) (X : Real) : Nat :=
  by
    classical
    exact ((Finset.range ⌈X⌉₊).filter (fun n => prefixCylinder w n)).card

private def prefixRaw {m : Nat} (w : Fin m → Fin 2) : RawDigits :=
  ∑ j : Fin m, Finsupp.single j.val (w j).val

/-- A legal prefix's literal Fibonacci value has those digits and no higher digits. -/
theorem prefixValue_has_canonical_digits
    {m : Nat} (w : Fin m → Fin 2) (hlegal : legalPrefix w) :
    prefixCylinder w (prefixValue w) ∧
      ∀ i : Nat, m ≤ i → zeckendorfBit (prefixValue w) i = 0 := by
  let r : RawDigits := prefixRaw w
  have happly (i : Nat) :
      r i = if hi : i < m then (w ⟨i, hi⟩).val else 0 := by
    classical
    dsimp [r, prefixRaw]
    rw [Finset.sum_apply']
    by_cases hi : i < m
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [hi]
      · intro b _ hb
        have hne : b.val ≠ i := by
          intro heq
          apply hb
          exact Fin.ext heq
        simp [hne]
      · simp
    · have hzero : ∀ b : Fin m, (Finsupp.single b.val (w b).val) i = 0 := by
        intro b
        simp only [Finsupp.single_apply]
        have hne : b.val ≠ i := by omega
        simp [hne]
      simp [hi, hzero]
  have hraw : CanonicalRaw r := by
    refine ⟨?_, ?_⟩
    · intro i
      classical
      rw [happly]
      by_cases hi : i < m
      · simp [hi, Fin.is_le]
      · simp [hi]
    · intro i hi
      classical
      by_cases him : i < m
      · by_cases hnext : i + 1 < m
        · have hw := hlegal ⟨i, by omega⟩
          rw [happly] at hi ⊢
          simp [him, hnext] at hi ⊢
          by_contra hn
          have hone : (w ⟨i, him⟩).val = 1 := by omega
          have hnextone : (w ⟨i + 1, hnext⟩).val = 1 := by omega
          apply hw
          constructor
          · apply Fin.ext
            exact hone
          · apply Fin.ext
            exact hnextone
        · rw [happly] at hi ⊢
          simp [him, hnext] at hi ⊢
      · rw [happly] at hi ⊢
        simp [him] at hi ⊢
  have hvalue : rawValue r = prefixValue w := by
    classical
    have hsum : ∀ s : Finset (Fin m),
        rawValue (∑ j ∈ s, Finsupp.single j.val (w j).val) =
          ∑ j ∈ s, (w j).val * Nat.fib (j.val + 2) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [rawValue]
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, rawValue_add, ih, rawValue_single,
            Finset.sum_insert ha]
          rfl
    simpa [r, prefixRaw, prefixValue] using hsum Finset.univ
  have hprefix : ∀ i : Nat, zeckendorfBit (rawValue r) i =
      if hi : i < m then w ⟨i, hi⟩ else 0 := by
    intro i
    have hcanon := (canonicalRaw_iff_isZeckendorfRep r).1 hraw
    have hz : rawToZeckendorf r = Nat.zeckendorf (rawValue r) :=
      rawToZeckendorf_eq_zeckendorf hraw
    have hmem : i + 2 ∈ rawToZeckendorf r ↔ r i ≠ 0 := by
      rw [rawToZeckendorf]
      simp only [List.mem_map, Multiset.mem_sort, Finsupp.mem_toMultiset,
        Finsupp.mem_support_iff]
      constructor
      · rintro ⟨k, hk, heq⟩
        have : k = i := by omega
        subst k
        simpa using hk
      · intro hr
        exact ⟨i, by simpa using hr, rfl⟩
    by_cases hr : r i = 0
    · have hm : i + 2 ∉ Nat.zeckendorf (rawValue r) := by
        rw [← hz]
        exact fun hh => (hmem.mp hh) hr
      rw [happly] at hr
      by_cases hi : i < m
      · simp only [hi, ↓reduceDIte] at hr ⊢
        simp [zeckendorfBit, wdigits, hm]
        apply Fin.ext
        have hw : (w ⟨i, hi⟩).val < 2 := (w ⟨i, hi⟩).isLt
        omega
      · simp [hi, zeckendorfBit, wdigits, hm]
    · have hm : i + 2 ∈ Nat.zeckendorf (rawValue r) := by
        rw [← hz]
        exact hmem.mpr hr
      rw [happly] at hr
      by_cases hi : i < m
      · simp only [hi, ↓reduceDIte] at hr ⊢
        simp [zeckendorfBit, wdigits, hm]
        apply Fin.ext
        have hw : (w ⟨i, hi⟩).val < 2 := (w ⟨i, hi⟩).isLt
        omega
      · simp [hi] at hr
  rw [← hvalue]
  constructor
  · intro j
    simpa [j.isLt] using hprefix j.val
  · intro i hi
    simpa [Nat.not_lt.mpr hi] using hprefix i

/-- Adjoining an arbitrary shifted canonical tail preserves the actual prefix digits. -/
theorem prefixCylinder_of_shift
    {m : Nat} (t : Nat) (w : Fin m → Fin 2) (hlegal : legalPrefix w) :
    prefixCylinder w
      (prefixValue w + (goldenSubstStart^[prefixHeight w]) t) := by
  let h := prefixHeight w
  let high := wdigits ((goldenSubstStart^[h]) t)
  let low := wdigits (prefixValue w)
  have hprefix := prefixValue_has_canonical_digits w hlegal
  letI : IsTrans Nat (fun a b => b + 2 ≤ a) :=
    ⟨fun _ _ _ hab hbc => by omega⟩
  have htwo {v : Nat} (k : Nat) (hk : k ∈ wdigits v) : 2 ≤ k := by
    have hc := List.isChain_iff_pairwise.mp (wdigits_isCanonical v)
    exact (List.pairwise_append.mp hc).2.2 k hk 0 (by simp)
  have hshift (d : Nat) (v : Nat) :
      wdigits ((goldenSubstStart^[d]) v) =
        (wdigits v).map (fun k => k + d) := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Function.iterate_succ_apply', golden_subst_start_wdigits, ih,
          List.map_map]
        simp [Function.comp_def, Nat.add_assoc]
  have hhigh (a : Nat) (ha : a ∈ high) : h + 2 ≤ a := by
    dsimp [high] at ha
    rw [hshift] at ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    have hk2 : 2 ≤ k := htwo k hk
    omega
  have hlow (b : Nat) (hb : b ∈ low) : b ≤ h := by
    have hb2 : 2 ≤ b := htwo b (by simpa [low] using hb)
    have hbit : zeckendorfBit (prefixValue w) (b - 2) = 1 := by
      have hbeq : b - 2 + 2 = b := Nat.sub_add_cancel hb2
      have hmem : b ∈ wdigits (prefixValue w) := by simpa [low] using hb
      simp [zeckendorfBit, hbeq, hmem]
    have hindex : b - 2 < m := by
      by_contra hn
      have hz := hprefix.2 (b - 2) (by omega)
      rw [hbit] at hz
      exact (by decide : (1 : Fin 2) ≠ 0) hz
    have hbupper : b ≤ m + 1 := by omega
    by_cases hbsmall : b ≤ m
    · have : m ≤ h := by simp [h, prefixHeight]
      omega
    · have hmpos : 0 < m := by omega
      have hlast : b - 2 = m - 1 := by omega
      have hbitLast : zeckendorfBit (prefixValue w) (m - 1) = 1 := by
        simpa [← hlast] using hbit
      have hw : w ⟨m - 1, by omega⟩ = 1 := by
        calc
          w ⟨m - 1, by omega⟩ = zeckendorfBit (prefixValue w) (m - 1) :=
            (hprefix.1 ⟨m - 1, by omega⟩).symm
          _ = 1 := hbitLast
      have hsigma : prefixSigma w = 1 := by
        simpa [prefixSigma, Nat.ne_of_gt hmpos, hw] using
          congrArg Fin.val hw
      simp [h, prefixHeight, hsigma]
      omega
  have hcanonical : (high ++ low).IsZeckendorfRep := by
    change ((high ++ low) ++ [0]).IsChain (fun a b => b + 2 ≤ a)
    rw [List.isChain_iff_pairwise, List.append_assoc, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (List.pairwise_append.mp
        (List.isChain_iff_pairwise.mp (wdigits_isCanonical _))).1
    · exact List.isChain_iff_pairwise.mp (wdigits_isCanonical _)
    · intro a ha b hb
      rcases List.mem_append.mp hb with hb | hb
      · have hb' := hlow b hb
        have ha' := hhigh a ha
        omega
      · simp at hb
        subst b
        have ha' := hhigh a ha
        omega
  have hvalue : ((high ++ low).map Nat.fib).sum =
      prefixValue w + (goldenSubstStart^[h]) t := by
    simp [high, low, List.map_append, decode_wdigits, Nat.add_comm]
  have hdigits : high ++ low =
      wdigits (prefixValue w + (goldenSubstStart^[h]) t) :=
    wdigits_unique hcanonical hvalue
  intro j
  have hnotHigh : j.val + 2 ∉ high := by
    intro hj
    have hh := hhigh (j.val + 2) hj
    have hm : m ≤ h := by simp [h, prefixHeight]
    omega
  have hmem : j.val + 2 ∈ wdigits
      (prefixValue w + (goldenSubstStart^[h]) t) ↔ j.val + 2 ∈ low := by
    rw [← hdigits, List.mem_append]
    simp [hnotHigh]
  by_cases hb : j.val + 2 ∈ low
  · have hbit : zeckendorfBit (prefixValue w) j.val = 1 := by
      simp [zeckendorfBit, low, hb]
    have hw : w j = 1 := (hprefix.1 j).symm.trans hbit
    change (if j.val + 2 ∈ wdigits (prefixValue w + (goldenSubstStart^[h]) t)
      then (1 : Fin 2) else 0) = w j
    simp [hmem.mpr hb, hw]
  · have hbit : zeckendorfBit (prefixValue w) j.val = 0 := by
      simp [zeckendorfBit, low, hb]
    have hw : w j = 0 := (hprefix.1 j).symm.trans hbit
    have hnot : j.val + 2 ∉ wdigits
        (prefixValue w + (goldenSubstStart^[h]) t) :=
      fun hh => hb (hmem.mp hh)
    change (if j.val + 2 ∈ wdigits (prefixValue w + (goldenSubstStart^[h]) t)
      then (1 : Fin 2) else 0) = w j
    simp [hnot, hw]

/-- Every actual cylinder member has a unique canonical tail, ordered by its parameter. -/
theorem prefixCylinder_has_tail
    {m : Nat} (w : Fin m → Fin 2) (hlegal : legalPrefix w)
    (n : Nat) (hn : prefixCylinder w n) :
    (∃! t : Nat, n = prefixValue w + (goldenSubstStart^[prefixHeight w]) t ∧
      prefixIota n = prefixIota (prefixValue w) +
        prefixMatrix ^ (prefixHeight w) *ᵥ prefixIota t) ∧
      StrictMono (fun t : Nat =>
        prefixValue w + (goldenSubstStart^[prefixHeight w]) t) := by
  classical
  let h := prefixHeight w
  let digits := wdigits n
  let high := digits.filter (fun k => h + 2 ≤ k)
  let low := digits.filter (fun k => k < h + 2)
  let tail := high.map (fun k => k - h)
  letI : IsTrans Nat (fun a b => b + 2 ≤ a) :=
    ⟨fun _ _ _ hab hbc => by omega⟩
  have hpair : digits.Pairwise (fun a b => b + 2 ≤ a) :=
    (List.pairwise_append.mp
      (List.isChain_iff_pairwise.mp (wdigits_isCanonical n))).1
  have hmin (k : Nat) (hk : k ∈ digits) : 2 ≤ k :=
    (List.pairwise_append.mp
      (List.isChain_iff_pairwise.mp (wdigits_isCanonical n))).2.2 k hk 0 (by simp)
  have hlowPair : low.Pairwise (fun a b => b + 2 ≤ a) := hpair.filter _
  have hhighPair : high.Pairwise (fun a b => b + 2 ≤ a) := hpair.filter _
  have htailCanonical : tail.IsZeckendorfRep := by
    change (tail ++ [0]).IsChain (fun a b => b + 2 ≤ a)
    rw [List.isChain_iff_pairwise, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [show tail = high.map (fun k => k - h) from rfl, List.pairwise_map]
      exact hhighPair.imp_of_mem (by
        intro a b ha hb hab
        have ha' : h + 2 ≤ a := of_decide_eq_true (List.mem_filter.mp ha).2
        have hb' : h + 2 ≤ b := of_decide_eq_true (List.mem_filter.mp hb).2
        omega)
    · intro k hk z hz
      simp only [List.mem_singleton] at hz
      subst z
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
      have ha' : h + 2 ≤ a := of_decide_eq_true (List.mem_filter.mp ha).2
      omega
  let t := (tail.map Nat.fib).sum
  have htailDigits : wdigits t = tail :=
    (wdigits_unique htailCanonical rfl).symm
  have hshift (d v : Nat) :
      wdigits ((goldenSubstStart^[d]) v) =
        (wdigits v).map (fun k => k + d) := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Function.iterate_succ_apply', golden_subst_start_wdigits, ih,
          List.map_map]
        simp [Function.comp_def, Nat.add_assoc]
  have hshifted : wdigits ((goldenSubstStart^[h]) t) = high := by
    rw [hshift, htailDigits, show tail = high.map (fun k => k - h) from rfl,
      List.map_map]
    convert List.map_id high using 1
    apply List.map_congr_left
    intro k hk
    have hk' : h + 2 ≤ k := of_decide_eq_true (List.mem_filter.mp hk).2
    simp [Function.comp_def, Nat.sub_add_cancel (by omega : h ≤ k)]
  have hhighValue : (high.map Nat.fib).sum =
      (goldenSubstStart^[h]) t := by
    rw [← hshifted, decode_wdigits]
  have hprefix := prefixValue_has_canonical_digits w hlegal
  have hnoAdjacent (a b : Nat) (ha : a ∈ digits) (hb : b ∈ digits)
      (hab : a = b + 1) : False := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
    by_cases hij : i = j
    · subst j
      omega
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hg := List.pairwise_iff_get.mp hpair i j hij
        omega
      · have hg := List.pairwise_iff_get.mp hpair j i hji
        omega
  have hlowMem (k : Nat) : k ∈ low ↔ k ∈ wdigits (prefixValue w) := by
    constructor
    · intro hk
      have hkd : k ∈ digits := (List.mem_filter.mp hk).1
      have hkbound : k < h + 2 := of_decide_eq_true (List.mem_filter.mp hk).2
      have hk2 := hmin k hkd
      by_cases hj : k - 2 < m
      · have hindex : k - 2 + 2 = k := Nat.sub_add_cancel hk2
        have hbit : zeckendorfBit n (k - 2) = 1 := by
          simp [zeckendorfBit, hindex, hkd, digits]
        have hp : zeckendorfBit (prefixValue w) (k - 2) = 1 :=
          (hprefix.1 ⟨k - 2, hj⟩).trans ((hn ⟨k - 2, hj⟩).symm.trans hbit)
        by_contra hnot
        simp [zeckendorfBit, hindex, hnot] at hp
      · have hsigma : prefixSigma w = 1 := by
          have hh : h = m + prefixSigma w := rfl
          have hsle : prefixSigma w ≤ 1 := by
            unfold prefixSigma
            split
            · omega
            · have hw := (w ⟨m - 1, by omega⟩).isLt
              omega
          omega
        have hmpos : 0 < m := by
          by_contra hm0
          have : m = 0 := by omega
          simp [prefixSigma, this] at hsigma
        have hlast : w ⟨m - 1, by omega⟩ = 1 := by
          have hw := (w ⟨m - 1, by omega⟩).isLt
          simp [prefixSigma, Nat.ne_of_gt hmpos] at hsigma
          apply Fin.ext
          omega
        have hlastN : m + 1 ∈ digits := by
          have heq := hn ⟨m - 1, by omega⟩
          rw [hlast] at heq
          have hmidx : m - 1 + 2 = m + 1 := by omega
          by_contra hnot
          simp [zeckendorfBit, hmidx, hnot, digits] at heq
        have hh : h = m + prefixSigma w := rfl
        have hkindex : k = m + 2 := by omega
        exact False.elim (hnoAdjacent k (m + 1) hkd hlastN (by omega))
    · intro hk
      have hk2 : 2 ≤ k := by
        have hc := (List.pairwise_append.mp
          (List.isChain_iff_pairwise.mp (wdigits_isCanonical (prefixValue w)))).2.2
        exact hc k hk 0 (by simp)
      have hj : k - 2 < m := by
        by_contra hnot
        have hz := hprefix.2 (k - 2) (by omega)
        have hindex : k - 2 + 2 = k := Nat.sub_add_cancel hk2
        simp [zeckendorfBit, hindex, hk] at hz
      have hindex : k - 2 + 2 = k := Nat.sub_add_cancel hk2
      have hbit : zeckendorfBit (prefixValue w) (k - 2) = 1 := by
        simp [zeckendorfBit, hindex, hk]
      have hnbit : zeckendorfBit n (k - 2) = 1 :=
        (hn ⟨k - 2, hj⟩).trans ((hprefix.1 ⟨k - 2, hj⟩).symm.trans hbit)
      have hkd : k ∈ digits := by
        by_contra hnot
        simp [zeckendorfBit, hindex, hnot, digits] at hnbit
      apply List.mem_filter.mpr
      refine ⟨hkd, ?_⟩
      simp only [decide_eq_true_eq]
      have hh : h = m + prefixSigma w := rfl
      omega
  have hlowEq : low = wdigits (prefixValue w) := by
    have hd : low.Pairwise (· > ·) := hlowPair.imp (by omega)
    have hp : (wdigits (prefixValue w)).Pairwise (· > ·) :=
      (List.pairwise_append.mp
        (List.isChain_iff_pairwise.mp (wdigits_isCanonical (prefixValue w)))).1.imp
        (by omega)
    apply hd.eq_of_mem_iff hp
    exact hlowMem
  have hsplit : (digits.map Nat.fib).sum =
      (high.map Nat.fib).sum + (low.map Nat.fib).sum := by
    have splitAny (xs : List Nat) : (xs.map Nat.fib).sum =
        ((xs.filter (fun k => h + 2 ≤ k)).map Nat.fib).sum +
          ((xs.filter (fun k => k < h + 2)).map Nat.fib).sum := by
      induction xs with
      | nil => simp
      | cons k ks ih =>
          by_cases hk : h + 2 ≤ k
          · have hnk : ¬ k < h + 2 := by omega
            simp only [List.map_cons, List.sum_cons, List.filter_cons,
              decide_eq_true_eq, if_pos hk, if_neg hnk]
            omega
          · have hnk : k < h + 2 := by omega
            simp only [List.map_cons, List.sum_cons, List.filter_cons,
              decide_eq_true_eq, if_neg hk, if_pos hnk]
            omega
    exact splitAny digits
  have hEq : n = prefixValue w + (goldenSubstStart^[prefixHeight w]) t := calc
    n = (digits.map Nat.fib).sum := (decode_wdigits n).symm
    _ = (high.map Nat.fib).sum + (low.map Nat.fib).sum := hsplit
    _ = prefixValue w + (goldenSubstStart^[h]) t := by
      rw [hhighValue, hlowEq, decode_wdigits]
      simp [Nat.add_comm]
  have hcoordSplit (xs : List Nat) :
      (xs.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum =
        ((xs.filter (fun k => h + 2 ≤ k)).map fun k =>
          prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum +
        ((xs.filter (fun k => k < h + 2)).map fun k =>
          prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum := by
    induction xs with
    | nil => simp
    | cons k ks ih =>
        by_cases hk : h + 2 ≤ k
        · have hnk : ¬ k < h + 2 := by omega
          simp only [List.map_cons, List.sum_cons, List.filter_cons,
            decide_eq_true_eq, if_pos hk, if_neg hnk]
          rw [ih]
          abel
        · have hnk : k < h + 2 := by omega
          simp only [List.map_cons, List.sum_cons, List.filter_cons,
            decide_eq_true_eq, if_neg hk, if_pos hnk]
          rw [ih]
          abel
  have hcoordHigh :
      (high.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum =
        prefixMatrix ^ h *ᵥ prefixIota t := by
    have hdown (xs : List Nat) (hxs : ∀ k ∈ xs, h + 2 ≤ k) :
        (xs.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum =
          prefixMatrix ^ h *ᵥ
            ((xs.map fun k => k - h).map fun k =>
              prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum := by
      induction xs with
      | nil => simp
      | cons k ks ih =>
          have hk : h + 2 ≤ k := hxs k (by simp)
          have hks : ∀ a ∈ ks, h + 2 ≤ a := by
            intro a ha
            exact hxs a (by simp [ha])
          simp only [List.map_cons, List.sum_cons, Matrix.mulVec_add]
          rw [← ih hks]
          have hidx : h + ((k - h) - 2) = k - 2 := by omega
          rw [Matrix.mulVec_mulVec, ← pow_add, hidx]
    have hbound : ∀ k ∈ high, h + 2 ≤ k := by
      intro k hk
      exact of_decide_eq_true (List.mem_filter.mp hk).2
    rw [hdown high hbound, prefixIota, htailDigits]
  have hcoord : prefixIota n = prefixIota (prefixValue w) +
      prefixMatrix ^ (prefixHeight w) *ᵥ prefixIota t := by
    change (digits.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum = _
    rw [hcoordSplit digits]
    change (high.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum +
        (low.map fun k => prefixMatrix ^ (k - 2) *ᵥ prefixSeed).sum = _
    rw [hlowEq, hcoordHigh]
    rw [add_comm]
    rfl
  have hstrict : StrictMono (fun t : Nat =>
      prefixValue w + (goldenSubstStart^[prefixHeight w]) t) := by
    intro a b hab
    exact Nat.add_lt_add_left ((goldenSubstStart_strictMono.iterate _ ) hab) _
  refine ⟨⟨t, ⟨hEq, hcoord⟩, ?_⟩, hstrict⟩
  intro u hu
  exact hstrict.injective (hu.1.symm.trans hEq)

/-- The actual real-cutoff cylinder count has fixed-prefix bounded discrepancy. -/
theorem prefixCylinder_real_cutoff_discrepancy
    {m : Nat} (w : Fin m → Fin 2) (hlegal : legalPrefix w) :
    (∀ X : Real, 0 ≤ X →
      |(prefixCount w X : Real) -
          X / Real.goldenRatio ^ (prefixHeight w)| ≤
        (prefixValue w : Real) +
          (Real.goldenRatio + 1) ^ (prefixHeight w) + 1) ∧
      Filter.Tendsto
        (fun X : Real => (prefixCount w X : Real) / X)
        Filter.atTop (nhds (1 / Real.goldenRatio ^ (prefixHeight w))) ∧
      Filter.Tendsto
        (fun N : Nat => (prefixCount w (N : Real) : Real) / (N : Real))
        Filter.atTop (nhds (1 / Real.goldenRatio ^ (prefixHeight w))) ∧
      ∀ {r : Nat} (b : Fin r → Fin 2), legalPrefix (Fin.append w b) →
        Filter.Tendsto
          (fun X : Real =>
            (prefixCount (Fin.append w b) X : Real) /
              (prefixCount w X : Real))
          Filter.atTop
          (nhds (1 / Real.goldenRatio ^
            (r + prefixSigma (Fin.append w b) - prefixSigma w))) := by
  have core {m : Nat} (w : Fin m → Fin 2) (hlegal : legalPrefix w) :
      (∀ X : Real, 0 ≤ X →
        |(prefixCount w X : Real) -
            X / Real.goldenRatio ^ (prefixHeight w)| ≤
          (prefixValue w : Real) +
            (Real.goldenRatio + 1) ^ (prefixHeight w) + 1) ∧
        Filter.Tendsto
          (fun X : Real => (prefixCount w X : Real) / X)
          Filter.atTop (nhds (1 / Real.goldenRatio ^ (prefixHeight w))) ∧
        Filter.Tendsto
          (fun N : Nat => (prefixCount w (N : Real) : Real) / (N : Real))
          Filter.atTop (nhds (1 / Real.goldenRatio ^ (prefixHeight w))) := by
    classical
    let phi := Real.goldenRatio
    let h := prefixHeight w
    let alpha := phi ^ h
    let B : Real := (prefixValue w : Real) + (phi + 1) ^ h
    let f : Nat → Nat := fun t => prefixValue w + (goldenSubstStart^[h]) t
    have hphi : 1 ≤ phi := Real.one_lt_goldenRatio.le
    have hαpos : 0 < alpha := pow_pos Real.goldenRatio_pos _
    have hαone : 1 ≤ alpha := one_le_pow₀ hphi
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have herror (v : Nat) :
        |(goldenSubstStart v : Real) - phi * v| ≤ 1 := by
      have hw := GoldenSubstStartSharpness.golden_subst_start_error_window v
      have hi : phi⁻¹ ≤ 1 := (inv_le_one₀ Real.goldenRatio_pos).2 hphi
      have hi2 : phi⁻¹ ^ 2 ≤ 1 :=
        pow_le_one₀ (inv_pos.mpr Real.goldenRatio_pos).le hi
      exact abs_le.mpr ⟨by dsimp [phi] at *; linarith [hw.1],
        by dsimp [phi] at *; linarith [hw.2]⟩
    have hiter (d : Nat) (t : Nat) :
        |((goldenSubstStart^[d]) t : Real) - phi ^ d * t| ≤
          (phi + 1) ^ d := by
      induction d generalizing t with
      | zero => simp
      | succ d ih =>
          have hs := herror ((goldenSubstStart^[d]) t)
          have ht := ih t
          have hpow : 1 ≤ (phi + 1) ^ d := one_le_pow₀ (by linarith)
          rw [Function.iterate_succ_apply']
          have hid : (goldenSubstStart ((goldenSubstStart^[d]) t) : Real) -
              phi ^ (d + 1) * t =
            ((goldenSubstStart ((goldenSubstStart^[d]) t) : Real) -
                phi * ((goldenSubstStart^[d]) t : Real)) +
              phi * (((goldenSubstStart^[d]) t : Real) - phi ^ d * t) := by
            rw [pow_succ]
            ring
          rw [hid]
          calc
            |_ + _| ≤
                |(goldenSubstStart ((goldenSubstStart^[d]) t) : Real) -
                    phi * ((goldenSubstStart^[d]) t : Real)| +
                  |phi * (((goldenSubstStart^[d]) t : Real) - phi ^ d * t)| :=
                    abs_add_le _ _
            _ ≤ 1 + phi * (phi + 1) ^ d := by
              rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
              exact add_le_add hs (mul_le_mul_of_nonneg_left ht Real.goldenRatio_pos.le)
            _ ≤ (phi + 1) ^ (d + 1) := by
              rw [pow_succ]
              nlinarith
    have hbound (t : Nat) : |(f t : Real) - alpha * t| ≤ B := by
      have hi := hiter h t
      simp only [f, Nat.cast_add]
      have hform : (prefixValue w : Real) +
          ((goldenSubstStart^[h]) t : Real) - alpha * t =
        (prefixValue w : Real) +
          (((goldenSubstStart^[h]) t : Real) - phi ^ h * t) := by
        dsimp [alpha]
        ring
      rw [hform]
      calc
        _ ≤ |(prefixValue w : Real)| +
            |((goldenSubstStart^[h]) t : Real) - phi ^ h * t| := abs_add_le _ _
        _ ≤ B := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          simpa [B, add_comm, add_left_comm] using
            add_le_add_left hi (prefixValue w : Real)
    have hmono : StrictMono f := by
      intro a b hab
      exact Nat.add_lt_add_left ((goldenSubstStart_strictMono.iterate _) hab) _
    have hid : ∀ t, t ≤ f t := hmono.id_le
    have hdiscrepancy (X : Real) (hX : 0 ≤ X) :
        |(prefixCount w X : Real) - X / alpha| ≤ B + 1 := by
      let N := ⌈X⌉₊
      let params := (Finset.range N).filter (fun t => (f t : Real) < X)
      have hcount : prefixCount w X = params.card := by
        unfold prefixCount
        symm
        apply Finset.card_bij (fun t _ => f t)
        · intro t ht
          rcases Finset.mem_filter.mp ht with ⟨_, htX⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr htX), ?_⟩
          exact prefixCylinder_of_shift t w hlegal
        · intro a _ b _ hab
          exact hmono.injective hab
        · intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hnN, hnC⟩
          obtain ⟨t, ⟨ht, _⟩, _⟩ := (prefixCylinder_has_tail w hlegal n hnC).1
          have htN : t < N := lt_of_le_of_lt (hid t) (by simpa [ht] using hnN)
          have htX : (f t : Real) < X := by
            change ((prefixValue w + (goldenSubstStart^[prefixHeight w]) t : Nat) : Real) < X
            rw [← ht]
            exact Nat.lt_ceil.mp (Finset.mem_range.mp hnN)
          exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htN, htX⟩, ht.symm⟩
      let L := (X - B) / alpha
      let U := (X + B) / alpha
      have hLleX : L ≤ X := by
        dsimp [L]
        apply (div_le_iff₀ hαpos).2
        nlinarith
      have hU : 0 ≤ U := div_nonneg (add_nonneg hX hB) hαpos.le
      have hLower : ⌈L⌉₊ ≤ params.card := by
        have hsubset : Finset.range ⌈L⌉₊ ⊆ params := by
          intro t ht
          have htL : (t : Real) < L := Nat.lt_ceil.mp (Finset.mem_range.mp ht)
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr (lt_of_lt_of_le htL hLleX)), ?_⟩
          have hb := hbound t
          have htop := (abs_le.mp hb).2
          dsimp [L] at htL
          have hlinear : alpha * t < X - B := by
            simpa only [mul_comm] using (lt_div_iff₀ hαpos).mp htL
          dsimp [f, alpha] at htop ⊢
          linarith
        simpa using Finset.card_le_card hsubset
      have hUpper : params.card ≤ ⌈U⌉₊ := by
        have hsubset : params ⊆ Finset.range ⌈U⌉₊ := by
          intro t ht
          have htX := (Finset.mem_filter.mp ht).2
          have hb := hbound t
          have hbottom := (abs_le.mp hb).1
          have hlinear : alpha * t < X + B := by linarith
          exact Finset.mem_range.mpr (Nat.lt_ceil.mpr
            ((lt_div_iff₀ hαpos).2 (by simpa only [mul_comm] using hlinear)))
        simpa using Finset.card_le_card hsubset
      have hceilL : L ≤ (⌈L⌉₊ : Real) := Nat.le_ceil L
      have hceilU : (⌈U⌉₊ : Real) < U + 1 := Nat.ceil_lt_add_one hU
      have hBc : B / alpha ≤ B := by
        apply (div_le_iff₀ hαpos).2
        nlinarith
      have hlow : X / alpha - B / alpha ≤ (prefixCount w X : Real) := by
        have hc : (⌈L⌉₊ : Real) ≤ (params.card : Real) := by exact_mod_cast hLower
        rw [hcount]
        have hform : L = X / alpha - B / alpha := by dsimp [L]; ring
        linarith
      have hhigh : (prefixCount w X : Real) ≤ X / alpha + B / alpha + 1 := by
        have hc : (params.card : Real) ≤ (⌈U⌉₊ : Real) := by exact_mod_cast hUpper
        rw [hcount]
        have hform : U = X / alpha + B / alpha := by dsimp [U]; ring
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hrem : Filter.Tendsto
        (fun X : Real =>
          ((prefixCount w X : Real) - X / alpha) / X)
        Filter.atTop (nhds 0) := by
      apply tendsto_bdd_div_atTop_nhds_zero
      · filter_upwards [Filter.eventually_ge_atTop (0 : Real)] with X hX
        exact (abs_le.mp (hdiscrepancy X hX)).1
      · filter_upwards [Filter.eventually_ge_atTop (0 : Real)] with X hX
        exact (abs_le.mp (hdiscrepancy X hX)).2
      · exact Filter.tendsto_id
    have hmain : Filter.Tendsto
        (fun X : Real => (1 : Real) / alpha +
          ((prefixCount w X : Real) - X / alpha) / X)
        Filter.atTop (nhds (1 / alpha)) := by
      simpa using tendsto_const_nhds.add hrem
    have hreal : Filter.Tendsto
        (fun X : Real => (prefixCount w X : Real) / X)
        Filter.atTop (nhds (1 / alpha)) := by
      apply hmain.congr'
      filter_upwards [Filter.eventually_ge_atTop (1 : Real)] with X hX
      have hX0 : X ≠ 0 := by linarith
      field_simp [hX0, hαpos.ne']
      ring
    refine ⟨hdiscrepancy, hreal, ?_⟩
    dsimp [alpha, h, phi] at hreal
    simpa only [Function.comp_def] using
      hreal.comp tendsto_natCast_atTop_atTop
  -- The extension ratio follows from two instances of the actual count estimate.
  obtain ⟨herrorW, hden, hdenNat⟩ := core w hlegal
  refine ⟨herrorW, hden, hdenNat, ?_⟩
  intro r b hlegalB
  have hnum := (core (Fin.append w b) hlegalB).2.1
  have hdenPos : 0 < (1 : Real) / Real.goldenRatio ^ (prefixHeight w) := by
    positivity
  have hquot := hnum.div hden hdenPos.ne'
  have hpositive : ∀ᶠ X : Real in Filter.atTop,
      0 < (prefixCount w X : Real) / X :=
    hden.eventually (lt_mem_nhds hdenPos)
  have hevent :
      (fun X : Real =>
        ((prefixCount (Fin.append w b) X : Real) / X) /
          ((prefixCount w X : Real) / X)) =ᶠ[Filter.atTop]
      (fun X : Real =>
        (prefixCount (Fin.append w b) X : Real) /
          (prefixCount w X : Real)) := by
    filter_upwards [hpositive, Filter.eventually_ge_atTop (1 : Real)] with X hposX hX
    have hX0 : X ≠ 0 := by linarith
    have hdenX : (prefixCount w X : Real) ≠ 0 := by
      intro hz
      simp [hz] at hposX
    field_simp [hX0, hdenX]
  have hσle : prefixSigma w ≤ 1 := by
    unfold prefixSigma
    split
    · omega
    · have hw := (w ⟨m - 1, by omega⟩).isLt
      omega
  have hheight : prefixHeight (Fin.append w b) =
      prefixHeight w + (r + prefixSigma (Fin.append w b) - prefixSigma w) := by
    by_cases hr : r = 0
    · subst r
      have hword : Fin.append w b = w := by
        rw [Fin.append_right_nil w b rfl]
        funext j
        rfl
      simp [hword, prefixHeight]
    · unfold prefixHeight
      omega
  have hlimit :
      ((1 : Real) / Real.goldenRatio ^ (prefixHeight (Fin.append w b))) /
          ((1 : Real) / Real.goldenRatio ^ (prefixHeight w)) =
        (1 : Real) /
          Real.goldenRatio ^
            (r + prefixSigma (Fin.append w b) - prefixSigma w) := by
    rw [hheight, pow_add]
    have hp : Real.goldenRatio ^ (prefixHeight w) ≠ 0 :=
      pow_ne_zero _ Real.goldenRatio_pos.ne'
    have hq : Real.goldenRatio ^
        (r + prefixSigma (Fin.append w b) - prefixSigma w) ≠ 0 :=
      pow_ne_zero _ Real.goldenRatio_pos.ne'
    field_simp [hp, hq]
  rw [← hlimit]
  exact hquot.congr' hevent

end

end D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
