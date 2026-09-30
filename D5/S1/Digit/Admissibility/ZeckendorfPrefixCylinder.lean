/- GID: D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder
   generality: I
   mirror-B: none(waiver:canonical-input-transport)
   mirror-E: none(waiver:canonical-input-transport)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Actual padded Zeckendorf prefix cylinders and their seam parameter. -/

import D5.S1.Digit.GoldenBase4AutomataOracle
import D5.S1.Digit.Raw
import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf

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

end

end D5.S1.Digit.Admissibility.ZeckendorfPrefixCylinder
