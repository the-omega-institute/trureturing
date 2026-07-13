/- GID: D5/S1/Digit/Raw
   generality: I
   mirror-B: D5/B/S1/Digit/Raw
   mirror-E: none(waiver:algebraically-proved)
   anchors: [gict/v3.6/I.2/definition/1.4, mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Raw W digits bridge finite multiplicities to mathlib Zeckendorf lists. -/

import D5.S0.Conventions.WDigits
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort

namespace D5.S1.Digit

open D5.S0.Conventions

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- A finite raw W-digit string; coefficients need not be binary. -/
abbrev RawDigits := ℕ →₀ ℕ

/-- Evaluation against the W weights `W_i = Fib (i + 2)`. -/
def rawValue (r : RawDigits) : ℕ :=
  r.sum fun i coefficient ↦ coefficient * wValue i

@[simp] theorem rawValue_single (i coefficient : ℕ) :
    rawValue (Finsupp.single i coefficient) = coefficient * wValue i := by
  classical
  simp [rawValue]

/-- Evaluation is an additive map from raw digit strings. -/
theorem rawValue_add (r s : RawDigits) :
    rawValue (r + s) = rawValue r + rawValue s := by
  classical
  simp [rawValue, Finsupp.sum_add_index, add_mul]

/-- Binary, nonadjacent raw W digits. -/
def CanonicalRaw (r : RawDigits) : Prop :=
  (∀ i, r i ≤ 1) ∧ (∀ i, r i = 1 → r (i + 1) = 0)

/--
Convert raw W indices to mathlib's Zeckendorf convention. Raw coefficients become
multiplicities, the indices are sorted in descending order, and `2` is added because
`W_i = Fib (i + 2)` while mathlib stores Fibonacci indices at least `2`.
-/
noncomputable def rawToZeckendorf (r : RawDigits) : List ℕ :=
  (r.toMultiset.sort (· ≥ ·)).map fun i ↦ i + 2

/--
Forget the order of a mathlib Fibonacci-index list and shift its indices down by `2`.
For `IsZeckendorfRep` lists, every index is at least `2`, so this is inverse to
`rawToZeckendorf` without truncated-subtraction loss.
-/
noncomputable def rawOfZeckendorf (digits : List ℕ) : RawDigits :=
  Multiset.toFinsupp (digits.map fun k ↦ k - 2)

private theorem coe_rawToZeckendorf (r : RawDigits) :
    (rawToZeckendorf r : Multiset ℕ) =
      r.toMultiset.map (fun i ↦ i + 2) := by
  rw [rawToZeckendorf, ← Multiset.map_coe, Multiset.sort_eq]

private theorem sum_map_nsmul_singleton (f : ℕ → ℕ) (i n : ℕ) :
    (Multiset.map f (n • ({i} : Multiset ℕ))).sum = n * f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih, Nat.succ_mul]

/-- Sorting and shifting raw multiplicities preserves their W-weighted value. -/
theorem rawValue_eq_sum_rawToZeckendorf (r : RawDigits) :
    rawValue r = ((rawToZeckendorf r).map Nat.fib).sum := by
  classical
  rw [← Multiset.sum_coe, ← Multiset.map_coe, coe_rawToZeckendorf]
  induction r using Finsupp.induction with
  | zero => simp [rawValue]
  | single_add i coefficient r _ _ ih =>
      simp only [rawValue_add, rawValue_single, Finsupp.toMultiset_add,
        Finsupp.toMultiset_single, Multiset.map_add, Multiset.sum_add, ih,
        wValue, Multiset.map_map]
      rw [sum_map_nsmul_singleton]
      rfl

/-- Shifting the sorted multiplicity list up and back down recovers every raw string. -/
theorem rawOfZeckendorf_rawToZeckendorf (r : RawDigits) :
    rawOfZeckendorf (rawToZeckendorf r) = r := by
  classical
  have hmultiset :
      ((rawToZeckendorf r).map (fun k ↦ k - 2) : Multiset ℕ) =
        r.toMultiset := by
    rw [← Multiset.map_coe, coe_rawToZeckendorf, Multiset.map_map]
    simp
  apply Finsupp.ext
  intro i
  rw [rawOfZeckendorf, Multiset.toFinsupp_apply, hmultiset,
    Finsupp.count_toMultiset]

private theorem isZeckendorfRep_rawTo_iff (r : RawDigits) :
    (rawToZeckendorf r).IsZeckendorfRep ↔
      (r.toMultiset.sort (· ≥ ·)).Pairwise (fun a b ↦ b + 2 ≤ a) := by
  let digits := r.toMultiset.sort (· ≥ ·)
  let shift := fun i : ℕ ↦ i + 2
  change List.IsChain (fun a b ↦ b + 2 ≤ a) (digits.map shift ++ [0]) ↔
    digits.Pairwise (fun a b ↦ b + 2 ≤ a)
  rw [List.isChain_append]
  constructor
  · rintro ⟨hshifted, _, _⟩
    have hraw : digits.IsChain (fun a b ↦ b + 2 ≤ a) :=
      ((List.isChain_map shift).1 hshifted).imp (by
        intro a b hab
        dsimp [shift] at hab
        omega)
    exact List.isChain_iff_pairwise.1 hraw
  · intro hraw
    have hrawChain := List.isChain_iff_pairwise.2 hraw
    have hshifted :
        (digits.map shift).IsChain (fun a b ↦ b + 2 ≤ a) :=
      (List.isChain_map shift).2 (hrawChain.imp (by
        intro a b hab
        dsimp [shift]
        omega))
    refine ⟨hshifted, List.IsChain.singleton 0, ?_⟩
    intro x hx y hy
    simp only [List.head?_singleton, Option.mem_some_iff] at hy
    subst y
    have hx_mem : x ∈ digits.map shift := List.mem_of_mem_getLast? hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx_mem
    dsimp [shift]
    omega

private theorem canonicalRaw_iff_gap_sorted (r : RawDigits) :
    CanonicalRaw r ↔
      (r.toMultiset.sort (· ≥ ·)).Pairwise (fun a b ↦ b + 2 ≤ a) := by
  classical
  let digits := r.toMultiset.sort (· ≥ ·)
  change CanonicalRaw r ↔ digits.Pairwise (fun a b ↦ b + 2 ≤ a)
  constructor
  · rintro ⟨hbinary, hadjacent⟩
    have hmulti : r.toMultiset.Nodup :=
      Multiset.nodup_iff_count_le_one.2 fun i ↦ by
        simpa using hbinary i
    have hnodup : digits.Nodup := by
      rw [← Multiset.coe_nodup, show (digits : Multiset ℕ) = r.toMultiset by
        simp [digits]]
      exact hmulti
    have horder : digits.Pairwise (· ≥ ·) := by
      exact Multiset.pairwise_sort r.toMultiset (· ≥ ·)
    rw [List.pairwise_iff_get]
    intro p q hpq
    have hge := List.pairwise_iff_get.1 horder p q hpq
    have hne : digits.get p ≠ digits.get q :=
      fun heq ↦ (Fin.ne_of_lt hpq) (hnodup.injective_get heq)
    have hp_mem : digits.get p ∈ r.toMultiset := by
      rw [← show (digits : Multiset ℕ) = r.toMultiset by simp [digits]]
      exact Multiset.mem_coe.mpr (List.get_mem digits p)
    have hq_mem : digits.get q ∈ r.toMultiset := by
      rw [← show (digits : Multiset ℕ) = r.toMultiset by simp [digits]]
      exact Multiset.mem_coe.mpr (List.get_mem digits q)
    have hp_nonzero : r (digits.get p) ≠ 0 := by simpa using hp_mem
    have hq_nonzero : r (digits.get q) ≠ 0 := by simpa using hq_mem
    have hq_le := hbinary (digits.get q)
    have hq_one : r (digits.get q) = 1 := by omega
    have hnot_adjacent : digits.get p ≠ digits.get q + 1 := by
      intro heq
      have := hadjacent (digits.get q) hq_one
      rw [← heq] at this
      exact hp_nonzero this
    omega
  · intro hgap
    have hnodup : digits.Nodup := hgap.imp fun h ↦ by omega
    have hmulti : r.toMultiset.Nodup := by
      rw [← show (digits : Multiset ℕ) = r.toMultiset by simp [digits]]
      exact Multiset.coe_nodup.mpr hnodup
    have hbinary : ∀ i, r i ≤ 1 := fun i ↦ by
      simpa using Multiset.nodup_iff_count_le_one.1 hmulti i
    refine ⟨hbinary, ?_⟩
    intro i hi
    by_contra hnext
    have hnext_le := hbinary (i + 1)
    have hnext_one : r (i + 1) = 1 := by omega
    have hi_mem : i ∈ digits := by
      have hi_nonzero : r i ≠ 0 := by omega
      have : i ∈ r.toMultiset := by simpa using hi_nonzero
      simpa [digits] using this
    have hnext_mem : i + 1 ∈ digits := by
      have hnext_nonzero : r (i + 1) ≠ 0 := by omega
      have : i + 1 ∈ r.toMultiset := by simpa using hnext_nonzero
      simpa [digits] using this
    obtain ⟨p, hp⟩ := List.mem_iff_get.1 hi_mem
    obtain ⟨q, hq⟩ := List.mem_iff_get.1 hnext_mem
    have hpq_ne : p ≠ q := by
      intro hpq
      subst q
      rw [hp] at hq
      omega
    rcases lt_or_gt_of_ne hpq_ne with hpq | hqp
    · have h := List.pairwise_iff_get.1 hgap p q hpq
      rw [hp, hq] at h
      omega
    · have h := List.pairwise_iff_get.1 hgap q p hqp
      rw [hp, hq] at h
      omega

/-- The raw binary/nonadjacent predicate is exactly mathlib Zeckendorf canonicality. -/
theorem canonicalRaw_iff_isZeckendorfRep (r : RawDigits) :
    CanonicalRaw r ↔ (rawToZeckendorf r).IsZeckendorfRep :=
  (canonicalRaw_iff_gap_sorted r).trans (isZeckendorfRep_rawTo_iff r).symm

/-- A valid mathlib Zeckendorf list survives the `-2`/sort/`+2` round trip. -/
theorem rawToZeckendorf_rawOfZeckendorf {digits : List ℕ}
    (canonical : digits.IsZeckendorfRep) :
    rawToZeckendorf (rawOfZeckendorf digits) = digits := by
  classical
  have hall := List.isChain_iff_pairwise.1 canonical
  have hparts := List.pairwise_append.1 hall
  have hpair : digits.Pairwise (fun a b ↦ b + 2 ≤ a) := hparts.1
  have hge : ∀ k ∈ digits, 2 ≤ k := by
    intro k hk
    exact hparts.2.2 k hk 0 (by simp)
  let down := digits.map fun k ↦ k - 2
  have hdownPair : down.Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact hpair.imp_of_mem (by
      intro a b ha hb hab
      have ha2 := hge a ha
      have hb2 := hge b hb
      omega)
  have hsortedPair :
      ((down : Multiset ℕ).sort (· ≥ ·)).Pairwise (· ≥ ·) :=
    Multiset.pairwise_sort (down : Multiset ℕ) (· ≥ ·)
  have hperm : ((down : Multiset ℕ).sort (· ≥ ·)).Perm down :=
    Quotient.exact (Multiset.sort_eq (down : Multiset ℕ) (· ≥ ·))
  have hsort : (down : Multiset ℕ).sort (· ≥ ·) = down :=
    List.Perm.eq_of_pairwise' hsortedPair hdownPair hperm
  rw [rawToZeckendorf, rawOfZeckendorf,
    Multiset.toFinsupp_toMultiset]
  change ((down : Multiset ℕ).sort (· ≥ ·)).map (fun i ↦ i + 2) = digits
  rw [hsort]
  change (digits.map fun k ↦ k - 2).map (fun i ↦ i + 2) = digits
  rw [List.map_map]
  calc
    digits.map ((fun i ↦ i + 2) ∘ fun k ↦ k - 2) = digits.map id := by
      apply List.map_congr_left
      intro k hk
      exact Nat.sub_add_cancel (hge k hk)
    _ = digits := List.map_id digits

/-- Shifting a valid mathlib Zeckendorf list down produces canonical raw W digits. -/
theorem canonicalRaw_rawOfZeckendorf {digits : List ℕ}
    (canonical : digits.IsZeckendorfRep) :
    CanonicalRaw (rawOfZeckendorf digits) := by
  apply (canonicalRaw_iff_isZeckendorfRep _).2
  rw [rawToZeckendorf_rawOfZeckendorf canonical]
  exact canonical

/-- Shifting a valid mathlib Zeckendorf list down preserves its Fibonacci sum. -/
theorem rawValue_rawOfZeckendorf {digits : List ℕ}
    (canonical : digits.IsZeckendorfRep) :
    rawValue (rawOfZeckendorf digits) = (digits.map Nat.fib).sum := by
  rw [rawValue_eq_sum_rawToZeckendorf,
    rawToZeckendorf_rawOfZeckendorf canonical]

/-- A canonical raw string maps to mathlib's unique Zeckendorf representation of its value. -/
theorem rawToZeckendorf_eq_zeckendorf {r : RawDigits} (canonical : CanonicalRaw r) :
    rawToZeckendorf r = Nat.zeckendorf (rawValue r) := by
  symm
  rw [rawValue_eq_sum_rawToZeckendorf]
  exact Nat.zeckendorf_sum_fib ((canonicalRaw_iff_isZeckendorfRep r).1 canonical)

/-- Canonical raw W strings as a machine type. -/
abbrev CanonicalRawDigits := {r : RawDigits // CanonicalRaw r}

/-- The structural `+2` bridge between canonical raw digits and mathlib representations. -/
noncomputable def rawZeckendorfEquiv : CanonicalRawDigits ≃ WDigitString where
  toFun r := ⟨rawToZeckendorf r.1,
    (canonicalRaw_iff_isZeckendorfRep r.1).1 r.2⟩
  invFun digits := ⟨rawOfZeckendorf digits.1,
    canonicalRaw_rawOfZeckendorf digits.2⟩
  left_inv r := Subtype.ext (rawOfZeckendorf_rawToZeckendorf r.1)
  right_inv digits := Subtype.ext
    (rawToZeckendorf_rawOfZeckendorf digits.2)

/-- The structural bridge agrees with `wEncoding := Nat.zeckendorfEquiv` on values. -/
theorem rawZeckendorfEquiv_eq_wEncoding (r : CanonicalRawDigits) :
    rawZeckendorfEquiv r = wEncoding (rawValue r.1) := by
  apply Subtype.ext
  exact rawToZeckendorf_eq_zeckendorf r.2

end D5.S1.Digit
