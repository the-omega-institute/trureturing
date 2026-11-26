/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/CertificateState
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Soundness of ordered tables and their grouped fixed-point prefix checks. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core
import Mathlib.Tactic

/-! Ordered-table and transition checks retain their mathematical meaning under concatenation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- The increasing-list check is exactly strict order with the stated lower endpoint. -/
theorem increasingFrom_sound {prev : ℕ} {xs : List ℕ} :
    increasingFrom prev xs = true ↔
      xs.Pairwise (· < ·) ∧ ∀ x ∈ xs, prev < x := by
  induction xs generalizing prev with
  | nil => simp [increasingFrom]
  | cons x xs ih =>
    change ((decide (prev < x) && increasingFrom x xs) = true) ↔ _
    rw [Bool.and_eq_true, decide_eq_true_eq, ih]
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hpx, hp, hm⟩
      exact ⟨⟨hm, hp⟩, hpx, fun y hy => hpx.trans (hm y hy)⟩
    · rintro ⟨⟨hm, hp⟩, hpx, _⟩
      exact ⟨hpx, hp, hm⟩

/-- A successful nonempty run exposes the checked group state before its first entry. -/
theorem stepTable_head {ts : List (ℕ × ℕ × ℕ)} {e : ℕ} {es : List ℕ}
    {st st' : List (ℕ × ℕ)} :
    stepTable ts (e :: es) st = some st' ↔
    ∃ p j L t, oddPrimes[entryLabel e]? = some p ∧
      st[entryLabel e]? = some (j, L) ∧ ts[entryLabel e]? = some t ∧
      prefixOk p j L t = true ∧
      stepTable ts es (st.set (entryLabel e)
        (j + 1, L * (entryValue e - 1) / entryValue e)) = some st' := by
  constructor
  · intro h
    cases hp : oddPrimes[entryLabel e]? with
    | none => simp [stepTable, hp] at h
    | some p =>
      cases hs : st[entryLabel e]? with
      | none => simp [stepTable, hp, hs] at h
      | some s =>
        obtain ⟨j, L⟩ := s
        cases ht : ts[entryLabel e]? with
        | none => simp [stepTable, hp, hs, ht] at h
        | some t =>
          have hh : (if prefixOk p j L t then
              stepTable ts es (st.set (entryLabel e)
                (j + 1, L * (entryValue e - 1) / entryValue e)) else none) = some st' := by
            simpa only [stepTable, hp, hs, ht] using h
          split at hh
          · rename_i hc
            exact ⟨p, j, L, t, rfl, rfl, rfl, hc, hh⟩
          · simp at hh
  · rintro ⟨p, j, L, t, hp, hs, ht, hc, hr⟩
    simpa only [stepTable, hp, hs, ht, if_pos hc] using hr

/-- Processing two table chunks is the composition of their successful transitions. -/
theorem stepTable_append (ts : List (ℕ × ℕ × ℕ)) (as bs : List ℕ)
    (st : List (ℕ × ℕ)) :
    stepTable ts (as ++ bs) st = (stepTable ts as st).bind (stepTable ts bs) := by
  induction as generalizing st with
  | nil => rfl
  | cons e es ih =>
    cases hp : oddPrimes[entryLabel e]? with
    | none => simp [stepTable, hp]
    | some p =>
      cases hs : st[entryLabel e]? with
      | none => simp [stepTable, hp, hs]
      | some s =>
        obtain ⟨j, L⟩ := s
        cases ht : ts[entryLabel e]? with
        | none => simp [stepTable, hp, hs, ht]
        | some t =>
          by_cases hc : prefixOk p j L t = true
          · simpa only [List.cons_append, stepTable, hp, hs, ht, if_pos hc] using
              ih (st.set (entryLabel e)
                (j + 1, L * (entryValue e - 1) / entryValue e))
          · simp [stepTable, hp, hs, ht, hc]

/-- The final check is exactly the checks at indices present in all three lists. -/
theorem finalOk_sound {ts : List (ℕ × ℕ × ℕ)} {st : List (ℕ × ℕ)} :
    finalOk ts st = true ↔
      ∀ (i p j L : ℕ) (t : ℕ × ℕ × ℕ), oddPrimes[i]? = some p →
        st[i]? = some (j, L) → ts[i]? = some t → prefixOk p j L t = true := by
  constructor
  · intro hf i p j L t hp hs ht
    have hzip : (st.zip ts)[i]? = some ((j, L), t) :=
      List.getElem?_zip_eq_some.mpr ⟨hs, ht⟩
    have hall : (oddPrimes.zip (st.zip ts))[i]? = some (p, (j, L), t) :=
      List.getElem?_zip_eq_some.mpr ⟨hp, hzip⟩
    simp only [finalOk, List.all_eq_true] at hf
    exact hf (p, ((j, L), t)) (List.mem_of_getElem? hall)
  · intro h
    simp only [finalOk, List.all_eq_true]
    rintro ⟨p, ⟨j, L⟩, t⟩ hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨hp, hz⟩ := List.getElem?_zip_eq_some.mp hi
    obtain ⟨hs, ht⟩ := List.getElem?_zip_eq_some.mp hz
    exact h i p j L t hp hs ht

/-- Concatenation carries the lower endpoint forward to the last entry of the first chunk. -/
theorem increasingFrom_append (prev : ℕ) (as bs : List ℕ) :
    increasingFrom prev (as ++ bs) =
      (increasingFrom prev as && increasingFrom (as.getLastD prev) bs) := by
  induction as generalizing prev with
  | nil => simp [increasingFrom]
  | cons a as ih =>
    change (decide (prev < a) && increasingFrom a (as ++ bs)) = _
    rw [ih]
    simp only [increasingFrom, List.getLastD_eq_getLast?, List.getLast?_cons]
    cases as <;> simp_all [Bool.and_assoc, increasingFrom]

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
