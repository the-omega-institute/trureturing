/- GID: D5/S0/Certificates/TripodNimPeriodRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/TripodNimPeriodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/TripodNimPeriodRefutation.claim; result=D5/S0/Certificates/TripodNimPeriodRefutation.result; claim=D5/S0/Certificates/TripodNimPeriodRefutation.claim
   digest: Refutes only printed Conjecture 2 of Tree and Tripod Nim, arXiv:2401.07943v1, using the section 9.3 transition at n=10. Literature-attested source; no priority claim.
   proof_shape: content
   escape_witness: Boolean-row semantics, bit-vector evaluator correctness, and a checked 264-step orbit with three proper-divisor nonreturns.
   admission_basis: escape-witness -/

import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.TripodNimPeriodRefutation

/-!
Hennessey, section 9.3, printed page 28: k rows of 2n+k bits; shift left,
append zeros, then insert into rows harvesting zero, bottom to top. Insertions
exclude the first n columns and columns used by earlier insertions in this step,
and select the leftmost remaining zero. Page 30 prints the divisor 2(4n)(4n+1)
and reports verification for n ≤ 9. Here k=3; list order is bottom to top and
column zero is leftmost. Shifting each row just before processing it commutes
with shifting the other rows, since only newly inserted column indices are shared.

Failure to find a permitted zero is explicit and absorbing. A periodic orbit
through a present board therefore consists entirely of defined paper transitions.
No arbitrary fallback move is added. The claim concerns every three-row periodic
board, with no initial-state reachability restriction. It asserts only the
printed Conjecture 2, and says nothing about the rest of the paper, any intended
statement, or a modified period formula. The 109-step initial segment is unused.
-/

/-- A column of the three-row system D(3,n), numbered from the left. -/
abbrev Column (n : ℕ) := Fin (2 * n + 3)

/-- A literal Boolean row. -/
abbrev Row (n : ℕ) := Column n → Bool

/-- Rows are listed from bottom to top; the claim requires exactly three. -/
abbrev Board (n : ℕ) := List (Row n)

private def shiftRow {n : ℕ} (r : Row n) : Row n :=
  fun c => if h : c.val + 1 < 2 * n + 3 then r ⟨c.val + 1, h⟩ else false

private def insertRow {n : ℕ} (r : Row n) (c : Column n) : Row n :=
  Function.update r c true

/-- First eligible column in the shifted row, in increasing left-to-right order. -/
private def firstZero {n : ℕ} (r : Row n) (used : List (Column n)) : Option (Column n) :=
  (List.finRange (2 * n + 3)).find? fun c =>
    decide (n ≤ c.val) && !r c && !used.contains c

private def runRows {n : ℕ} {α : Type} (read : α → Row n)
    (shift : α → α) (insert : α → Column n → α) :
    List α → List (Column n) → Option (List α)
  | [], _ => some []
  | r :: rs, used =>
    let shifted := shift r
    if read r ⟨0, by omega⟩ then
      (runRows read shift insert rs used).map (shifted :: ·)
    else
      match firstZero (read shifted) used with
      | none => none
      | some c =>
        (runRows read shift insert rs (c :: used)).map (insert shifted c :: ·)

/-- Exactly the section 9.3 transition, with an absorbing undefined state. -/
def transition (n : ℕ) (s : Option (Board n)) : Option (Board n) :=
  s.bind fun rows => runRows id shiftRow insertRow rows []

private abbrev PackedRow (n : ℕ) := BitVec (2 * n + 3)

private def readBits {n : ℕ} (r : PackedRow n) : Row n :=
  fun c => r.getLsbD c.val

private def insertBit {n : ℕ} (r : PackedRow n) (c : Column n) : PackedRow n :=
  r ||| ((1 : PackedRow n) <<< c.val)

private def packedTransition (n : ℕ) (s : Option (List (PackedRow n))) :=
  s.bind fun rows => runRows readBits (· >>> 1) insertBit rows []

private def decode {n : ℕ} (s : Option (List (PackedRow n))) : Option (Board n) :=
  s.map (List.map readBits)

private theorem read_shift {n : ℕ} (r : PackedRow n) :
    readBits (r >>> 1) = shiftRow (readBits r) := by
  funext c
  simp only [readBits, shiftRow, BitVec.getLsbD_ushiftRight]
  split_ifs with h
  · congr 1 <;> omega
  · exact BitVec.getLsbD_of_ge r _ (by omega)

private theorem read_insert {n : ℕ} (r : PackedRow n) (c : Column n) :
    readBits (insertBit r c) = insertRow (readBits r) c := by
  funext j
  by_cases h : j = c
  · subst j
    simp [readBits, insertBit, insertRow, c.isLt]
  · have hval : j.val ≠ c.val := fun he => h (Fin.ext he)
    simp [readBits, insertBit, insertRow, j.isLt, h]
    omega

private theorem runRows_correct {n : ℕ} (rs : List (PackedRow n))
    (used : List (Column n)) :
    (runRows readBits (· >>> 1) insertBit rs used).map (List.map readBits) =
      runRows id shiftRow insertRow (rs.map readBits) used := by
  induction rs generalizing used with
  | nil => rfl
  | cons r rs ih =>
    simp only [runRows, List.map_cons, id_eq, read_shift]
    split
    · simp only [Option.map_map, Function.comp_def, List.map_cons, read_shift]
      rw [← ih]
      simp [Option.map_map, Function.comp_def]
    · cases hc : firstZero (shiftRow (readBits r)) used with
      | none => rfl
      | some c =>
        simp only [Option.map_map, Function.comp_def, List.map_cons, read_insert, read_shift]
        rw [← ih]
        simp [Option.map_map, Function.comp_def]

/-- The Boolean semantics and the word evaluator commute with decoding at every step. -/
private theorem evaluator_correct (n : ℕ) :
    Function.Semiconj (@decode n) (packedTransition n) (transition n) := by
  intro s
  cases s with
  | none => rfl
  | some rs => exact runRows_correct rs []

private theorem readBits_injective (n : ℕ) : Function.Injective (@readBits n) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun h ⟨i, hi⟩

private theorem decode_injective (n : ℕ) : Function.Injective (@decode n) := by
  exact Option.map_injective (List.map_injective_iff.mpr (readBits_injective n))

/-- The printed assertion for every periodic three-row board, with its actual transition. -/
def claim : Prop :=
  ∀ (n : ℕ) (s : Board n), s.length = 3 →
    some s ∈ Function.periodicPts (transition n) →
    Function.minimalPeriod (transition n) (some s) ∣ 2 * (4 * n) * (4 * n + 1)

set_option maxHeartbeats 4000000 in
-- Covers the four finite orbit evaluations and the divisor certificate.
/-- At n=10 the explicitly evaluated paper transition has a period-264 orbit. -/
theorem result : ¬ claim := by
  let seed : Option (List (PackedRow 10)) := some [1, 2047, 2042]
  have cycle : Function.IsPeriodicPt (packedTransition 10) 264 seed := by
    decide +kernel
  have away24 : ¬ Function.IsPeriodicPt (packedTransition 10) 24 seed := by
    decide +kernel
  have away88 : ¬ Function.IsPeriodicPt (packedTransition 10) 88 seed := by
    decide +kernel
  have away132 : ¬ Function.IsPeriodicPt (packedTransition 10) 132 seed := by
    decide +kernel
  have semantic_cycle := cycle.map (evaluator_correct 10)
  have reflects (k : ℕ) (hk : Function.IsPeriodicPt (transition 10) k (decode seed)) :
      Function.IsPeriodicPt (packedTransition 10) k seed := by
    apply decode_injective 10
    rw [(evaluator_correct 10).iterate_right k]
    exact hk
  let d := Function.minimalPeriod (transition 10) (decode seed)
  have hd : d ∣ 264 := semantic_cycle.minimalPeriod_dvd
  have hpos : 0 < d := semantic_cycle.minimalPeriod_pos (by decide)
  have hle : d ≤ 264 := Nat.le_of_dvd (by decide) hd
  have proper (m : Fin 265) :
      m.val ∣ 264 → m.val = 264 ∨ m.val ∣ 132 ∨ m.val ∣ 88 ∨ m.val ∣ 24 := by
    revert m
    decide +kernel
  have exact_period : d = 264 := by
    rcases proper ⟨d, by omega⟩ hd with he | he | he | he
    · exact he
    · exact False.elim (away132 (reflects 132
        (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr he)))
    · exact False.elim (away88 (reflects 88
        (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr he)))
    · exact False.elim (away24 (reflects 24
        (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr he)))
  intro h
  have required := h 10 ([1, 2047, 2042].map (@readBits 10)) rfl
    (Function.mk_mem_periodicPts (by decide : 0 < 264) semantic_cycle)
  change d ∣ 3280 at required
  rw [exact_period] at required
  norm_num at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.TripodNimPeriodRefutation
