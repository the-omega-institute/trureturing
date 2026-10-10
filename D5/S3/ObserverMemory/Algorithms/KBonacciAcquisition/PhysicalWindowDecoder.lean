/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Donor-compensated literal rows and final-only original INITIAL decoding. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse WindowSeamCodes OriginalNarrowCost OriginalAcquiredTrace
open scoped BigOperators
universe u

variable {m d : ℕ} {Y : Type u} [DecidableEq Y]

/-- Scalar coordinate of the selected code at a particular ordered vertex. -/
def vertexBit (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (i : Fin d) (v : Fin (m + 1)) : ZMod 2 := if i ∈ c (tableLabel table v) then 1 else 0

/-- Compensation sums vertices, so repeated labels contribute repeatedly. -/
def physicalCharge (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (i : Fin d) (x : ZMod (m + 2)) : ZMod 2 :=
  if h : x.val < m + 1 then vertexBit table c i ⟨x.val, h⟩
  else ∑ v : Fin (m + 1), vertexBit table c i v

/-- The actual relative row at issued index i+1, after rotating out the prior archive. -/
def actualRow (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (i : Fin d) (h : ℕ) : ZMod 2 :=
  physicalCharge table c i ((((i.val + 1) * m : ℕ) : ZMod (m + 2)) + (h : ℕ))

private theorem charge_at (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (i : Fin d) (v : Fin (m + 1)) :
    physicalCharge table c i (v.val : ZMod (m + 2)) = vertexBit table c i v := by
  simp only [physicalCharge, ZMod.val_natCast_of_lt (n := m + 2) (a := v.val) (by have := v.isLt; omega),
    dif_pos v.isLt]

private def phaseEquiv (m : ℕ) : Fin (m + 2) ≃ ZMod (m + 2) where
  toFun x := (x.val : ZMod (m + 2))
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv x := Fin.ext (ZMod.val_natCast_of_lt x.isLt)
  right_inv x := ZMod.natCast_zmod_val x

private theorem charge_even (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (i : Fin d) : (∑ x : ZMod (m + 2), physicalCharge table c i x) = 0 := by
  let e := phaseEquiv m
  rw [← e.sum_comp]
  have applyE (x : Fin (m + 2)) : e x = (x.val : ZMod (m + 2)) :=
    rfl
  simp only [applyE]
  rw [Fin.sum_univ_castSucc]
  have last : physicalCharge table c i ((m + 1 : ℕ) : ZMod (m + 2)) =
      ∑ v : Fin (m + 1), vertexBit table c i v := by
    unfold physicalCharge
    rw [ZMod.val_natCast_of_lt (n := m + 2) (a := m + 1) (by omega), dif_neg (by omega)]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [last]
  have first : (∑ x : Fin (m + 1), physicalCharge table c i (x.val : ZMod (m + 2))) =
      ∑ x : Fin (m + 1), vertexBit table c i x := by
    apply Finset.sum_congr rfl
    intro x _
    exact charge_at table c i x
  rw [first, CharTwo.add_self_eq_zero]

private theorem row_outside (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d) : actualRow table c i (m + 1) = 0 := by
  have geometry := source_window_vertices m d fit i
  have edge : (((i.val + 1) * m : ℕ) : ZMod (m + 2)) + (m + 1 : ℕ) =
      ((missedVertex m d fit i).val : ZMod (m + 2)) := by
    have h : ((m + 2 : ℕ) : ZMod (m + 2)) = 0 := by simp
    have h' : (missedVertex m d fit i).val + 1 = (seamVertex m d fit i).val := by
      simp only [missedVertex, seamVertex]; have := i.isLt; omega
    have cast := congrArg (fun n : ℕ => (n : ZMod (m + 2))) h'
    rw [geometry.2.2.1]
    push_cast at cast h ⊢
    linear_combination h - cast
  rw [actualRow, edge, charge_at]
  exact if_neg (unary i)

/-- Even donor rows, unavailable zero, and the exact native literal inverse.
The compensation is the sum over all ordered vertices, with multiplicity. -/
theorem donor_rows_inverse (m d : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d) :
    actualRow table c i (m + 1) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), actualRow table c i h) = 0 ∧
    (∀ j : ZMod (m + 2), wordIncrement (m + 1) (-j) (prefixWord m (actualRow table c i)) =
      windowCharge (m + 1) m (actualRow table c i) j) ∧
    (prefixWord m (actualRow table c i) ⟨0, by omega⟩ = false ↔ actualRow table c i 0 = 0) ∧
    (prefixWord m (actualRow table c i) ⟨m - 1, by omega⟩ = false ↔ actualRow table c i m = 0) := by
  have outside := row_outside table fit c unary i
  have sumAll : (∑ h ∈ Finset.range (m + 2), actualRow table c i h) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    let e := phaseEquiv m
    let shift := Equiv.addLeft ((((i.val + 1) * m : ℕ) : ZMod (m + 2)))
    have eq := (e.trans shift).sum_comp (physicalCharge table c i)
    have applyE (x : Fin (m + 2)) : e x = (x.val : ZMod (m + 2)) :=
      rfl
    have shiftApply (x : ZMod (m + 2)) : shift x = (((i.val + 1) * m : ℕ) : ZMod (m + 2)) + x := rfl
    simpa only [Equiv.trans_apply, applyE, actualRow, shiftApply] using
      eq.trans (charge_even table c i)
  have even : (∑ h ∈ Finset.range (m + 1), actualRow table c i h) = 0 := by
    rw [Finset.sum_range_succ, outside, add_zero] at sumAll
    exact sumAll
  have inverse := short_window_charge_inverse (m + 1) (by omega) m (by omega)
    (by omega) (actualRow table c i) even
  exact ⟨outside, even, inverse.1, inverse.2.1, inverse.2.2.1⟩


private theorem row_native (m d : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d) (x : ZMod (m + 2)) :
    wordIncrement (m + 1) (-(x - (((i.val + 1) * m : ℕ) : ZMod (m + 2))))
      (prefixWord m (actualRow table c i)) = physicalCharge table c i x := by
  rw [(donor_rows_inverse m d hm table fit c unary i).2.2.1]
  unfold windowCharge
  split_ifs with inside
  · simp only [actualRow, ZMod.natCast_zmod_val]
    congr 1
    ring
  · have bound := ZMod.val_lt (x - (((i.val + 1) * m : ℕ) : ZMod (m + 2)))
    have valEq : (x - (((i.val + 1) * m : ℕ) : ZMod (m + 2))).val = m + 1 := by omega
    have eq := ZMod.natCast_zmod_val (x - (((i.val + 1) * m : ℕ) : ZMod (m + 2)))
    rw [valEq] at eq
    have xx : x = (((i.val + 1) * m : ℕ) : ZMod (m + 2)) + (m + 1 : ℕ) := by
      linear_combination -eq
    rw [xx]
    exact (row_outside table fit c unary i).symm

private theorem row_head (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (i : Fin d) :
    actualRow table c i 0 = vertexBit table c i (seamVertex m d fit i) := by
  rw [actualRow, Nat.cast_zero, add_zero,
    (source_window_vertices m d fit i).2.2.1, charge_at]

private theorem row_seam (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (i : Fin d) (hi : 0 < i.val) :
    actualRow table c (prev i) m = vertexBit table c (prev i) (seamVertex m d fit i) := by
  have castEq : (((((prev i).val + 1) * m : ℕ) : ZMod (m + 2)) + (m : ℕ)) =
      ((seamVertex m d fit i).val : ZMod (m + 2)) := by
    have natEq : ((prev i).val + 1) * m + m = i.val * m + m := by
      simp only [prev]
      rw [show i.val - 1 + 1 = i.val by omega]
    rw [← Nat.cast_add, natEq]
    exact (source_window_vertices m d fit i).2.2.2
  rw [actualRow, castEq, charge_at]

private theorem safe_rows_of_adjacent (m : ℕ) (rows : List (ℕ → ZMod 2))
    (even : ∀ q ∈ rows, (∑ h ∈ Finset.range (m + 1), q h) = 0)
    (adjacent : ∀ (i : ℕ) (hi : i + 1 < rows.length),
      rows[i] m = 0 ∨ rows[i + 1] 0 = 0) : safeRows m rows := by
  induction rows with
  | nil => trivial
  | cons q rows ih =>
    refine ⟨even q (by simp), ?_, ih ?_ ?_⟩
    · cases rows with
      | nil => simp
      | cons r rest =>
        intro s hs
        have eq : r = s := by simpa using hs
        subst s
        exact adjacent 0 (by simp)
    · intro r hr; exact even r (by simp [hr])
    · intro i hi
      exact adjacent (i + 1) (by simpa using hi)

/-- All ordered rows, with exactly one row per code coordinate. -/
def actualRows (table : Fin (m + 1) → Y) (c : Label table → Word d) :
    List (ℕ → ZMod 2) := List.ofFn (actualRow table c)

/-- The regular Selection itself supplies all seam zeros; no safety premise
is added to the original table. -/
theorem regular_rows_safe (m d : ℕ) (hm : 3 ≤ m) (hd : 2 ≤ d)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d)
    (regular : ∀ L, c L ∈ codeList (sourceClauses table d fit) (by omega) L) :
    actualRow table c (first (by omega)) 0 = 0 ∧ safeRows m (actualRows table c) := by
  have unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i) := fun i =>
    ((mem_codeList_iff _ _ _ _).mp (regular _)).1 i rfl
  have extra := ((mem_codeList_iff _ _ _ _).mp (regular (sourceClauses table d fit).extra)).2.1 rfl
  have head : actualRow table c (first (by omega)) 0 = 0 := by
    rw [row_head table fit]
    have seam : seamVertex m d fit (first (by omega)) = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp only [seamVertex, first]
      omega
    rw [seam]
    exact if_neg extra
  refine ⟨head, safe_rows_of_adjacent m _ ?_ ?_⟩
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact (donor_rows_inverse m d hm table fit c unary i).2.1
  · intro n hn
    have nd : n + 1 < d := by simpa [actualRows] using hn
    let i : Fin d := ⟨n + 1, nd⟩
    have prevEq : prev i = ⟨n, by omega⟩ := by apply Fin.ext; simp [i, prev]
    have pair := ((mem_codeList_iff _ _ _ _).mp
      (regular ((sourceClauses table d fit).pair i))).2.2 i (by simp [i]) rfl
    simp only [actualRows]
    have validN : n < (List.ofFn (actualRow table c)).length := by simp; omega
    have validNext : n + 1 < (List.ofFn (actualRow table c)).length := by simp; omega
    have getN : (List.ofFn (actualRow table c))[n]'validN = actualRow table c ⟨n, by omega⟩ :=
      List.getElem_ofFn (by simp; omega)
    have getNext : (List.ofFn (actualRow table c))[n + 1]'validNext = actualRow table c ⟨n + 1, nd⟩ :=
      List.getElem_ofFn (by simp; omega)
    have seamZero : actualRow table c (prev i) m = 0 ∨ actualRow table c i 0 = 0 := by
      rw [row_seam table fit c i (by simp [i]), row_head table fit]
      rcases pair with current | previous
      · right; exact if_neg current
      · left; exact if_neg previous
    rcases seamZero with lastZero | firstZero
    · left
      exact (congrArg (fun q => q m) getN).trans (by simpa only [prevEq] using lastZero)
    · right
      exact (congrArg (fun q => q 0) getNext).trans firstZero

/-- Every selected source vertex has its prescribed code increment at the
actual issued phase. This statement retains the prior archive rotation a. -/
theorem issued_phase_code (m d a : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d) (v : Fin (m + 1)) :
    wordIncrement (m + 1)
      (-(((a * m : ℕ) : ZMod (m + 2)) + (v.val : ℕ)) +
        (((a + i.val + 1) * m : ℕ) : ZMod (m + 2)))
      (prefixWord m (actualRow table c i)) = vertexBit table c i v := by
  have phase : -(((a * m : ℕ) : ZMod (m + 2)) + (v.val : ℕ)) +
      (((a + i.val + 1) * m : ℕ) : ZMod (m + 2)) =
      -((v.val : ZMod (m + 2)) - (((i.val + 1) * m : ℕ) : ZMod (m + 2))) := by
    push_cast
    ring
  rw [phase, row_native m d hm table fit c unary, charge_at]


private theorem row_index (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (i : Fin d) (h b : ℕ) (v : Fin (m + 1))
    (eq : (seamVertex m d fit i).val + h = v.val + b * (m + 2)) :
    actualRow table c i h = vertexBit table c i v := by
  have castEq := congrArg (fun n : ℕ => (n : ZMod (m + 2))) eq
  have phase : ((seamVertex m d fit i).val : ZMod (m + 2)) + (h : ℕ) = (v.val : ℕ) := by
    have period : (m : ZMod (m + 2)) + 2 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using (ZMod.natCast_self (m + 2))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, period, mul_zero, add_zero] using castEq
  rw [actualRow, (source_window_vertices m d fit i).2.2.1, phase, charge_at]

/-- The exact four-label words force first-head zero, terminal charges 11,
and second charges 101. This includes m=3 and arbitrary other repeated labels. -/
theorem exceptional_row_coordinates (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 4 ≤ m + 1)
    (c : Label table → Word 2)
    (codes : ∀ i : Fin 4, c (fourOwners (sourceClauses table 2 fit) i) = fourWords i) :
    actualRow table c 0 0 = 0 ∧ actualRow table c 0 m = 1 ∧
    actualRow table c 0 (m - 1) = 1 ∧
    actualRow table c 1 0 = 1 ∧ actualRow table c 1 1 = 0 ∧ actualRow table c 1 2 = 1 := by
  have A := codes 0
  have B := codes 1
  have C := codes 2
  have D := codes 3
  change c (tableLabel table (missedVertex m 2 fit 0)) = ∅ at A
  change c (tableLabel table ⟨m, by omega⟩) = {1} at B
  change c (tableLabel table (missedVertex m 2 fit 1)) = {0} at C
  change c (tableLabel table (seamVertex m 2 fit 1)) = {0, 1} at D
  have h0 := row_index table fit c 0 0 0 ⟨m, by omega⟩ (by simp [seamVertex] <;> omega)
  have hlast := row_index table fit c 0 m 1 (seamVertex m 2 fit 1)
    (by simp [seamVertex] <;> omega)
  have hpen := row_index table fit c 0 (m - 1) 1 (missedVertex m 2 fit 1)
    (by simp [seamVertex, missedVertex] <;> omega)
  have h10 := row_index table fit c 1 0 0 (seamVertex m 2 fit 1) (by omega)
  have h11 := row_index table fit c 1 1 0 (missedVertex m 2 fit 0)
    (by simp [seamVertex, missedVertex] <;> omega)
  have h12 := row_index table fit c 1 2 0 ⟨m, by omega⟩ (by simp [seamVertex] <;> omega)
  simpa [vertexBit, A, B, C, D] using And.intro h0
    (And.intro hlast (And.intro hpen (And.intro h10 (And.intro h11 h12))))

private theorem terminal01_tail : ∀ (n : ℕ) (word : Fin (n + 2) → Bool) (s : ℕ),
    word ⟨n, by omega⟩ = false → word ⟨n + 1, by omega⟩ = true → tailAfter s word = 1 := by
  intro n
  induction n with
  | zero =>
    intro word s h0 h1
    change word 0 = false at h0
    change word 1 = true at h1
    simp [tailAfter, Fin.tail, h0, h1]
  | succ n ih =>
    intro word s h0 h1
    simp only [tailAfter]
    apply ih
    · simpa only [Fin.tail, Fin.succ_mk] using h0
    · simpa only [Fin.tail, Fin.succ_mk, Nat.add_assoc] using h1

private theorem prefix110_cut (m : ℕ) (hm : 3 ≤ m) (word : Fin m → Bool)
    (h0 : word ⟨0, by omega⟩ = true) (h1 : word ⟨1, by omega⟩ = true)
    (h2 : word ⟨2, by omega⟩ = false) :
    ∃ rest, List.ofFn word = List.replicate 2 true ++ false :: rest := by
  obtain ⟨n, eq⟩ := Nat.exists_eq_add_of_le hm
  have eq' : m = n + 3 := by omega
  clear eq
  subst m
  change word 0 = true at h0
  change word (Fin.succ 0) = true at h1
  change word (Fin.succ (Fin.succ 0)) = false at h2
  refine ⟨List.ofFn (Fin.tail (Fin.tail (Fin.tail word))), ?_⟩
  simp only [List.ofFn_succ, Fin.tail, Fin.succ_mk, Fin.val_zero]
  simp only [h0, h1, h2, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
  rfl

/-- The exceptional seam uses the actual terminal tail one and the next
literal issuedPrefix 110. Its crossing run is three, strictly below m+1 even at m=3. -/
theorem exceptional_literal_execution (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 4 ≤ m + 1)
    (c : Label table → Word 2)
    (unary : ∀ i, i ∉ c ((sourceClauses table 2 fit).unary i))
    (codes : ∀ i : Fin 4, c (fourOwners (sourceClauses table 2 fit) i) = fourWords i)
    (v : ZMod 2) (phase : ZMod (m + 2)) (s : ℕ) (hs : s < m + 1) :
    let w₀ := prefixWord m (actualRow table c 0)
    let w₁ := prefixWord m (actualRow table c 1)
    w₀ ⟨0, by omega⟩ = false ∧ w₀ ⟨m - 2, by omega⟩ = false ∧
    w₀ ⟨m - 1, by omega⟩ = true ∧ tailAfter s w₀ = 1 ∧
    w₁ ⟨0, by omega⟩ = true ∧ w₁ ⟨1, by omega⟩ = true ∧
    w₁ ⟨2, by omega⟩ = false ∧ 1 + 2 < m + 1 ∧
    runBits (m + 1) w₀ (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement (m + 1) phase w₀, phase + (m : ℕ), 1⟩ ∧
    runBits (m + 1) w₁
      (some ⟨v + wordIncrement (m + 1) phase w₀, phase + (m : ℕ), 1⟩) =
      some ⟨v + wordIncrement (m + 1) phase w₀ +
        wordIncrement (m + 1) (phase + (m : ℕ)) w₁,
        phase + (m : ℕ) + (m : ℕ), tailAfter 0 w₁⟩ := by
  intro w₀ w₁
  obtain ⟨q00, q0m, q0pen, q10, q11, q12⟩ := exceptional_row_coordinates m hm table fit c codes
  have inv0 := donor_rows_inverse m 2 hm table fit c unary 0
  have inv1 := donor_rows_inverse m 2 hm table fit c unary 1
  have first : w₀ ⟨0, by omega⟩ = false := inv0.2.2.2.1.mpr q00
  have last : w₀ ⟨m - 1, by omega⟩ = true := by
    have ne : w₀ ⟨m - 1, by omega⟩ ≠ false := by
      intro hf
      have h := inv0.2.2.2.2.mp hf
      rw [q0m] at h
      exact one_ne_zero h
    exact Bool.eq_true_of_not_eq_false ne
  have pen : w₀ ⟨m - 2, by omega⟩ = false := by
    have e := inv0.2.1
    have mm : m + 1 = ((m - 1) + 1) + 1 := by omega
    rw [mm, Finset.sum_range_succ, Finset.sum_range_succ] at e
    have sum0 : (∑ h ∈ Finset.range (m - 1), actualRow table c 0 h) = 0 := by
      have eqm : m - 1 + 1 = m := by omega
      rw [eqm, q0m, q0pen] at e
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at e
      exact e
    change decide ((∑ h ∈ Finset.range (m - 2 + 1), actualRow table c 0 h) ≠ 0) = false
    rw [show m - 2 + 1 = m - 1 by omega, sum0]
    rfl
  have tails : ∀ t, tailAfter t w₀ = 1 := by
    intro t
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
    have hn' : m = n + 2 := by omega
    clear hn
    subst m
    apply terminal01_tail n w₀ t
    · simpa using pen
    · simpa using last
  have prefix0 : w₁ ⟨0, by omega⟩ = true := by simp [w₁, prefixWord, q10]
  have prefix1 : w₁ ⟨1, by omega⟩ = true := by
    simp [w₁, prefixWord, Finset.sum_range_succ, q10, q11]
  have prefix2 : w₁ ⟨2, by omega⟩ = false := by
    simp [w₁, prefixWord, Finset.sum_range_succ, q10, q11, q12, CharTwo.add_self_eq_zero]
  have step0 := short_safe_execution (m + 1) (by omega) m (by omega) (by omega)
    w₀ v phase s hs (Or.inr first)
  rw [tails 0] at step0
  obtain ⟨rest, cut⟩ := prefix110_cut m hm w₁ prefix0 prefix1 prefix2
  have step1 := first_zero_block_exact (m + 1) (by omega) m 2 w₁ rest cut
    (short_legal (m + 1) m (by omega) (by omega) w₁)
    (v + wordIncrement (m + 1) phase w₀) (phase + (m : ℕ)) 1 (by omega)
  rw [if_pos (show 1 + 2 < m + 1 by omega)] at step1
  exact ⟨first, pen, last, tails s, prefix0, prefix1, prefix2, by omega, step0.1, step1⟩


/-- All actual replies of a fixed complete-word script, paired with their
issued words. The recursion never stops at a homogeneous intermediate reply. -/
def scriptArchive {k m : ℕ} : List (Fin m → Bool) → Option (LiveRecord k) →
    NarrowWindowCost.Archive m
  | [], _ => []
  | B :: rest, q =>
    let next := runBits k B q
    (B, endpointReading next) :: scriptArchive rest next

/-- An archive-only selector. The paid index is its own archive length;
only after all prescribed words does it call the endpoint decoder. -/
def finalSelector {m : ℕ} {Y : Type u} (start : ℕ) (words : List (Fin m → Bool))
    (decode : NarrowWindowCost.Archive m → Y) : NarrowWindowCost.Selector m Y :=
  fun _ archive => match words[archive.length - start]? with
    | some B => .inr B
    | none => .inl (decode (archive.drop start))

private theorem script_length {k m : ℕ} (words : List (Fin m → Bool))
    (q : Option (LiveRecord k)) : (scriptArchive words q).length = words.length := by
  induction words generalizing q with
  | nil => rfl
  | cons B rest ih => simp only [scriptArchive, List.length_cons, ih]

private theorem prescribed_paid_trace {k m : ℕ} {Y : Type u}
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (base issuedPrefix : NarrowWindowCost.Archive m) (rest : List (Fin m → Bool))
    (decomposition : words = issuedPrefix.map Prod.fst ++ rest)
    (q : Option (LiveRecord k)) (free : Option (ZMod 2)) :
    PaidTrace (finalSelector base.length words decode) free q (base ++ issuedPrefix)
      (scriptArchive rest q) (decode (issuedPrefix ++ scriptArchive rest q)) := by
  induction rest generalizing q issuedPrefix with
  | nil =>
    simp only [scriptArchive, List.append_nil, PaidTrace]
    simp [finalSelector, List.length_append, decomposition]
  | cons B rest ih =>
    have action : finalSelector base.length words decode free (base ++ issuedPrefix) = .inr B := by
      simp [finalSelector, List.length_append, decomposition]
    refine ⟨action, rfl, ?_⟩
    let reply := endpointReading (runBits k B q)
    have decomp : words = (issuedPrefix ++ [(B, reply)]).map Prod.fst ++ rest := by
      simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append] using decomposition
    have next := ih (issuedPrefix ++ [(B, reply)]) decomp (runBits k B q)
    simpa only [List.append_assoc, List.cons_append, List.nil_append, scriptArchive] using next

/-- The prescribed original selector pays exactly the full script length,
including a rejecting word, and invokes its decoder only at the final endpoint.
Its issued archive is the actual script on that same given original history. -/
theorem original_final_script {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (w : List Bool) (free : Option (ZMod 2)) (base : NarrowWindowCost.Archive m) :
    let issued := scriptArchive words (OriginalRecord k (by omega) w)
    PaidTrace (finalSelector base.length words decode) free
      (OriginalRecord k (by omega) w) base issued (decode issued) ∧
    issued.map Prod.fst = words ∧ issued.length = words.length ∧
    NarrowWindowCost.execute k (by omega) (finalSelector base.length words decode)
      words.length w free base = some (decode issued, words.length) := by
  intro issued
  have traced := prescribed_paid_trace words decode base [] words (by simp)
    (OriginalRecord k (by omega) w) free
  simp only [List.append_nil, List.nil_append] at traced
  have wordEq : ∀ (bs : List (Fin m → Bool)) (q : Option (LiveRecord k)),
      (scriptArchive bs q).map Prod.fst = bs := by
    intro bs
    induction bs with
    | nil => intro q; rfl
    | cons B rest ih => intro q; simp only [scriptArchive, List.map_cons, ih]
  refine ⟨traced, wordEq words _, script_length words _, ?_⟩
  exact (execute_paid_trace k m hk _ words.length w free base _ words.length).mpr
    ⟨issued, traced, script_length words _, le_rfl⟩


/-- The complete fixed literal suffix. Both source alphabets admit every
one of these words because its length is m<k. -/
def actualWords (table : Fin (m + 1) → Y) (c : Label table → Word d) :
    List (Fin m → Bool) := (actualRows table c).map (prefixWord m)

theorem script_readings {k m : ℕ} {alphabet : Bool}
    (actions : List (AllowedBlock k m alphabet)) (q : Option (LiveRecord k)) :
    (scriptArchive (actions.map Subtype.val) q).map Prod.snd = fixedBlockArchive actions q := by
  induction actions generalizing q with
  | nil => rfl
  | cons B rest ih =>
    change endpointReading (runBits k B.val q) :: (scriptArchive (rest.map Subtype.val) (runBits k B.val q)).map Prod.snd =
      endpointReading (runBits k B.val q) :: fixedBlockArchive rest (runBits k B.val q)
    exact congrArg (List.cons _) (ih _)

/-- Differences use only the remembered scalar and the source's own endpoints. -/
def endpointDifferences : Option (ZMod 2) → List (Option (ZMod 2)) → List (Option (ZMod 2))
  | _, [] => []
  | previous, next :: rest =>
    (do let x ← previous; let y ← next; pure (y - x)) :: endpointDifferences next rest

def rowReadings (k m : ℕ) : List (ℕ → ZMod 2) → ZMod (k + 1) → List (Option (ZMod 2))
  | [], _ => []
  | q :: rest, j => some (windowCharge k m q j) :: rowReadings k m rest (j - (m : ℕ))

theorem charge_differences (k m : ℕ) (rows : List (ℕ → ZMod 2))
    (v : ZMod 2) (j : ZMod (k + 1)) :
    endpointDifferences (some v) (chargeArchive k m rows v j) = rowReadings k m rows j := by
  induction rows generalizing v j with
  | nil => rfl
  | cons q rest ih =>
    change some (v + windowCharge k m q j - v) ::
      endpointDifferences (some (v + windowCharge k m q j))
        (chargeArchive k m rest (v + windowCharge k m q j) (j - (m : ℕ))) =
      some (windowCharge k m q j) :: rowReadings k m rest (j - (m : ℕ))
    rw [add_sub_cancel_left, ih]

private theorem indexed_row_readings (m d : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (n r : ℕ) (bound : r + n ≤ d) (v : Fin (m + 1)) :
    rowReadings (m + 1) m
      (List.ofFn (fun i : Fin n => actualRow table c ⟨r + i.val, by have := i.isLt; omega⟩))
      ((v.val : ZMod (m + 2)) - (((r + 1) * m : ℕ) : ZMod (m + 2))) =
    List.ofFn (fun i : Fin n => some (vertexBit table c ⟨r + i.val, by have := i.isLt; omega⟩ v)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [rowReadings, Fin.val_zero, Nat.add_zero]
    have inverse := (donor_rows_inverse m d hm table fit c unary ⟨r, by omega⟩).2.2.1
      ((v.val : ZMod (m + 2)) - (((r + 1) * m : ℕ) : ZMod (m + 2)))
    have issued := issued_phase_code m d 0 hm table fit c unary ⟨r, by omega⟩ v
    have phase : -((v.val : ZMod (m + 2)) - (((r + 1) * m : ℕ) : ZMod (m + 2))) =
        -(v.val : ZMod (m + 2)) + (((r + 1) * m : ℕ) : ZMod (m + 2)) := by ring
    simp only [Nat.zero_mul, Nat.cast_zero, zero_add] at issued
    rw [phase, issued] at inverse
    rw [← inverse]
    congr 1
    have nextPhase : (v.val : ZMod (m + 2)) - (((r + 1) * m : ℕ) : ZMod (m + 2)) - (m : ℕ) =
        (v.val : ZMod (m + 2)) - ((((r + 1) + 1) * m : ℕ) : ZMod (m + 2)) := by
      push_cast; ring
    rw [nextPhase]
    simpa only [Fin.tail, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using ih (r + 1) (by omega)

/-- Both physical alternatives give exactly the selected code from each
candidate's own endpoint differences on its supplied native starting record. -/
theorem physical_endpoint_codes (m d : ℕ) (hm : 3 ≤ m) (odd : Odd m) (hd : 2 ≤ d)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (selected : Selection (sourceClauses table d fit) (by omega) c)
    (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (v : ZMod 2) (x : Fin (m + 1)) (alphabet : Bool) :
    let q : Option (LiveRecord (m + 1)) := some ⟨v, -(x.val : ZMod (m + 2)) + (m : ℕ), 1⟩
    let issued := scriptArchive (actualWords table c) q
    (actualWords table c).length = d ∧ none ∉ issued.map Prod.snd ∧
    endpointDifferences (some v) (issued.map Prod.snd) =
      List.ofFn (fun i : Fin d => some (vertexBit table c i x)) := by
  intro q issued
  let rows := actualRows table c
  let j : ZMod (m + 2) := (x.val : ZMod (m + 2)) - (m : ℕ)
  have phase : -(x.val : ZMod (m + 2)) + (m : ℕ) = -j := by dsimp [j]; ring
  have readings : issued.map Prod.snd = chargeArchive (m + 1) m rows v j := by
    have scriptEq : issued.map Prod.snd = fixedBlockArchive
        (chargeBlocks (m + 1) m (by omega) (by omega) alphabet rows) q := by
      have mapVals : ∀ rs : List (ℕ → ZMod 2),
          (chargeBlocks (m + 1) m (by omega) (by omega) alphabet rs).map Subtype.val = rs.map (prefixWord m) := by
        intro rs
        induction rs with
        | nil => rfl
        | cons r rs ih => exact congrArg (List.cons (prefixWord m r)) ih
      have eq := script_readings (chargeBlocks (m + 1) m (by omega) (by omega) alphabet rows) q
      rw [mapVals] at eq
      exact eq
    rw [scriptEq]
    rcases selected with regular | ⟨h, total, distinct, codes, un, extra, pair⟩
    · obtain ⟨head, safe⟩ := regular_rows_safe m d hm hd table fit c regular
      have gcd : Nat.gcd m (m + 2) = 1 := by
        rw [Nat.add_comm m 2, Nat.gcd_add_self_right]
        exact odd.coprime_two_right
      have native := actual_shared_charge_suffix (m + 1) (by omega) m (by omega) (by omega)
        alphabet rows safe v j 1 (by omega) ?_ (by rw [gcd]; exact one_dvd _)
      · simpa only [q, phase] using native.2.1
      · intro row member
        have rowEq : row = actualRow table c (first (by omega)) := by
          obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
          subst d
          simpa only [rows, actualRows, List.ofFn_succ, List.head?_cons, Option.mem_def, Option.some.injEq, first, Fin.val_zero, Fin.mk_zero] using member.symm
        rw [rowEq]
        exact Or.inr head
    · subst d
      have execution := exceptional_literal_execution m hm table fit c unary codes v (-j) 1 (by omega)
      simp only at execution
      have rowEq : rows = [actualRow table c 0, actualRow table c 1] := by
        simp [rows, actualRows, List.ofFn_succ, Fin.tail]
      rw [rowEq]
      change endpointReading (runBits (m + 1) (prefixWord m (actualRow table c 0)) q) ::
        endpointReading (runBits (m + 1) (prefixWord m (actualRow table c 1))
          (runBits (m + 1) (prefixWord m (actualRow table c 0)) q)) :: [] = _
      simp only [chargeArchive]
      rw [show q = some ⟨v, -j, 1⟩ by simp only [q, phase], execution.2.2.2.2.2.2.2.2.1,
        execution.2.2.2.2.2.2.2.2.2]
      have inv0 := (donor_rows_inverse m 2 hm table fit c unary 0).2.2.1 j
      have inv1 := (donor_rows_inverse m 2 hm table fit c unary 1).2.2.1 (j - (m : ℕ))
      have nextPhase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
      simp only [endpointReading, List.cons.injEq, and_true]
      rw [inv0, nextPhase, inv1]
      exact ⟨rfl, rfl⟩
  have live : none ∉ chargeArchive (m + 1) m rows v j :=
    (charge_archive_live (m + 1) m rows v j).2
  refine ⟨by simp [actualWords, actualRows], readings.symm ▸ live, ?_⟩
  rw [readings, charge_differences]
  simpa only [rows, actualRows, Nat.zero_add, Nat.one_mul] using
    indexed_row_readings m d hm table fit c unary d 0 (by omega) x


/-- The selected code expressed as own-endpoint differences. -/
def codeVector {L : Type*} (c : L → Word d) (label : L) : List (Option (ZMod 2)) :=
  List.ofFn (fun i : Fin d => some (if i ∈ c label then 1 else 0))

private theorem code_vector_injective {L : Type*} (c : L → Word d)
    (inj : Function.Injective c) : Function.Injective (codeVector c) := by
  intro a b equal
  apply inj
  ext i
  have funEq := List.ofFn_injective equal
  have bitEq := Option.some.inj (congrFun funEq i)
  by_cases ha : i ∈ c a <;> by_cases hb : i ∈ c b <;> simp_all [codeVector]

/-- Decode the final differences with the fixed injective code table.
The fallback applies only to transcripts outside the stated source fiber. -/
def decodeArchive (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (baseline : ZMod 2) (archive : NarrowWindowCost.Archive m) : Y :=
  if h : ∃ L : Label table,
      codeVector c L = endpointDifferences (some baseline) (archive.map Prod.snd) then
    (Classical.choose h).val
  else table ⟨0, by omega⟩

private theorem decode_correct (table : Fin (m + 1) → Y) (c : Label table → Word d)
    (inj : Function.Injective c) (baseline : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (L : Label table)
    (eq : endpointDifferences (some baseline) (archive.map Prod.snd) = codeVector c L) :
    decodeArchive table c baseline archive = L.val := by
  have existsLabel : ∃ K : Label table,
      codeVector c K = endpointDifferences (some baseline) (archive.map Prod.snd) := ⟨L, eq.symm⟩
  rw [decodeArchive, dif_pos existsLabel]
  have chosen := Classical.choose_spec existsLabel
  have same := code_vector_injective c inj (chosen.trans eq)
  exact congrArg Subtype.val same

/-- The entire fixed physical suffix and forced-final INITIAL decoder on
EVERY given original source history compatible with ONE acquired archive.
The phase-label law is assumed; labels are never replaced by current records.
Only suffix attainment is asserted, with exactly d paid complete words. -/
theorem original_physical_initial_decoder (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m + 1) m (by omega) alphabet free
      (archive ++ [(parent, some (previous + 1))]) = physicalWindow (m + 1) m archive.length)
    (f : Option (LiveRecord (m + 1)) → Y) (initialLabels : ZMod (m + 2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m + 1),
      (some initial, some current) ∈ AcquiredPairs (m + 1) m (by omega) alphabet (some free)
        (archive ++ [(parent, some (previous + 1))]) →
        f (some initial) = initialLabels (-initial.phase))
    (many : 3 ≤ (labels (fun x : Fin (m + 1) =>
      initialLabels (vertex (m + 1) m archive.length x.val))).card) :
    let table := fun x : Fin (m + 1) => initialLabels (vertex (m + 1) m archive.length x.val)
    let d := Nat.clog 2 (labels table).card
    let acquired := archive ++ [(parent, some (previous + 1))]
    ∃ (c : Label table → Word d) (π : NarrowWindowCost.Selector m Y),
      Function.Injective c ∧
      (actualWords table c).length = d ∧
      (∀ y₀ ar B, π y₀ ar = .inr B → DBonacciAdmissible (m + 1) m B) ∧
      ∀ history : List (AllowedBlock (m + 1) m alphabet),
        let w := history.flatMap (fun action => List.ofFn action.val)
        NarrowWindowCost.output (m + 1) (by omega) w = some free →
        ActualArchive (m + 1) (by omega) w acquired →
        let issued := scriptArchive (actualWords table c)
          (OriginalRecord (m + 1) (by omega) (w ++ archiveWords acquired))
        issued.map Prod.fst = actualWords table c ∧ issued.length = d ∧
        none ∉ issued.map Prod.snd ∧
        (∃ L : Label table, L.val = f (OriginalRecord (m + 1) (by omega) w) ∧
          endpointDifferences (some (previous + 1)) (issued.map Prod.snd) = codeVector c L) ∧
        PaidTrace π (some free)
          (OriginalRecord (m + 1) (by omega) (w ++ archiveWords acquired))
          acquired issued (f (OriginalRecord (m + 1) (by omega) w)) ∧
        NarrowWindowCost.execute (m + 1) (by omega) π d (w ++ archiveWords acquired)
          (some free) acquired = some (f (OriginalRecord (m + 1) (by omega) w), d) := by
  intro table d acquired
  obtain ⟨fit, hd, c, inj, bitsInj, selected, unary, extra, windows, donors, starts, seams⟩ :=
    actual_table_codes table odd many
  let decode := decodeArchive table c (previous + 1)
  let π := finalSelector acquired.length (actualWords table c) decode
  have length : (actualWords table c).length = d := by simp [actualWords, actualRows, d]
  refine ⟨c, π, inj, length, ?_, ?_⟩
  · intro y₀ ar B issued
    exact short_legal (m + 1) m (by omega) (by omega) B
  · intro history w freeEq matched issued
    let initialRecord := OriginalRecord (m + 1) (by omega) w
    let currentRecord := OriginalRecord (m + 1) (by omega) (w ++ archiveWords acquired)
    have member : (initialRecord, currentRecord) ∈
        AcquiredPairs (m + 1) m (by omega) alphabet (some free) acquired :=
      ⟨history, freeEq, matched, rfl, rfl⟩
    have facts := full_positive_history_trace (m + 1) m hm odd rfl alphabet free previous
      archive parent prior full f initialLabels wellDefined
    obtain ⟨initial, current, initialEq, currentEq, labelEq, support, value, tail, phase, rest⟩ :=
      facts.2 (initialRecord, currentRecord) member
    change initialRecord = some initial at initialEq
    change currentRecord = some current at currentEq
    change f initialRecord = initialLabels (-initial.phase) at labelEq
    obtain ⟨h, hle, position⟩ := support
    let x : Fin (m + 1) := ⟨h, by omega⟩
    have initialPosition : -initial.phase = vertex (m + 1) m archive.length x.val := position
    have currentPhase : current.phase = -(x.val : ZMod (m + 2)) + (m : ℕ) := by
      rw [phase]
      have pos := initialPosition
      simp only [vertex, Nat.cast_add, Nat.cast_mul] at pos ⊢
      linear_combination -pos
    have currentActual : currentRecord =
        some ⟨previous + 1, -(x.val : ZMod (m + 2)) + (m : ℕ), 1⟩ := by
      rw [currentEq]
      congr 1
      cases current
      simp only at value currentPhase tail
      simp only [value, currentPhase, tail]
    have physical := physical_endpoint_codes m d hm odd hd table fit c selected unary
      (previous + 1) x alphabet
    have issuedEq : issued = scriptArchive (actualWords table c)
        (some (⟨previous + 1, -(x.val : ZMod (m + 2)) + (m : ZMod (m + 2)), 1⟩ : LiveRecord (m + 1))) := by
      exact congrArg (scriptArchive (actualWords table c)) currentActual
    have differences : endpointDifferences (some (previous + 1)) (issued.map Prod.snd) =
        codeVector c (tableLabel table x) := by
      rw [issuedEq]
      exact physical.2.2
    have immutableLabel : (tableLabel table x).val = f initialRecord := by
      change table x = f initialRecord
      rw [labelEq, initialPosition]
    have decoded : decode issued = f initialRecord :=
      (decode_correct table c inj (previous + 1) issued (tableLabel table x) differences).trans immutableLabel
    have exactScript := original_final_script (m + 1) m (by omega) (actualWords table c) decode
      (w ++ archiveWords acquired) (some free) acquired
    dsimp only at exactScript
    rw [decoded, length] at exactScript
    exact ⟨exactScript.2.1, exactScript.2.2.1, issuedEq.symm ▸ physical.2.1,
      ⟨tableLabel table x, immutableLabel, differences⟩, exactScript.1, exactScript.2.2.2⟩

#print axioms physical_endpoint_codes
#print axioms original_physical_initial_decoder

#print axioms donor_rows_inverse
#print axioms regular_rows_safe
#print axioms issued_phase_code
#print axioms exceptional_row_coordinates
#print axioms exceptional_literal_execution
#print axioms original_final_script

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
