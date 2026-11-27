/- GID: D5/S3/Quantum/Codes/BinaryEARankOneCore
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEARankOneCore
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Quantum/Codes/BinaryEARankOneCore.claim; result=D5/S3/Quantum/Codes/BinaryEARankOneCore.result; claim=D5/S3/Quantum/Codes/BinaryEARankOneCore.claim
   digest: No normalized self-orthogonal binary rank-one core of support eight through ten meets the three-zero bound. -/

import OmegaBuild.Commands
import Mathlib.Data.List.Sort

compile_only_with_mathlib

/-! The finite rank-one core obstruction for trureturing issue #34860.
The head of each packed word occupies its four low bits. -/

namespace D5.S3.Quantum.Codes.BinaryEARankOneCore

private def outer (a : Nat) : Nat :=
  let bit (i j : Nat) := (a.testBit i && a.testBit j).toNat
  a % 16 + 16 * (bit 0 1 + 2 * bit 0 2 + 4 * bit 0 3 +
    8 * bit 1 2 + 16 * bit 1 3 + 32 * bit 2 3)

/-- The upper triangle of the binary tail Gram matrix, with the four diagonal
bits first, followed by entries 01, 02, 03, 12, 13 and 23. -/
def gram (columns : List Nat) : Nat :=
  columns.foldr (fun a rest => outer a ^^^ rest) 0

/-- Multiply the matrix of tail columns by the given packed tail vector. -/
def columnSum : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, row =>
    (if row.testBit 0 then a else 0) ^^^ columnSum rest (row >>> 1)

private def dot4 (h a : Nat) : Bool :=
  ((h.testBit 0 && a.testBit 0) != (h.testBit 1 && a.testBit 1)) !=
    ((h.testBit 2 && a.testBit 2) != (h.testBit 3 && a.testBit 3))

private def radicalTail (h : Nat) : List Nat → Nat
  | [] => 0
  | a :: rest => (dot4 h a).toNat + 2 * radicalTail h rest

/-- The radical word with head `h` and tail given by the column evaluations. -/
def radicalWord (columns : List Nat) (h : Nat) : Nat :=
  h + 16 * radicalTail h columns

/-- Count simultaneous zero coordinates for `(X(q) + H(h), Z(q))`.
Here `x` and `z` are tail words, and the X-head before translation is zero. -/
def zeroCount (s q z x radical : Nat) : Nat :=
  let support := ((16 * x) ^^^ radical) ||| (q + 16 * z)
  (List.range s).countP (fun i => !support.testBit i)

/-- A systematic radical and systematic Z projection with a linear X lift.
The sorted nonzero masks are the columns of `A` in `[I | A]`.
The Gram condition encodes `AAᵀ = I` and the syndrome condition encodes
`ARᵀ = I`, where `[I | R]` generates the Z projection. -/
structure Core (m : Nat) where
  columns : List Nat
  length_eq : columns.length = m
  sorted : columns.Pairwise (· ≤ ·)
  column_bounds : ∀ a ∈ columns, 0 < a ∧ a < 16
  self_orthogonal : gram columns = 15
  zTail : BitVec 4 → BitVec m
  xTail : BitVec 4 → BitVec m
  z_xor : ∀ q r, zTail (q ^^^ r) = zTail q ^^^ zTail r
  x_xor : ∀ q r, xTail (q ^^^ r) = xTail q ^^^ xTail r
  syndrome : ∀ i : Fin 4,
    columnSum columns (zTail ((1 : BitVec 4) <<< i.val)).toNat = (1 : Nat) <<< i.val
  distance : ∀ q : BitVec 4, q ≠ 0 → ∀ h : BitVec 4,
    zeroCount (m + 4) q.toNat (zTail q).toNat (xTail q).toNat
      (radicalWord columns h.toNat) ≤ 3

/-- Existence of a normalized core at support eight, nine or ten. -/
def claim : Prop :=
  ∃ m, 4 ≤ m ∧ m ≤ 6 ∧ Nonempty (Core m)

private def columnChoices (lower : Nat) : List Nat :=
  List.range' lower (16 - lower)

-- The remaining Gram diagonal determines the final column.
private def candidates : Nat → Nat → Nat → List (List Nat)
  | 0, _, needed => if needed == 0 then [[]] else []
  | 1, lower, needed =>
    let a := needed % 16
    if lower ≤ a ∧ outer a = needed then [[a]] else []
  | n + 2, lower, needed =>
    (columnChoices lower).flatMap fun a =>
      (candidates (n + 1) a (needed ^^^ outer a)).map (a :: ·)

private def rowChoices (m : Nat) (columns : List Nat) (syndrome : Nat) : List Nat :=
  (List.range (2 ^ m)).filter fun r => columnSum columns r == syndrome

private def allowed (m : Nat) (radicals : List Nat) (q z : Nat) : List Nat :=
  (List.range (2 ^ m)).filter fun x =>
    radicals.all fun h => decide (zeroCount (m + 4) q z x h ≤ 3)

private def liftExists (m : Nat) (radicals : List Nat) (z1 z2 z4 : Nat) : Bool :=
  let allowed1 := allowed m radicals 1 z1
  let allowed2 := allowed m radicals 2 z2
  let allowed3 := allowed m radicals 3 (z1 ^^^ z2)
  let allowed4 := allowed m radicals 4 z4
  let allowed5 := allowed m radicals 5 (z1 ^^^ z4)
  let allowed6 := allowed m radicals 6 (z2 ^^^ z4)
  let allowed7 := allowed m radicals 7 ((z1 ^^^ z2) ^^^ z4)
  allowed1.any fun x1 =>
    allowed2.any fun x2 =>
      allowed3.contains (x1 ^^^ x2) &&
        allowed4.any fun x4 =>
          allowed5.contains (x1 ^^^ x4) &&
          allowed6.contains (x2 ^^^ x4) &&
          allowed7.contains ((x1 ^^^ x2) ^^^ x4)

private def survives (m : Nat) (columns : List Nat) : Bool :=
  let radicals := (List.range 16).map (radicalWord columns)
  (rowChoices m columns 1).any fun z1 =>
    (rowChoices m columns 2).any fun z2 =>
      (rowChoices m columns 4).any fun z4 =>
        liftExists m radicals z1 z2 z4

private def search (m : Nat) : Bool :=
  (candidates m 1 15).any (survives m)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem search_four : search 4 = false := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem search_five : search 5 = false := by decide +kernel

private def searchFrom (m start : Nat) : Bool :=
  ((candidates m 1 15).drop start).any (survives m)

private def searchBlock (m start count : Nat) : Bool :=
  (((candidates m 1 15).drop start).take count).any (survives m)

-- Taking and dropping the same prefix partitions the entire remaining search.
private theorem search_join {m start count : Nat}
    (block : searchBlock m start count = false)
    (rest : searchFrom m (start + count) = false) : searchFrom m start = false := by
  unfold searchBlock at block
  unfold searchFrom at rest ⊢
  rw [← List.drop_drop] at rest
  rw [← List.take_append_drop count (List.drop start (candidates m 1 15)),
    List.any_append, block, rest]
  rfl

-- Bound kernel memory by checking four candidates at a time. The last
-- certificate checks the entire suffix, so no candidate count is assumed.
section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

private theorem search_six_from_0 : searchBlock 6 0 4 = false := by decide +kernel

private theorem search_six_from_4 : searchBlock 6 4 4 = false := by decide +kernel

private theorem search_six_from_8 : searchBlock 6 8 4 = false := by decide +kernel

private theorem search_six_from_12 : searchBlock 6 12 4 = false := by decide +kernel

private theorem search_six_from_16 : searchBlock 6 16 4 = false := by decide +kernel

private theorem search_six_from_20 : searchBlock 6 20 4 = false := by decide +kernel

private theorem search_six_from_24 : searchBlock 6 24 4 = false := by decide +kernel

private theorem search_six_from_28 : searchBlock 6 28 4 = false := by decide +kernel

private theorem search_six_from_32 : searchFrom 6 32 = false := by decide +kernel

end

private theorem search_six : search 6 = false := by
  have h28 := search_join (start := 28) (count := 4) search_six_from_28 search_six_from_32
  have h24 := search_join (start := 24) (count := 4) search_six_from_24 h28
  have h20 := search_join (start := 20) (count := 4) search_six_from_20 h24
  have h16 := search_join (start := 16) (count := 4) search_six_from_16 h20
  have h12 := search_join (start := 12) (count := 4) search_six_from_12 h16
  have h8 := search_join (start := 8) (count := 4) search_six_from_8 h12
  have h4 := search_join (start := 4) (count := 4) search_six_from_4 h8
  have h0 := search_join (start := 0) (count := 4) search_six_from_0 h4
  simpa only [searchFrom, List.drop_zero, search] using h0

private theorem candidates_complete {columns : List Nat} {lower : Nat}
    (hs : columns.Pairwise (· ≤ ·))
    (hb : ∀ a ∈ columns, lower ≤ a ∧ a < 16) :
    columns ∈ candidates columns.length lower (gram columns) := by
  induction columns generalizing lower with
  | nil => simp [candidates, gram]
  | cons a rest ih =>
    have ha := hb a List.mem_cons_self
    cases rest with
    | nil =>
      have houter : outer a % 16 = a := by simp [outer, Nat.mod_eq_of_lt ha.2]
      simp [candidates, gram, houter, ha.1]
    | cons b rest =>
      have hrest := List.pairwise_cons.mp hs
      have hb' (x : Nat) (hx : x ∈ b :: rest) : a ≤ x ∧ x < 16 :=
        ⟨hrest.1 x hx, (hb x (List.mem_cons_of_mem a hx)).2⟩
      have hcol : a ∈ columnChoices lower := by
        rw [columnChoices, List.mem_range'_1]
        exact ⟨ha.1, by omega⟩
      have hgram : gram (a :: b :: rest) ^^^ outer a = gram (b :: rest) := by
        change (outer a ^^^ gram (b :: rest)) ^^^ outer a = gram (b :: rest)
        rw [Nat.xor_comm (outer a) (gram (b :: rest)), Nat.xor_assoc, Nat.xor_self,
          Nat.xor_zero]
      rw [show (a :: b :: rest).length = rest.length + 2 from rfl, candidates]
      apply List.mem_flatMap.mpr
      refine ⟨a, hcol, List.mem_map_of_mem ?_⟩
      rw [hgram]
      exact ih hrest.2 hb'

private theorem row_mem {m : Nat} {columns : List Nat} {row : BitVec m} {s : Nat}
    (h : columnSum columns row.toNat = s) : row.toNat ∈ rowChoices m columns s :=
  List.mem_filter.mpr ⟨List.mem_range.mpr row.isLt, beq_iff_eq.mpr h⟩

private theorem allowed_value {m : Nat} (c : Core m) (q : BitVec 4) (hq : q ≠ 0) :
    (c.xTail q).toNat ∈ allowed m ((List.range 16).map (radicalWord c.columns))
      q.toNat (c.zTail q).toNat := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (c.xTail q).isLt, List.all_eq_true.mpr ?_⟩
  intro radical hr
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hr
  have hh' : (BitVec.ofNat 4 h).toNat = h :=
    Nat.mod_eq_of_lt (List.mem_range.mp hh)
  simpa only [hh'] using decide_eq_true (c.distance q hq (BitVec.ofNat 4 h))

private theorem map_xor_toNat {m : Nat} {f : BitVec 4 → BitVec m}
    (hf : ∀ q r, f (q ^^^ r) = f q ^^^ f r) (q r : BitVec 4) :
    (f (q ^^^ r)).toNat = (f q).toNat ^^^ (f r).toNat := by
  rw [hf, BitVec.toNat_xor]

private theorem survives_core {m : Nat} (c : Core m) : survives m c.columns = true := by
  unfold survives
  refine List.any_eq_true.mpr ⟨(c.zTail 1).toNat, row_mem (c.syndrome 0), ?_⟩
  refine List.any_eq_true.mpr ⟨(c.zTail 2).toNat, row_mem (c.syndrome 1), ?_⟩
  refine List.any_eq_true.mpr ⟨(c.zTail 4).toNat, row_mem (c.syndrome 2), ?_⟩
  unfold liftExists
  refine List.any_eq_true.mpr ⟨(c.xTail 1).toNat, allowed_value c 1 (by decide), ?_⟩
  refine List.any_eq_true.mpr ⟨(c.xTail 2).toNat, allowed_value c 2 (by decide), ?_⟩
  simp only [Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rw [← map_xor_toNat c.z_xor 1 2, ← map_xor_toNat c.x_xor 1 2]
    exact allowed_value c 3 (by decide)
  · refine List.any_eq_true.mpr ⟨(c.xTail 4).toNat, allowed_value c 4 (by decide), ?_⟩
    simp only [Bool.and_eq_true, List.contains_iff_mem]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← map_xor_toNat c.z_xor 1 4, ← map_xor_toNat c.x_xor 1 4]
      exact allowed_value c 5 (by decide)
    · rw [← map_xor_toNat c.z_xor 2 4, ← map_xor_toNat c.x_xor 2 4]
      exact allowed_value c 6 (by decide)
    · rw [← map_xor_toNat c.z_xor 1 2, ← map_xor_toNat c.z_xor (1 ^^^ 2) 4,
        ← map_xor_toNat c.x_xor 1 2, ← map_xor_toNat c.x_xor (1 ^^^ 2) 4]
      exact allowed_value c 7 (by decide)

private theorem search_complete {m : Nat} (c : Core m) : search m = true := by
  have h := candidates_complete c.sorted (fun a ha => c.column_bounds a ha)
  rw [c.length_eq, c.self_orthogonal] at h
  exact List.any_eq_true.mpr ⟨c.columns, h, survives_core c⟩

/-- No normalized rank-one core of support eight, nine or ten meets the
three-zero bound. The seven nonzero words in the first three head directions
already force a contradiction. -/
theorem result : ¬ claim := by
  rintro ⟨m, hlo, hhi, ⟨core⟩⟩
  have h : search m = false := by
    have hm : m = 4 ∨ m = 5 ∨ m = 6 := by omega
    rcases hm with rfl | rfl | rfl
    · exact search_four
    · exact search_five
    · exact search_six
  rw [search_complete core] at h
  cases h

end D5.S3.Quantum.Codes.BinaryEARankOneCore
