/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The selected supports satisfy the direction-pair and size clauses used by the refutation. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

/-! Clause semantics for the unsigned small-support contact rectangle certificate. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportClauses

open Finset
open BalancedCriticalSpectrum (Q flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open Q9SharedContactCNF (Word Axis Variable pos)
open private adjacentWord adjacentWord_spec satisfies_positive_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

private abbrev occ := Variable.occupied

/-- The lexicographic order of the 36 two-element subsets of the nine axes. -/
def pairAxes : Fin 36 → Axis × Axis := ![
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8),
  (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8),
  (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8),
  (3, 4), (3, 5), (3, 6), (3, 7), (3, 8),
  (4, 5), (4, 6), (4, 7), (4, 8),
  (5, 6), (5, 7), (5, 8),
  (6, 7), (6, 8),
  (7, 8)]

theorem pairAxes_lt (p : Fin 36) : (pairAxes p).1 < (pairAxes p).2 := by
  fin_cases p <;> decide +kernel

/-- Corner variables start at DIMACS number 9217. Within a side and pair,
the words occur in natural-number order from 0 through 511. -/
def witnessIndex (s : Bool) (p : Fin 36) (w : Word) : ℕ :=
  9216 + ((if s then 36 else 0) + p.val) * 512 + w.toNat

noncomputable def witnessValuation (S : Bool → Finset (Q 9)) : Sat.Valuation := fun n =>
  if 9216 ≤ n ∧ n < 46080 then
    let k := n - 9216
    let s := decide (18432 ≤ k)
    let p : Fin 36 := ⟨(k / 512) % 36, Nat.mod_lt _ (by decide)⟩
    let w : Word := BitVec.ofNat 9 k
    cubeBitVec 9 w ∈ S s ∧
      flip (cubeBitVec 9 w) (pairAxes p).1 ∈ S s ∧
      flip (cubeBitVec 9 w) (pairAxes p).2 ∈ S s
  else Q9TightDistanceTwoCNF.valuation S n

theorem witness_value (S : Bool → Finset (Q 9)) (s : Bool) (p : Fin 36) (w : Word) :
    witnessValuation S (witnessIndex s p w) ↔
      cubeBitVec 9 w ∈ S s ∧
        flip (cubeBitVec 9 w) (pairAxes p).1 ∈ S s ∧
        flip (cubeBitVec 9 w) (pairAxes p).2 ∈ S s := by
  have hp := p.isLt
  have hw : w.toNat < 512 := w.toFin.isLt
  have hn : 9216 ≤ witnessIndex s p w ∧ witnessIndex s p w < 46080 := by
    cases s <;> simp [witnessIndex] <;> omega
  have hs : decide (18432 ≤ witnessIndex s p w - 9216) = s := by
    cases s <;> simp [witnessIndex] <;> omega
  have hP : (⟨((witnessIndex s p w - 9216) / 512) % 36,
      Nat.mod_lt _ (by decide)⟩ : Fin 36) = p := by
    apply Fin.ext
    change ((witnessIndex s p w - 9216) / 512) % 36 = p.val
    cases s <;> simp [witnessIndex] <;> omega
  have hW : BitVec.ofNat 9 (witnessIndex s p w - 9216) = w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    change (witnessIndex s p w - 9216) % 512 = w.toNat
    cases s <;> simp [witnessIndex] <;> omega
  simp only [witnessValuation, ite_eq_left hn, hs, hP, hW]

theorem ordinary_value (S : Bool → Finset (Q 9)) (n : ℕ) (hn : n < 9216) :
    witnessValuation S n = Q9TightDistanceTwoCNF.valuation S n := by
  have hout : ¬ (9216 ≤ n ∧ n < 46080) := fun h => (Nat.not_le_of_lt hn) h.1
  simp only [witnessValuation, ite_eq_right hout]

private theorem variable_index_lt (v : Variable) : v.index < 9216 := by
  cases v with
  | occupied s w =>
    have hw : w.toNat < 512 := w.toFin.isLt
    cases s <;> simp [Variable.index, Q9SharedContactCNF.wordIndex] <;> omega
  | parityPrefix s w i =>
    have hw : w.toNat < 512 := w.toFin.isLt
    have hi := i.isLt
    cases s <;> simp [Variable.index, Q9SharedContactCNF.wordIndex] <;> omega

theorem occupied_value (S : Bool → Finset (Q 9)) (s : Bool) (w : Word) :
    witnessValuation S (occ s w).index ↔ cubeBitVec 9 w ∈ S s := by
  rw [ordinary_value S (occ s w).index (variable_index_lt (occ s w))]
  exact Q9TightDistanceTwoCNF.valuation_occupied S s w

theorem witnesses_imply_center {S : Bool → Finset (Q 9)} (s : Bool) (p : Fin 36) (w : Word) :
    (witnessValuation S).satisfies
      [.neg (witnessIndex s p w), pos (occ s w)] := by
  intro hw hn
  apply hn
  exact (occupied_value S s w).mpr ((witness_value S s p w).mp hw).1

theorem witnesses_imply_first {S : Bool → Finset (Q 9)} (s : Bool) (p : Fin 36) (w : Word) :
    (witnessValuation S).satisfies
      [.neg (witnessIndex s p w), pos (occ s (adjacentWord w (pairAxes p).1))] := by
  intro hw hn
  apply hn
  apply (occupied_value S s _).mpr
  rw [adjacentWord_spec]
  exact ((witness_value S s p w).mp hw).2.1

theorem witnesses_imply_second {S : Bool → Finset (Q 9)} (s : Bool) (p : Fin 36) (w : Word) :
    (witnessValuation S).satisfies
      [.neg (witnessIndex s p w), pos (occ s (adjacentWord w (pairAxes p).2))] := by
  intro hw hn
  apply hn
  apply (occupied_value S s _).mpr
  rw [adjacentWord_spec]
  exact ((witness_value S s p w).mp hw).2.2

private theorem positive_list {v : Sat.Valuation} {indices : List ℕ}
    (h : ∃ i ∈ indices, v i) : v.satisfies (indices.map Sat.Literal.pos) := by
  induction indices with
  | nil => simp at h
  | cons x xs ih =>
    intro hx
    obtain ⟨i, hi, hv⟩ := h
    rcases List.mem_cons.mp hi with rfl | hi
    · exact False.elim (hx hv)
    · exact ih ⟨i, hi, hv⟩

/-- The generator appends all 512 corner literals for each side and direction pair. -/
def pairRow (s : Bool) (p : Fin 36) : Sat.Clause :=
  ((List.finRange 512).map (fun i => witnessIndex s p (BitVec.ofFin i))).map Sat.Literal.pos

theorem realizedClause {S : Bool → Finset (Q 9)} (s : Bool) (p : Fin 36)
    (h : ∃ x ∈ S s, flip x (pairAxes p).1 ∈ S s ∧ flip x (pairAxes p).2 ∈ S s) :
    (witnessValuation S).satisfies (pairRow s p) := by
  obtain ⟨x, hx, hi, hj⟩ := h
  obtain ⟨w, rfl⟩ := (cubeBitVec 9).surjective x
  unfold pairRow
  apply positive_list
  refine ⟨witnessIndex s p w, ?_, (witness_value S s p w).mpr ⟨hx, hi, hj⟩⟩
  exact List.mem_map.mpr ⟨w.toFin, List.mem_finRange _, by rw [BitVec.ofFin_toFin]⟩

theorem pairClause {S : Bool → Finset (Q 9)} (s : Bool) (p : Fin 36)
    (hcorner : ∀ i j : Axis, i ≠ j → ∃ x ∈ S s, flip x i ∈ S s ∧ flip x j ∈ S s) :
    (witnessValuation S).satisfies (pairRow s p) :=
  realizedClause s p (hcorner _ _ (ne_of_lt (pairAxes_lt p)))

/-- A size obstruction requires an occupied word outside the given list. -/
def sizeRow (s : Bool) (inside : List Word) : Sat.Clause :=
  (((List.finRange 512).filter (fun i => decide (BitVec.ofFin i ∉ inside))).map
    (fun i => occ s (BitVec.ofFin i))).map pos

theorem sizeClause {S : Bool → Finset (Q 9)} (s : Bool) (inside : List Word)
    (hinside : inside.toFinset.card < 60) (hsize : 60 ≤ (S s).card) :
    (witnessValuation S).satisfies (sizeRow s inside) := by
  unfold sizeRow
  apply satisfies_positive_list
  intro hall
  have hsub : S s ⊆ inside.toFinset.image (cubeBitVec 9) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (cubeBitVec 9).surjective x
    by_cases hw : w ∈ inside
    · exact Finset.mem_image.mpr ⟨w, List.mem_toFinset.mpr hw, rfl⟩
    · exfalso
      have hf : w.toFin ∈ (List.finRange 512).filter
          (fun i => decide (BitVec.ofFin i ∉ inside)) := by
        exact List.mem_filter.mpr
          ⟨List.mem_finRange _, by simpa only [decide_eq_true_eq, BitVec.ofFin_toFin] using hw⟩
      apply hall (occ s w) (List.mem_map.mpr ⟨w.toFin, hf, by rw [BitVec.ofFin_toFin]⟩)
      exact (occupied_value S s w).mpr hx
  have hbound : (S s).card ≤ inside.toFinset.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

/-- The seven excluded support lists in k33-small-support-size-clauses.json,
in the generator's order, with the side encoded as false for 0 and true for 1. -/
def sizeBlock : Fin 7 → Bool × List Word := ![
  (false, [15, 27, 30, 39, 45, 51, 54, 57, 60, 79, 91, 94, 95, 103, 109, 111, 115, 118,
    119, 121, 123, 124, 125, 126, 143, 155, 158, 159, 167, 173, 175, 179, 182, 183, 185, 187,
    188, 189, 190, 271, 283, 286, 287, 295, 301, 303, 307, 310, 311, 313, 315, 316, 317, 318]),
  (true, [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 33, 36, 48, 259, 262, 265,
    268, 274, 280, 289, 292, 304, 321, 322, 323, 324, 326, 328, 329, 332, 336, 338, 344, 352,
    353, 356, 368, 385, 386, 387, 388, 390, 392, 393, 396, 400, 402, 408, 416, 417, 420, 432]),
  (false, [15, 27, 30, 31, 39, 45, 47, 51, 54, 55, 57, 59, 60, 61, 62, 143, 155, 158,
    167, 173, 179, 182, 185, 188, 207, 219, 222, 223, 231, 237, 239, 243, 246, 247, 249, 251,
    252, 253, 254, 399, 411, 414, 415, 423, 429, 431, 435, 438, 439, 441, 443, 444, 445, 446]),
  (true, [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 33, 36, 48, 131, 134, 137,
    140, 146, 152, 161, 164, 176, 193, 194, 195, 196, 198, 200, 201, 204, 208, 210, 216, 224,
    225, 228, 240, 385, 386, 387, 388, 390, 392, 393, 396, 400, 402, 408, 416, 417, 420, 432]),
  (true, [3, 6, 9, 12, 18, 24, 33, 36, 48, 65, 66, 67, 68, 70, 72, 73, 76, 80,
    82, 88, 96, 97, 100, 112, 129, 130, 131, 132, 134, 136, 137, 140, 144, 146, 152, 160,
    161, 164, 176, 257, 258, 259, 260, 262, 264, 265, 268, 272, 274, 280, 288, 289, 292, 304]),
  (false, [15, 27, 30, 31, 39, 45, 47, 51, 54, 55, 57, 59, 60, 61, 62, 79, 91, 94,
    103, 109, 115, 118, 121, 124, 207, 219, 222, 223, 231, 237, 239, 243, 246, 247, 249, 251,
    252, 253, 254, 335, 347, 350, 351, 359, 365, 367, 371, 374, 375, 377, 379, 380, 381, 382]),
  (true, [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 33, 36, 48, 67, 70, 73,
    76, 82, 88, 97, 100, 112, 193, 194, 195, 196, 198, 200, 201, 204, 208, 210, 216, 224,
    225, 228, 240, 321, 322, 323, 324, 326, 328, 329, 332, 336, 338, 344, 352, 353, 356, 368])]

theorem sizeBlock_length (b : Fin 7) : (sizeBlock b).2.length < 60 := by
  fin_cases b <;> decide +kernel

theorem obstructionClause {S : Bool → Finset (Q 9)} (b : Fin 7)
    (hsize : 60 ≤ (S (sizeBlock b).1).card) :
    (witnessValuation S).satisfies (sizeRow (sizeBlock b).1 (sizeBlock b).2) :=
  sizeClause _ _ (lt_of_le_of_lt (List.toFinset_card_le _) (sizeBlock_length b)) hsize

def literalIndex : Sat.Literal → ℕ
  | .pos n => n
  | .neg n => n

/-- Satisfaction of each ordinary clause transfers to the extended valuation. -/
theorem ordinaryClause {S : Bool → Finset (Q 9)} {c : Sat.Clause}
    (h : (Q9TightDistanceTwoCNF.valuation S).satisfies c)
    (hsmall : List.all c (fun l => decide (literalIndex l < 9216)) = true) :
    (witnessValuation S).satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h
  | cons x xs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hsmall
    have hsize : literalIndex x < 9216 := of_decide_eq_true hsmall.1
    have he := ordinary_value S (literalIndex x) hsize
    intro hx
    refine ih (h ?_) hsmall.2
    cases x <;> simp only [literalIndex] at he <;>
      simpa only [Sat.Valuation.neg, ← he] using hx

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportClauses
