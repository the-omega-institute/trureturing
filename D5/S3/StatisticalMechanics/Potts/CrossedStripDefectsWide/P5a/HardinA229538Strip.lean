/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.vector_polynomial
   digest: The order-twenty recurrence for five-row one-defect canonical HDA colourings. -/

/-
admission_basis: open-problem-resolution (#32224; Proved)
escape_witness: none (helpers consumed by the settlement result)
edges: proof_shape=bind-only; consumers=HardinA229538Strip.a
mem_edges: proof_shape=content; consumers=HardinA229538Strip.cost_zero
edges_eq: proof_shape=content; consumers=HardinA229538Strip.cost_countCut
cut_card: proof_shape=content; consumers=HardinA229538Strip.cut_total_exclusion
cut_total_exclusion: proof_shape=content; consumers=HardinA229538Strip.result, HardinA229641Strip.result
cost: proof_shape=bind-only; consumers=HardinA229538Strip.cost_zero
bondDefects_empty: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count, HardinA229641Strip.transfer_count
cost_zero: proof_shape=bind-only; consumers=HardinA229538Strip.zero_cost_entry._simp_1_1
zero_cost_entry: proof_shape=bind-only; consumers=HardinA229538Strip.transition_entry, HardinA229641Strip.transfer_count._simp_1_2
oneDefect: proof_shape=bind-only; consumers=HardinA229538Strip.transfer
transfer: proof_shape=bind-only; consumers=HardinA229538Strip.result
transfer_readout: proof_shape=bind-only; consumers=HardinA229538Strip.result, HardinA229641Strip.old_coordinate, HardinA229641Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229538Strip.result
countCut: proof_shape=bind-only; consumers=HardinA229538Strip.cost_countCut
cost_countCut: proof_shape=content; consumers=HardinA229538Strip.moves_one_filter
movesOne: proof_shape=bind-only; consumers=HardinA229538Strip.step_one
moves_one_filter: proof_shape=content; consumers=HardinA229538Strip.step_one
weighted_indicator_sum: proof_shape=bind-only; consumers=HardinA229538Strip.step_one, HardinA229641Strip.step_two
step_one: proof_shape=content; consumers=HardinA229538Strip.seed_image, HardinA229641Strip.seed_image₁
weights: proof_shape=bind-only; consumers=HardinA229641Strip.top_seed
weights_initial: proof_shape=bind-only; consumers=HardinA229538Strip.weight_eq
weights_step: proof_shape=content; consumers=HardinA229538Strip.zero_values
zeroValues: proof_shape=bind-only; consumers=HardinA229538Strip.weight_eq
weight_eq: proof_shape=bind-only; consumers=HardinA229538Strip.zero_values, HardinA229538Strip.weighted_image, HardinA229641Strip.weighted_top
zero_values: proof_shape=content; consumers=HardinA229641Strip.old_values
classIndex: proof_shape=bind-only; consumers=HardinA229641Strip.topSeed
oneAtWidthOne: proof_shape=bind-only; consumers=HardinA229538Strip.tableOne
tableOne: proof_shape=bind-only; consumers=HardinA229538Strip.table_base
seedImage: proof_shape=bind-only; consumers=HardinA229538Strip.seed_image
seed_image: proof_shape=content; consumers=HardinA229538Strip.weighted_image
weighted_image: proof_shape=content; consumers=HardinA229538Strip.table_step
table_base: proof_shape=bind-only; consumers=HardinA229538Strip.table_powers
table_step: proof_shape=content; consumers=HardinA229538Strip.table_powers
table_powers: proof_shape=content; consumers=HardinA229641Strip.old_values
coefficients538: proof_shape=bind-only; consumers=HardinA229538Strip.result
new_polynomial: proof_shape=content; consumers=HardinA229538Strip.vector_polynomial
inherited_polynomial: proof_shape=content; consumers=HardinA229538Strip.vector_polynomial
vector_polynomial: proof_shape=content; consumers=HardinA229538Strip.result
canonicalCount: proof_shape=bind-only; consumers=HardinA229538Strip.a
a: proof_shape=bind-only; consumers=HardinA229538Strip.result
residual: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count
transition_entry: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count, HardinA229641Strip.transfer_count
transfer_count: proof_shape=bind-only; consumers=HardinA229538Strip.result
labelled_scale: proof_shape=content; consumers=HardinA229538Strip.result, HardinA229641Strip.result
result: proof_shape=content; consumers=none (external open-problem-resolution #32224)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Chromatic
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Init.ByCases
import Init.Classical
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Function
import Init.Data.Int.Basic
import Init.Data.Int.Lemmas
import Init.Data.List.Basic
import Init.Data.List.FinRange
import Init.Data.List.Lemmas
import Init.Data.List.Nat.Pairwise
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Data.Nat.Dvd
import Init.Data.Nat.Lemmas
import Init.Data.Prod
import Init.Data.Sum.Basic
import Init.Prelude
import Init.Notation
import Init.PropLemmas
import Init.SimpLemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.IsEmpty.Basic
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip

section

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA233178Chromatic (colour Column Bond T moves step_fast table powers_table cut_parts)
open HardinA233178Recurrence (columnEquiv)
open D5.S3.StatisticalMechanics.Potts.StripDefects
open DefectTransfer (bondDefects)
open HardinA229637RowColumn (betw)

def edges : Finset (Fin 5 × Fin 5) := Finset.univ.diag ∪ betw 5

theorem mem_edges (e : Fin 5 × Fin 5) :
    e ∈ edges ↔ e.1.val ≤ e.2.val + 1 ∧ e.2.val ≤ e.1.val + 1 := by
  obtain ⟨x, y⟩ := e
  simp only [edges, betw, Finset.mem_union, Finset.mem_diag, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← Fin.val_inj]
  omega

private theorem edges_eq :
    edges = {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2),
      (2, 3), (3, 2), (3, 3), (3, 4), (4, 3), (4, 4)} := by
  decide +kernel

private theorem cut_card (k : ℕ) :
    ((Finset.univ : Finset (Fin k)).diag ∪ betw k).card = k + 2 * (k - 1) := by
  cases k with
  | zero => simp [betw]
  | succ k =>
    obtain ⟨_, hbetw, hparts, hstraight⟩ := cut_parts k
    rw [Finset.card_union_of_disjoint hstraight, hbetw, Finset.card_union_of_disjoint hparts]
    simp only [Finset.diag_card, Finset.card_univ, Fintype.card_fin, Finset.card_map, Nat.add_sub_cancel]
    omega

theorem cut_total_exclusion (D : ℕ) :
    (∀ m : ℕ, D ≠ m * edges.card) ↔ ¬ 13 ∣ D := by
  change (∀ m : ℕ, D ≠ m * ((Finset.univ : Finset (Fin 5)).diag ∪ betw 5).card) ↔ _
  rw [cut_card]
  simp only [dvd_iff_exists_eq_mul_left, not_exists, ne_eq]

def cost (p q : Column) : ℕ :=
  bondDefects edges (columnEquiv p) (columnEquiv q)

theorem bondDefects_empty {q k : ℕ} (r t : Fin k → Fin q) : bondDefects ∅ r t = 0 := by
  rw [bondDefects, Finset.filter_empty, Finset.card_empty]

theorem cost_zero (p q : Column) : cost p q = 0 ↔ Bond p q := by
  simp only [cost, bondDefects, Finset.card_filter_eq_zero_iff, Bond]
  exact ⟨fun h i j hij => h (i, j) ((mem_edges _).mpr hij),
    fun h e he => h e.1 e.2 ((mem_edges _).mp he)⟩

theorem zero_cost_entry (p q : Column) : (if cost p q = 0 then (1 : ℤ) else 0) = T p q := by
  simp only [T, cost_zero]

def oneDefect {R : Type*} [Zero R] [One R] : Matrix Column Column R :=
  fun p q => if cost p q = 1 then 1 else 0

def transfer : Matrix (Column ⊕ Column) (Column ⊕ Column) ℤ :=
  Matrix.fromBlocks T oneDefect 0 T

def terminal {C : Type*} {Z : Type*} {R : Type*} [Zero R] [One R] : C ⊕ Z → R :=
  Sum.elim 0 1

/-- The vector recurrence is equivalent to every shifted scalar readout recurrence.
The coefficient action commutes with left multiplication by matrix and readout entries,
so both operations carry the coefficients through the recurrence. -/
theorem transfer_readout {S R K : Type*} [Fintype S] [DecidableEq S]
    [Semiring R] [SMul K R] [SMulCommClass K R R]
    (M : Matrix S S R) (u : S → R) (d b : ℕ) (c : Fin d → K) :
    ((M ^ (b + d)).mulVec u = ∑ j : Fin d, c j • (M ^ (b + j.val)).mulVec u) ↔
      ∀ (v : S → R) (n : ℕ),
        dotProduct v ((M ^ (n + b + d)).mulVec u) =
          ∑ j : Fin d, c j • dotProduct v ((M ^ (n + b + j.val)).mulVec u) := by
  have rightMul (k : K) (x : R) : k • x = x * (k • (1 : R)) := by
    simpa only [smul_eq_mul, mul_one] using smul_comm k x (1 : R)
  letI : DistribSMul K R :=
    { toSMul := ‹SMul K R›
      smul_zero := fun k => by rw [rightMul k 0, zero_mul]
      smul_add := fun k x y => by rw [rightMul k (x + y), rightMul k x, rightMul k y, add_mul] }
  constructor
  · intro h v n
    have shifted := congrArg ((M ^ n).mulVec) h
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add,
      ← Nat.add_assoc] at shifted
    rw [shifted, dotProduct_sum]; simp_rw [dotProduct_smul]
  · intro h; funext p
    simpa only [Nat.zero_add, single_one_dotProduct, Finset.sum_apply, Pi.smul_apply] using h (Pi.single p 1) 0

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def countCut (p q : Column) : ℕ :=
    (if colour p 0 = colour q 0 then 1 else 0)
    + (if colour p 0 = colour q 1 then 1 else 0)
    + (if colour p 1 = colour q 0 then 1 else 0)
    + (if colour p 1 = colour q 1 then 1 else 0)
    + (if colour p 1 = colour q 2 then 1 else 0)
    + (if colour p 2 = colour q 1 then 1 else 0)
    + (if colour p 2 = colour q 2 then 1 else 0)
    + (if colour p 2 = colour q 3 then 1 else 0)
    + (if colour p 3 = colour q 2 then 1 else 0)
    + (if colour p 3 = colour q 3 then 1 else 0)
    + (if colour p 3 = colour q 4 then 1 else 0)
    + (if colour p 4 = colour q 3 then 1 else 0)
    + (if colour p 4 = colour q 4 then 1 else 0)

theorem cost_countCut (p q : Column) : cost p q = countCut p q := by
  simp only [cost, D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.bondDefects,
    edges_eq, Finset.card_filter]
  repeat' rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton, countCut, Nat.add_assoc] <;> rfl

def movesOne : Column → List Column := ![
  [],
  [122, 123, 124, 131, 132, 133, 149, 150, 151, 158, 159, 160, 203, 204, 205, 212, 213, 214, 230, 231, 232, 239, 240, 241],
  [120, 122, 124, 129, 131, 133, 147, 149, 151, 156, 158, 160, 201, 203, 205, 210, 212, 214, 228, 230, 232, 237, 239, 241],
  [125, 131, 132, 133, 152, 158, 159, 160, 206, 212, 213, 214, 233, 239, 240, 241],
  [123, 125, 126, 128, 150, 152, 153, 155, 204, 206, 207, 209, 231, 233, 234, 236],
  [126, 129, 132, 153, 156, 159, 207, 210, 213, 234, 237, 240],
  [120, 122, 124, 130, 147, 149, 151, 157, 201, 203, 205, 211, 228, 230, 232, 238],
  [117, 120, 123, 144, 147, 150, 198, 201, 204, 225, 228, 231],
  [117, 118, 129, 130, 144, 145, 156, 157, 198, 199, 210, 211, 225, 226, 237, 238],
  [133, 134, 151, 152, 157, 158, 214, 215, 232, 233, 238, 239],
  [134, 152, 155, 159, 160, 215, 233, 236, 240, 241],
  [154, 157, 160, 235, 238, 241],
  [134, 143, 155, 159, 160, 215, 224, 236, 240, 241],
  [126, 128, 132, 134, 135, 137, 141, 143, 207, 209, 213, 215, 216, 218, 222, 224],
  [126, 135, 154, 155, 159, 207, 216, 235, 236, 240],
  [],
  [135, 144, 153, 216, 225, 234],
  [135, 136, 144, 145, 153, 154, 216, 217, 225, 226, 234, 235],
  [124, 125, 130, 131, 148, 149, 205, 206, 211, 212, 229, 230],
  [119, 122, 125, 200, 203, 206],
  [118, 120, 122, 130, 148, 199, 201, 203, 211, 229],
  [],
  [108, 110, 117, 119, 126, 128, 189, 191, 198, 200, 207, 209],
  [108, 117, 126, 189, 198, 207],
  [112, 118, 120, 122, 148, 193, 199, 201, 203, 229],
  [108, 118, 119, 120, 144, 189, 199, 200, 201, 225],
  [108, 109, 111, 112, 144, 145, 147, 148, 189, 190, 192, 193, 225, 226, 228, 229],
  [76, 77, 79, 80, 157, 158, 160, 161, 211, 212, 214, 215, 229, 230, 232, 233],
  [80, 161, 215, 233, 239, 240, 241],
  [76, 157, 211, 229, 237, 239, 241],
  [80, 161, 215, 224, 239, 240, 241],
  [78, 80, 159, 161, 213, 215, 222, 224, 234, 236],
  [234, 237, 240],
  [220, 229, 238],
  [],
  [219, 220, 228, 229, 237, 238],
  [79, 80, 160, 161, 187, 188, 223, 224, 238, 239],
  [80, 161, 188, 224, 236, 240, 241],
  [235, 238, 241],
  [62, 80, 143, 161, 170, 188, 218, 222, 223, 236, 240, 241],
  [54, 56, 60, 62, 72, 74, 78, 80, 135, 137, 141, 143, 153, 155, 159, 161, 162, 164, 168, 170, 180, 182, 186, 188],
  [54, 72, 135, 153, 162, 180, 217, 218, 222, 235, 236, 240],
  [217, 220, 223],
  [54, 135, 162, 217, 218, 222, 234],
  [54, 55, 135, 136, 162, 163, 219, 220, 234, 235],
  [],
  [],
  [],
  [],
  [162, 164, 189, 191, 216, 218],
  [162, 189, 216],
  [166, 193, 220],
  [162, 189, 216],
  [162, 163, 165, 166, 189, 190, 192, 193, 216, 217, 219, 220],
  [40, 41, 43, 44, 130, 131, 133, 134, 148, 149, 151, 152, 202, 203, 205, 206],
  [44, 122, 123, 124, 134, 152, 206],
  [40, 120, 122, 124, 130, 148, 202],
  [116, 125, 134],
  [114, 116, 123, 125, 132, 134],
  [],
  [40, 112, 120, 122, 124, 148, 202],
  [117, 120, 123],
  [39, 40, 111, 112, 117, 118, 147, 148, 201, 202],
  [],
  [],
  [],
  [89, 116, 143],
  [81, 83, 87, 89, 108, 110, 114, 116, 135, 137, 141, 143],
  [81, 108, 135],
  [],
  [81, 108, 135],
  [81, 82, 108, 109, 135, 136],
  [40, 41, 94, 95, 112, 113, 124, 125, 202, 203],
  [119, 122, 125],
  [40, 94, 112, 118, 120, 122, 202],
  [110, 113, 116],
  [27, 29, 81, 83, 114, 116, 117, 119, 189, 191],
  [27, 81, 109, 110, 111, 117, 189],
  [31, 40, 85, 94, 109, 111, 113, 118, 120, 122, 193, 202],
  [27, 36, 81, 90, 109, 110, 111, 118, 119, 120, 189, 198],
  [27, 28, 30, 31, 36, 37, 39, 40, 81, 82, 84, 85, 90, 91, 93, 94, 189, 190, 192, 193, 198, 199, 201, 202],
  [67, 68, 70, 71, 76, 77, 79, 80, 148, 149, 151, 152, 157, 158, 160, 161, 202, 203, 205, 206, 211, 212, 214, 215],
  [71, 80, 152, 161, 206, 215, 230, 231, 232, 239, 240, 241],
  [67, 76, 148, 157, 202, 211, 228, 230, 232, 237, 239, 241],
  [80, 161, 215, 233, 239, 240, 241],
  [78, 80, 159, 161, 213, 215, 231, 233, 234, 236],
  [234, 237, 240],
  [67, 148, 202, 228, 230, 232, 238],
  [225, 228, 231],
  [66, 67, 147, 148, 201, 202, 225, 226, 237, 238],
  [79, 80, 160, 161, 187, 188, 232, 233, 238, 239],
  [80, 161, 188, 233, 236, 240, 241],
  [235, 238, 241],
  [80, 161, 188, 224, 236, 240, 241],
  [72, 74, 78, 80, 153, 155, 159, 161, 180, 182, 186, 188, 216, 218, 222, 224],
  [72, 153, 180, 216, 235, 236, 240],
  [],
  [216, 225, 234],
  [216, 217, 225, 226, 234, 235],
  [175, 176, 202, 203, 229, 230],
  [],
  [175, 202, 229],
  [],
  [],
  [],
  [175, 202, 229],
  [171, 198, 225],
  [171, 172, 174, 175, 198, 199, 201, 202, 225, 226, 228, 229],
  [22, 23, 25, 26, 67, 68, 70, 71, 184, 185, 187, 188, 229, 230, 232, 233],
  [26, 71, 77, 78, 79, 188, 233, 239, 240, 241],
  [22, 67, 75, 77, 79, 184, 229, 237, 239, 241],
  [26, 62, 77, 78, 79, 188, 224, 239, 240, 241],
  [24, 26, 60, 62, 72, 74, 186, 188, 222, 224, 234, 236],
  [72, 75, 78, 234, 237, 240],
  [58, 67, 76, 220, 229, 238],
  [],
  [57, 58, 66, 67, 75, 76, 219, 220, 228, 229, 237, 238],
  [7, 8, 22, 23, 61, 62, 76, 77, 169, 170, 184, 185, 223, 224, 238, 239],
  [8, 20, 24, 25, 62, 74, 78, 79, 170, 182, 186, 187, 224, 236, 240, 241],
  [19, 22, 25, 73, 76, 79, 181, 184, 187, 235, 238, 241],
  [2, 6, 7, 20, 24, 25, 56, 60, 61, 74, 78, 79, 164, 168, 169, 182, 186, 187, 218, 222, 223, 236, 240, 241],
  [],
  [1, 2, 6, 19, 20, 24, 55, 56, 60, 73, 74, 78, 163, 164, 168, 181, 182, 186, 217, 218, 222, 235, 236, 240],
  [1, 4, 7, 55, 58, 61, 163, 166, 169, 217, 220, 223],
  [1, 2, 6, 18, 55, 56, 60, 72, 163, 164, 168, 180, 217, 218, 222, 234],
  [3, 4, 18, 19, 57, 58, 72, 73, 165, 166, 180, 181, 219, 220, 234, 235],
  [4, 5, 13, 14, 22, 23, 166, 167, 175, 176, 184, 185],
  [],
  [4, 13, 22, 166, 175, 184],
  [2, 5, 8, 164, 167, 170],
  [6, 8, 18, 20, 54, 56, 168, 170, 180, 182, 216, 218],
  [1, 2, 3, 18, 54, 163, 164, 165, 180, 216],
  [1, 3, 5, 13, 58, 163, 165, 167, 175, 220],
  [1, 2, 3, 9, 54, 163, 164, 165, 171, 216],
  [9, 10, 12, 13, 54, 55, 57, 58, 171, 172, 174, 175, 216, 217, 219, 220],
  [13, 14, 16, 17, 40, 41, 43, 44, 67, 68, 70, 71],
  [17, 44, 71],
  [13, 40, 67],
  [],
  [],
  [],
  [13, 40, 67],
  [],
  [12, 13, 39, 40, 66, 67],
  [7, 8, 16, 17, 25, 26],
  [8, 17, 26],
  [],
  [2, 6, 7, 26, 62, 89, 170],
  [18, 20, 24, 26, 54, 56, 60, 62, 81, 83, 87, 89, 162, 164, 168, 170],
  [1, 2, 6, 18, 54, 81, 162],
  [1, 4, 7],
  [1, 2, 6, 9, 54, 81, 162],
  [3, 4, 9, 10, 54, 55, 81, 82, 162, 163],
  [4, 5, 16, 17, 40, 41, 94, 95, 175, 176],
  [11, 14, 17],
  [4, 10, 12, 14, 40, 94, 175],
  [2, 5, 8],
  [6, 8, 9, 11, 27, 29, 81, 83, 162, 164],
  [1, 2, 3, 9, 27, 81, 162],
  [1, 3, 5, 10, 12, 14, 31, 40, 85, 94, 166, 175],
  [1, 2, 3, 10, 11, 12, 27, 36, 81, 90, 162, 171],
  [27, 28, 30, 31, 36, 37, 39, 40, 81, 82, 84, 85, 90, 91, 93, 94, 162, 163, 165, 166, 171, 172, 174, 175],
  [40, 41, 43, 44, 49, 50, 52, 53, 148, 149, 151, 152, 157, 158, 160, 161, 202, 203, 205, 206, 211, 212, 214, 215],
  [44, 53, 122, 123, 124, 131, 132, 133, 152, 161, 206, 215],
  [40, 49, 120, 122, 124, 129, 131, 133, 148, 157, 202, 211],
  [53, 125, 131, 132, 133, 161, 215],
  [51, 53, 123, 125, 126, 128, 159, 161, 213, 215],
  [126, 129, 132],
  [40, 120, 122, 124, 130, 148, 202],
  [117, 120, 123],
  [39, 40, 117, 118, 129, 130, 147, 148, 201, 202],
  [106, 107, 133, 134, 160, 161],
  [107, 134, 161],
  [],
  [107, 134, 161],
  [99, 101, 105, 107, 126, 128, 132, 134, 153, 155, 159, 161],
  [99, 126, 153],
  [],
  [],
  [],
  [40, 41, 94, 95, 124, 125, 130, 131, 202, 203],
  [119, 122, 125],
  [40, 94, 118, 120, 122, 130, 202],
  [],
  [108, 110, 117, 119, 126, 128],
  [108, 117, 126],
  [40, 94, 112, 118, 120, 122, 202],
  [36, 90, 108, 118, 119, 120, 198],
  [36, 37, 39, 40, 90, 91, 93, 94, 108, 109, 111, 112, 198, 199, 201, 202],
  [22, 23, 25, 26, 49, 50, 52, 53, 76, 77, 79, 80],
  [26, 53, 80],
  [22, 49, 76],
  [26, 53, 80],
  [24, 26, 51, 53, 78, 80],
  [],
  [],
  [],
  [],
  [7, 8, 22, 23, 79, 80, 106, 107, 187, 188],
  [8, 20, 24, 25, 80, 107, 188],
  [19, 22, 25],
  [2, 6, 7, 20, 24, 25, 62, 80, 89, 107, 170, 188],
  [54, 56, 60, 62, 72, 74, 78, 80, 81, 83, 87, 89, 99, 101, 105, 107, 162, 164, 168, 170, 180, 182, 186, 188],
  [1, 2, 6, 19, 20, 24, 54, 72, 81, 99, 162, 180],
  [1, 4, 7],
  [1, 2, 6, 18, 54, 81, 162],
  [3, 4, 18, 19, 54, 55, 81, 82, 162, 163],
  [4, 5, 13, 14, 22, 23],
  [],
  [4, 13, 22],
  [2, 5, 8],
  [6, 8, 18, 20, 27, 29, 81, 83, 162, 164],
  [1, 2, 3, 18, 27, 81, 162],
  [1, 3, 5, 13, 31, 85, 166],
  [1, 2, 3, 9, 27, 81, 162],
  [9, 10, 12, 13, 27, 28, 30, 31, 81, 82, 84, 85, 162, 163, 165, 166],
  [13, 14, 16, 17, 49, 50, 52, 53, 94, 95, 97, 98, 130, 131, 133, 134],
  [17, 41, 42, 43, 53, 98, 122, 123, 124, 134],
  [13, 39, 41, 43, 49, 94, 120, 122, 124, 130],
  [35, 44, 53, 116, 125, 134],
  [33, 35, 42, 44, 51, 53, 114, 116, 123, 125, 132, 134],
  [],
  [13, 31, 39, 41, 43, 94, 112, 120, 122, 124],
  [36, 39, 42, 117, 120, 123],
  [12, 13, 30, 31, 36, 37, 93, 94, 111, 112, 117, 118],
  [7, 8, 16, 17, 25, 26, 88, 89, 97, 98, 106, 107],
  [8, 17, 26, 89, 98, 107],
  [],
  [2, 6, 7, 26, 35, 83, 87, 88, 107, 116],
  [18, 20, 24, 26, 27, 29, 33, 35, 99, 101, 105, 107, 108, 110, 114, 116],
  [1, 2, 6, 18, 27, 82, 83, 87, 99, 108],
  [1, 4, 7, 82, 85, 88],
  [1, 2, 6, 9, 27, 82, 83, 87, 90, 108],
  [3, 4, 9, 10, 27, 28, 84, 85, 90, 91, 108, 109],
  [4, 5, 16, 17, 31, 32, 43, 44, 85, 86, 97, 98, 112, 113, 124, 125],
  [11, 14, 17, 38, 41, 44, 92, 95, 98, 119, 122, 125],
  [4, 10, 12, 14, 31, 37, 39, 41, 85, 91, 93, 95, 112, 118, 120, 122],
  [2, 5, 8, 29, 32, 35, 83, 86, 89, 110, 113, 116],
  [6, 8, 9, 11, 33, 35, 36, 38, 87, 89, 90, 92, 114, 116, 117, 119],
  [1, 2, 3, 9, 28, 29, 30, 36, 82, 83, 84, 90, 109, 110, 111, 117],
  [1, 3, 5, 10, 12, 14, 28, 30, 32, 37, 39, 41, 82, 84, 86, 91, 93, 95, 109, 111, 113, 118, 120, 122],
  [1, 2, 3, 10, 11, 12, 28, 29, 30, 37, 38, 39, 82, 83, 84, 91, 92, 93, 109, 110, 111, 118, 119, 120],
  []]

private theorem moves_one_filter (p : Column) :
    movesOne p = (List.finRange 243).filter (fun q => decide (cost p q = 1)) := by
  have checked : ∀ (block : Fin 27) (offset : Fin 9),
      let col := finProdFinEquiv (block, offset)
      movesOne col = (List.finRange 243).filter (fun q => decide (cost col q = 1)) := by
    intro block; simp only [cost_countCut]
    fin_cases block <;> decide +kernel
  obtain ⟨⟨block, offset⟩, rfl⟩ := (finProdFinEquiv (m := 27) (n := 9)).surjective p
  exact checked block offset

theorem weighted_indicator_sum {S R : Type*} [Fintype S] [AddCommMonoid R] [Mul R] [One R]
    (P : S → Prop) [DecidablePred P] (L : List S) (nodup : L.Nodup)
    (mem : ∀ q, q ∈ L ↔ P q) (w : S → R) (zeroLeft : ∀ q ∉ L, (0 : R) * w q = 0) :
    dotProduct (fun q => if P q then (1 : R) else 0) w =
      (L.map (fun q => (1 : R) * w q)).sum := by
  classical
  calc
    _ = ∑ q : S, if q ∈ L then (1 : R) * w q else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : q ∈ L
      · rw [if_pos h, if_pos ((mem q).mp h)]
      · rw [if_neg h, if_neg (fun hP => h ((mem q).mpr hP)), zeroLeft q h]
    _ = _ := by
      simp_rw [← List.mem_toFinset]
      rw [Finset.sum_ite_mem_eq, List.sum_toFinset _ nodup]

theorem step_one {R : Type*} [AddCommMonoid R] [Mul R] [One R]
    (w : Column → R) (p : Column)
    (zeroLeft : ∀ q : Column, q ∉ movesOne p → (0 : R) * w q = 0) :
    dotProduct (oneDefect p) w = ((movesOne p).map (fun q => (1 : R) * w q)).sum :=
  weighted_indicator_sum (fun q => cost p q = 1) (movesOne p)
    (by rw [moves_one_filter]; exact (List.nodup_finRange _).filter _)
    (fun q => by rw [moves_one_filter]; simp) w zeroLeft

def weights (n : Fin 23) : Fin 12 → ℤ :=
  if h : n.val < 12 then (1 : Matrix (Fin 12) (Fin 12) ℤ) (n.castLT h)
  else if hn : n.val = 12 then Fin.append (0 : Fin 2 → ℤ) HardinA233178Chromatic.coefficients
  else
    let later : Fin 10 → Fin 12 → ℤ := ![
  ![0, 0, -216, 396, 1224, -2892, 44, 2595, -561, -745, 89, 67],
  ![0, 0, -2412, 4608, 13260, -33214, 3339, 27983, -8326, -7060, 1332, 491],
  ![0, 0, -17676, 32940, 98880, -239114, 12449, 208086, -52050, -55953, 8161, 4278],
  ![0, 0, -154008, 290340, 854316, -2100012, 158740, 1796375, -489228, -467016, 76665, 33829],
  ![0, 0, -1217844, 2281680, 6785508, -16533790, 1046085, 14265433, -3717752, -3770641, 581683, 279639],
  ![0, 0, -10067004, 18916164, 55972368, -136948938, 9472637, 117655548, -31315724, -30842735, 4898168, 2259517],
  ![0, 0, -81342612, 152618220, 452743428, -1105419370, 73186143, 951691226, -250645723, -250488873, 39202292, 18455270],
  ![0, 0, -664389720, 1247436828, 3696030060, -9033265352, 610920740, 7769033733, -2056517784, -2040806913, 321624497, 149933912],
  ![0, 0, -5397620832, 10130851944, 30034747932, -73370000708, 4910588464, 63133362044, -16670193923, -16600107248, 2607144359, 1221227969],
  ![0, 0, -43964206884, 82530792936, 244606621992, -597676428134, 40204200409, 514162651537, -135926796903, -135129306916, 21257959791, 9934512173]]
    later (n.subNat 13 (Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm hn)))

private theorem weights_initial (i j : Fin 12) :
    weights (i.castAdd 11) j = if i = j then 1 else 0 := by
  simp only [weights, Fin.val_castAdd, dite_eq_left i.isLt, Fin.castLT_castAdd, Matrix.one_apply]

private theorem weights_step : ∀ (n : Fin 23) (hn : 12 ≤ n.val) (j : Fin 12),
    weights n j =
      ∑ k : Fin 10, HardinA233178Chromatic.coefficients k *
        weights ((Fin.natAdd (n.val - 10) k).castLE
          ((Nat.sub_add_cancel ((Nat.le_add_right 10 2).trans hn)).trans_le
            (Nat.le_of_lt n.isLt))) j := by
  decide +kernel

def zeroValues (n : Fin 23) (p : Column) : ℤ :=
  if h : n.val < 12 then table (n.castLT h) p
  else ∑ j : Fin 12, weights n j * table j p

theorem weight_eq (i : Fin 23) :
    zeroValues i = ∑ j : Fin 12, weights i j • table j := by
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold zeroValues; split_ifs with hi
  · have hi' (j : Fin 12) : weights i j =
        if i.castLT hi = j then 1 else 0 := by
      simpa only [Fin.castAdd_castLT] using weights_initial (i.castLT hi) j
    simp_rw [hi', ite_mul, one_mul, zero_mul]; simp
  · rfl

theorem zero_values (n : Fin 23) :
    zeroValues n = (T ^ n.val).mulVec (1 : Column → ℤ) := by
  have reconstruct (m : ℕ) (hm : m < 23) :
      zeroValues ⟨m, hm⟩ = (T ^ m).mulVec (1 : Column → ℤ) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hsmall : m < 12
      · let i : Fin 23 := ⟨m, hm⟩
        change zeroValues i = (T ^ i.val).mulVec (1 : Column → ℤ)
        funext p
        simp only [zeroValues, dite_eq_left (show i.val < 12 from hsmall)]
        exact congrFun (powers_table (i.castLT hsmall)).symm p
      · have large : 12 ≤ m := Nat.le_of_not_gt hsmall
        have relation : (T ^ m).mulVec (1 : Column → ℤ) =
            ∑ k : Fin 10, HardinA233178Chromatic.coefficients k •
              (T ^ (m - 10 + k.val)).mulVec (1 : Column → ℤ) := by
          have hbound : 11 ≤ m := (Nat.le_succ 11).trans large
          have h₁ : m - 11 + 1 + 10 = m := Nat.sub_add_cancel hbound
          have h₂ (k : Fin 10) : m - 11 + 1 + k.val = m - 10 + k.val :=
            congrArg (· + k.val) (Nat.sub_add_sub_cancel hbound (Nat.le_succ 10))
          refine dotProduct_eq _ _ fun v => ?_
          have shifted := TransferMatrix.scalarRelationShift T v 10 1
            HardinA233178Chromatic.coefficients HardinA233178Chromatic.vector_certificate (m - 11)
          simpa only [dotProduct_comm _ v, dotProduct_sum, dotProduct_smul, smul_eq_mul, h₁, h₂]
            using shifted
        rw [relation]
        have prior (k : Fin 10) : m - 10 + k.val < m := by
          simpa only [Fin.val_natAdd, Nat.sub_add_cancel ((Nat.le_add_right 10 2).trans large)]
            using (Fin.natAdd (m - 10) k).isLt
        have earlier (k : Fin 10) := (ih _ (prior k) ((prior k).trans hm)).symm
        simp_rw [earlier, weight_eq, weights_step ⟨m, hm⟩ large, Finset.sum_smul, Finset.smul_sum]
        rw [Finset.sum_comm]; simp only [mul_smul]; rfl
  exact reconstruct n.val n.isLt

def classIndex (p : Column) : Fin 25 :=
  let c := columnEquiv p
  let reversalClass : Fin 41 → Fin 25 :=
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 9, 10, 11, 12, 2, 13, 14, 15, 6, 16, 17, 18, 11, 8, 13, 19, 20, 1, 21, 22, 14, 9, 10, 23, 18, 24, 7, 16, 22, 19, 4]
  reversalClass (HardinA233260Literal.cls (c 0, c 1, c 2, c 3, c 4))

private def oneAtWidthOne : Fin 25 → ℤ :=
  ![0, 24, 16, 16, 12, 12, 10, 6, 10, 10, 0, 6, 12, 7, 7, 7, 3, 3, 0, 3, 12, 12, 3, 0, 0]

def tableOne (n : Fin 23) (p : Column) : ℤ :=
  let values : Fin 23 → Fin 25 → ℤ := ![
  0,
  oneAtWidthOne,
  ![394, 159, 106, 140, 23, 99, 67, 20, 65, 49, 0, 18, 20, 44, 42, 44, 16, 16, 0, 16, 60, 68, 2, 0, 0],
  ![3518, 1936, 1428, 1447, 177, 1312, 1008, 209, 968, 398, 0, 140, 150, 820, 415, 820, 133, 130, 0, 133, 1029, 700, 10, 0, 0],
  ![43786, 18242, 12639, 14053, 1368, 11943, 8780, 1497, 8534, 3426, 0, 1005, 1080, 6826, 3400, 6826, 1023, 930, 0, 1023, 8772, 5870, 75, 0, 0],
  ![418950, 178008, 126707, 139617, 10942, 121178, 90287, 12935, 87949, 30507, 0, 8528, 9068, 71134, 30902, 71134, 8467, 7988, 0, 8467, 89305, 53816, 540, 0, 0],
  ![4175942, 1662548, 1161266, 1312556, 89110, 1112139, 822142, 102249, 804373, 275095, 0, 67208, 71742, 640072, 272678, 640072, 68060, 62674, 0, 68060, 807954, 482682, 4534, 0, 0],
  ![39084042, 15348998, 10780221, 12299376, 722249, 10380376, 7688268, 843623, 7538529, 2444163, 0, 554359, 590230, 5979842, 2410406, 5979842, 556496, 518488, 0, 556496, 7488055, 4302324, 35871, 0, 0],
  ![364405566, 139509622, 97429112, 112450054, 5884702, 93913265, 69417645, 6819874, 68218893, 21702012, 0, 4477385, 4772500, 53747856, 21172736, 53747856, 4516740, 4182270, 0, 4516740, 67289848, 38163202, 295115, 0, 0],
  ![3321805798, 1254655252, 876535067, 1019622552, 47846974, 847007162, 626125817, 55679170, 616290660, 190816833, 0, 36563740, 38949990, 483800592, 184897980, 483800592, 36801069, 34177490, 0, 36801069, 603689341, 335618470, 2386250, 0, 0],
  ![30020725546, 11180597837, 7794443980, 9131081020, 389528395, 7540631521, 5569982596, 452422902, 5490253640, 1671425784, 0, 297034941, 316509936, 4293234798, 1608275623, 4293234798, 299312170, 277559946, 0, 299312170, 5350673560, 2938991300, 19474995, 0, 0],
  ![268248906334, 98883665182, 68894295681, 81167712514, 3169392631, 66745238720, 49290872006, 3684666109, 48640786353, 14554663119, 0, 2419349062, 2577604030, 37927255328, 13925323690, 37927255328, 2436542776, 2261094094, 0, 2436542776, 47184229835, 25589553286, 158254968, 0, 0],
  ![2379429608690, 868988917681, 604781789809, 716035691114, 25795488574, 586494737499, 432950553768, 29975540774, 427664907031, 126255727581, 0, 19680918055, 20969720070, 332590262820, 120169518810, 332590262820, 19826243403, 18392116040, 0, 19826243403, 413288408342, 221946921580, 1288802015, 0, 0],
  ![20955654523594, 7594813700504, 5282195445750, 6280136681698, 209918272267, 5127384493696, 3784121018590, 243989540010, 3741086185035, 1090786329871, 0, 160198835071, 170683695106, 2903064558696, 1033496955375, 2903064558696, 161360378137, 149713975036, 0, 161360378137, 3603169960843, 1917279935714, 10484860035, 0, 0],
  ![183520217434750, 66063392078764, 45914366978823, 54788732346107, 1708391642958, 44603596928281, 32909860163701, 1985460807641, 32559710892006, 9393183577613, 0, 1303599933365, 1388941780918, 25217038520178, 8863466676131, 25217038520178, 1313136985298, 1218258085812, 0, 1313136985298, 31268773110022, 16508675266450, 85341847553, 0, 0],
  ![1599031655904778, 572264276172538, 397503390803852, 475853370589659, 13903045973779, 386431051992674, 285062130045437, 16158714524903, 282212250839177, 80639580983939, 0, 10609434130173, 11303905020632, 218200342645910, 75813239580587, 218200342645910, 10686717064143, 9914963239714, 0, 10686717064143, 270327394699931, 141711515921460, 694470890459, 0, 0],
  ![13872363934872878, 4939017283568565, 3428900867408587, 4116397301918229, 113146127906889, 3335457394334195, 2460022657682043, 131499902138816, 2436831008753485, 690427865875628, 0, 86339522268788, 91991474779104, 1881264013953468, 646951090399550, 1881264013953468, 86969778026686, 80687569758472, 0, 86969778026686, 2328918659033030, 1213214611040628, 5651952510316, 0, 0],
  ![119885740537524650, 42488108940833754, 29483799633366368, 35484659757069457, 920801363853635, 28696360971941052, 21161107417472929, 1070180649882489, 20972364864490043, 5896814086146283, 0, 702654576980016, 748650314369568, 16169225473308940, 5508835708988271, 16169225473308940, 707778534436823, 656658839590464, 0, 707778534436823, 20002946058260771, 10361012578386078, 45995737389552, 0, 0],
  ![1032545610428236790, 364441089889073508, 252791230242824758, 304930337638019447, 7493658705721735, 246162684900721461, 181496287788010914, 8709283518715242, 179960285047972687, 50251993423679261, 0, 5718299948745194, 6092625105929978, 138578005277635020, 46816521715408520, 138578005277635020, 5760020131966471, 5343974791560410, 0, 5760020131966471, 171329265792586382, 88289068639256630, 374325157184784, 0, 0],
  ![8866020076332504642, 3117786739329982580, 2161816827371553317, 2613015782411007535, 60984721293344694, 2106083056125597808, 1552608827769857030, 70877899065565413, 1540108484577589540, 427372269026272473, 0, 46536688412796579, 49583000965761568, 1184666714838352412, 397151312352752566, 1184666714838352412, 46876134000074101, 43490375859831590, 0, 46876134000074101, 1463829135932979533, 750812248845673542, 3046312552964989, 0, 0],
  ![75921211471652238446, 26609302287534417243, 18444124212244894493, 22334825262500204114, 496304916003785566, 17975978141911871381, 13250287069561882769, 576816601887330547, 13148557289494858799, 3627882776249402820, 0, 378723561652006232, 403515062134887016, 10104009126545963924, 3363526004050311686, 10104009126545963924, 381486351248276613, 353932061169125448, 0, 381486351248276613, 12478649154929251514, 6373119946931497924, 24791500482880784, 0, 0],
  ![648524116781607535898, 226611628256855444624, 157026254757364359330, 190469829594160490734, 4039019192146819734, 153097834565455632800, 112837364469212713795, 4694241099480499405, 112009467852274932470, 30743847626057982515, 0, 3082123215533013350, 3283880746600456858, 85996192578520487850, 28442617522997897681, 85996192578520487850, 3104606038258244546, 2880365684465569842, 0, 3104606038258244546, 106157739780009959353, 54004869361530225520, 201757531067443508, 0, 0],
  ![5527354717444740947014, 1926079207513596333341, 1334261539426384884503, 1620920103035625317835, 32870276004176439389, 1301326262935516281405, 959014758017438642304, 38202578771716401467, 952277189103093288231, 260123459691669037637, 0, 25082872438742574753, 26724812812042803182, 730516144556637805268, 240176141740903636934, 730516144556637805268, 25265846730877627768, 23440932065442346324, 0, 25265846730877627768, 901400524224819567128, 456911351416364927544, 1641940373300228429, 0, 0]]
  values n (classIndex p)

private def seedImage (k : Fin 12) (p : Column) : ℤ :=
  let entries : Fin 12 → Fin 25 → ℤ := ![
  oneAtWidthOne,
  ![0, 55, 50, 31, 23, 39, 43, 20, 41, 23, 0, 18, 20, 44, 26, 44, 16, 16, 0, 16, 48, 36, 2, 0, 0],
  ![0, 766, 629, 330, 177, 540, 455, 209, 415, 209, 0, 140, 150, 426, 275, 426, 133, 130, 0, 133, 536, 420, 10, 0, 0],
  ![0, 5178, 4310, 2275, 1368, 3524, 3326, 1497, 3080, 1581, 0, 1005, 1080, 3308, 1953, 3308, 1023, 930, 0, 1023, 3942, 2976, 75, 0, 0],
  ![0, 45978, 37987, 19959, 10942, 32136, 28259, 12935, 25921, 13028, 0, 8528, 9068, 27348, 16849, 27348, 8467, 7988, 0, 8467, 33576, 25710, 540, 0, 0],
  ![0, 360235, 297984, 156041, 89110, 247868, 225184, 102249, 207415, 104971, 0, 67208, 71742, 221122, 133061, 221122, 68060, 62674, 0, 68060, 267826, 203448, 4534, 0, 0],
  ![0, 2985476, 2467909, 1294061, 722249, 2071384, 1849778, 843623, 1700039, 856512, 0, 554359, 590230, 1803900, 1097850, 1803900, 556496, 518488, 0, 556496, 2199974, 1677212, 35871, 0, 0],
  ![0, 24090436, 19916475, 10431526, 5884702, 16643172, 14984605, 6819874, 13785853, 6958473, 0, 4477385, 4772500, 14663814, 8873360, 14663814, 4516740, 4182270, 0, 4516740, 17825430, 13564450, 295115, 0, 0],
  ![0, 196861041, 162740713, 85280626, 47846974, 136292504, 122210629, 55679170, 112375472, 56664767, 0, 36563740, 38949990, 119395026, 72447926, 119395026, 36801069, 34177490, 0, 36801069, 145370510, 110718362, 2386250, 0, 0],
  ![0, 1598932977, 1321825311, 692473816, 389528395, 1105825878, 993521546, 452422902, 913792590, 460986399, 0, 297034941, 316509936, 971429000, 588653071, 971429000, 299312170, 277559946, 0, 299312170, 1181860600, 899746196, 19474995, 0, 0],
  ![0, 13024868022, 10767447298, 5641573587, 3169392631, 9012643940, 8089548623, 3684666109, 7439462970, 3752156315, 0, 2419349062, 2577604030, 7906529782, 4794242670, 7906529782, 2436542776, 2261094094, 0, 2436542776, 9622872768, 7327391246, 158254968, 0, 0],
  ![0, 105949728377, 87587210098, 45887906126, 25795488574, 73294270966, 65817982252, 29975540774, 60532335515, 30533351948, 0, 19680918055, 20969720070, 64341356486, 39001806296, 64341356486, 19826243403, 18392116040, 0, 19826243403, 78294263288, 59611496552, 1288802015, 0, 0]]
  entries k (classIndex p)

private theorem seed_image (k : Fin 12) (p : Column) :
    oneDefect.mulVec (table k) p = seedImage k p := by
  rw [Matrix.mulVec, step_one (table k) p (fun q _ => Int.zero_mul (table k q)), List.sum_map_mul_left, one_mul]
  have checked : ∀ (i : Fin 12) (block : Fin 27) (offset : Fin 9),
      let col := finProdFinEquiv (block, offset)
      ((movesOne col).map (table i)).sum = seedImage i col := by
    intro i block; fin_cases i <;> fin_cases block <;> decide +kernel
  obtain ⟨⟨block, offset⟩, rfl⟩ := (finProdFinEquiv (m := 27) (n := 9)).surjective p
  exact checked k block offset

private theorem weighted_image (k : Fin 23) (p : Column) :
    oneDefect.mulVec (zeroValues k) p = ∑ j : Fin 12, weights k j * seedImage j p := by
  rw [weight_eq k]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, seed_image]

private theorem table_base (p : Column) : tableOne 0 p = 0 := rfl

private theorem table_step (k : Fin 22) (p : Column) :
    tableOne k.succ p = T.mulVec (tableOne k.castSucc) p +
      oneDefect.mulVec (zeroValues k.castSucc) p := by
  rw [step_fast, weighted_image]
  have checked : ∀ (n : Fin 22) (block : Fin 27) (offset : Fin 9),
      let col := finProdFinEquiv (block, offset)
      tableOne n.succ col = ((moves col).map (tableOne n.castSucc)).sum +
        (∑ j : Fin 12, weights n.castSucc j * seedImage j col) := by
    intro n block; fin_cases n <;> fin_cases block <;> decide +kernel
  obtain ⟨⟨block, offset⟩, rfl⟩ := (finProdFinEquiv (m := 27) (n := 9)).surjective p
  exact checked k block offset

theorem table_powers (n : Fin 23) :
    (transfer ^ n.val).mulVec terminal =
      Sum.elim (tableOne n) ((T ^ n.val).mulVec (1 : Column → ℤ)) := by
  apply Fin.induction (n := 22) (motive := fun n =>
    (transfer ^ n.val).mulVec terminal =
      Sum.elim (tableOne n) ((T ^ n.val).mulVec (1 : Column → ℤ))) _ _ n
  · simp only [Fin.val_zero, pow_zero, Matrix.one_mulVec]
    funext p; cases p with
    | inl p => exact (table_base p).symm
    | inr p => rfl
  · intro k ih
    simp only [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec, ← Fin.val_castSucc k]
    rw [ih]
    simp only [transfer, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_mulVec, zero_add]
    funext p; cases p with
    | inl p =>
      exact ((congrArg (fun z => T.mulVec (tableOne k.castSucc) p + oneDefect.mulVec z p)
        (zero_values k.castSucc)).symm.trans (table_step k p).symm)
    | inr p => rfl

def coefficients538 : Fin 20 → ℤ := ![-1296, 5184, 8640, -64656, 43848, 214008, -371692, -48036, 498819, -211910, -256127, 183692, 55115, -59620, -4121, 8804, -123, -566, 26, 12]

private theorem new_polynomial : ∀ p : Column,
    tableOne (Fin.last 22) p = ∑ k : Fin 20, coefficients538 k *
      tableOne ((Fin.natAdd 2 k).castSucc) p := by
  decide +kernel

private theorem inherited_polynomial (p : Column) :
    ((T ^ 22).mulVec (1 : Column → ℤ)) p =
      ∑ k : Fin 20, coefficients538 k * ((T ^ (2 + k.val)).mulVec (1 : Column → ℤ)) p := by
  let f : ℕ → ℤ := fun n => ((T ^ n).mulVec (1 : Column → ℤ)) p
  have factor :
      f 22 - ∑ k : Fin 20, coefficients538 k * f (2 + k.val) =
        ∑ j : Fin 11, Fin.snoc (α := fun _ => ℤ) (fun k => -HardinA233178Chromatic.coefficients k) 1 j *
          (f (1 + j.val + 11) -
            ∑ k : Fin 10, HardinA233178Chromatic.coefficients k * f (1 + j.val + 1 + k.val)) := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    norm_num [Fin.sum_univ_succ, coefficients538, HardinA233178Chromatic.coefficients]; ring
  apply sub_eq_zero.mp
  change f 22 - ∑ k : Fin 20, coefficients538 k * f (2 + k.val) = 0
  rw [factor]
  apply Finset.sum_eq_zero; intro j _
  have shifted := TransferMatrix.scalarRelationShift T (Pi.single p 1) 10 1
    HardinA233178Chromatic.coefficients HardinA233178Chromatic.vector_certificate (1 + j.val)
  have coordinate : f (1 + j.val + 11) =
      ∑ k : Fin 10, HardinA233178Chromatic.coefficients k * f (1 + j.val + 1 + k.val) := by
    simpa only [f, single_one_dotProduct] using shifted
  rw [sub_eq_zero.mpr coordinate, mul_zero]

theorem vector_polynomial :
    (transfer ^ 22).mulVec terminal =
      ∑ k : Fin 20, coefficients538 k • (transfer ^ (2 + k.val)).mulVec terminal := by
  rw [← Fin.val_last 22, table_powers]
  simp_rw [show ∀ k : Fin 20, (transfer ^ (2 + k.val)).mulVec terminal =
    Sum.elim (tableOne ((Fin.natAdd 2 k).castSucc))
      ((T ^ (2 + k.val)).mulVec (1 : Column → ℤ)) from
      fun k => table_powers ((Fin.natAdd 2 k).castSucc)]
  funext p; cases p with
  | inl p => simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl] using new_polynomial p
  | inr p => simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr,
      Fin.val_last] using inherited_polynomial p

end

section

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA233177Canonical (Canonical canonical_pattern_card)
open HardinA233178Chromatic (Column)
open HardinA233178Recurrence (columnEquiv)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects defects literalCount lumped_count)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact-defect arrays for two cuts with canonical row-major colour names. -/
def canonicalCount {k : ℕ} (H V : Finset (Fin k × Fin k)) (D n : ℕ) : ℕ :=
  letI := HardinA229637RowColumn.arrayCanonicalDecidable (n := k) (k := n)
  (Finset.univ.filter fun A : Fin k × Fin n → Fin 3 =>
    defects H V (List.ofFn fun j i => A (i, j)) = D ∧
    (@Canonical (Fin k × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

def a (n : ℕ) : ℕ := canonicalCount ∅ edges 1 n

def residual {C : Type*} (p : C) (d : ℕ) : C ⊕ C :=
    if d = 0 then Sum.inr p else Sum.inl p

theorem transition_entry (p q : Column) (d : ℕ) (s : Column ⊕ Column) :
    (if cost p q ≤ d ∧ residual q (d - cost p q) = s then (1 : ℤ) else 0) -
      (if Sum.elim id id s = q then transfer (residual p d) s else 0) =
    if 1 < d ∧ 0 < cost p q ∧ cost p q ≤ d then
      (if s = residual q (d - cost p q) then 1 else 0) -
        (if cost p q = 1 ∧ s = Sum.inr q then 1 else 0)
    else 0 := by
  have pending (hd : d ≤ 1) (s : Column ⊕ Column) :
      (if cost p q ≤ d ∧ residual q (d - cost p q) = s then (1 : ℤ) else 0) =
        (if Sum.elim id id s = q then transfer (residual p d) s else 0) := by
    have zero := zero_cost_entry p q
    have cutoff : cost p q ≤ 1 ↔ cost p q = 0 ∨ cost p q = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one
    have hd' : d = 0 ∨ d = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hd
    rcases hd' with rfl | rfl <;> rcases s with x | x <;>
      by_cases h₀ : cost p q = 0 <;> by_cases h₁ : cost p q = 1 <;> by_cases hq : x = q <;>
      simp [residual, transfer, oneDefect, ← zero, cutoff, h₀, h₁, hq, @eq_comm _ q x]
  have agree (allowed : d ≤ 1 ∨ cost p q = 0 ∨ d < cost p q) (s : Column ⊕ Column) :
      (if cost p q ≤ d ∧ residual q (d - cost p q) = s then (1 : ℤ) else 0) =
        (if Sum.elim id id s = q then transfer (residual p d) s else 0) := by
    rcases allowed with hd | hz | ht
    · exact pending hd s
    · rcases s with x | x <;> by_cases hq : x = q <;> by_cases hd : d = 0 <;>
        simp [residual, transfer, ← zero_cost_entry, oneDefect, hz, hd, hq, @eq_comm _ q x]
    · by_cases hd : d ≤ 1
      · exact pending hd s
      have hd0 : d ≠ 0 := by omega
      have hc0 : cost p q ≠ 0 := by omega
      have hc1 : cost p q ≠ 1 := by omega
      rcases s with x | x <;> by_cases hq : x = q <;>
        simp [residual, transfer, ← zero_cost_entry, oneDefect, hd0, hc0, hc1,
          Nat.not_le_of_lt ht, hq]
  by_cases allowed : d ≤ 1 ∨ cost p q = 0 ∨ d < cost p q
  · have noDiscrepancy : ¬ (1 < d ∧ 0 < cost p q ∧ cost p q ≤ d) := by
      rcases allowed with hsmall | hzero | hlarge <;> omega
    rw [agree allowed s, sub_self, if_neg noDiscrepancy]
  · have hd : 1 < d := by omega
    have hd0 : d ≠ 0 := by omega
    have hc : 0 < cost p q := by omega
    have hcz : cost p q ≠ 0 := by omega
    have hle : cost p q ≤ d := by omega
    by_cases h1 : cost p q = 1
    · have hres : d - 1 ≠ 0 := by omega
      have hd1 : 1 ≤ d := by omega
      rcases s with x | x <;> by_cases hq : x = q <;>
        simp [residual, transfer, oneDefect, ← zero_cost_entry,
          hd, hd0, hc, hcz, hle, h1, hres, hq, @eq_comm _ q x, hd1]
    · by_cases hres : d - cost p q = 0 <;>
        rcases s with x | x <;> by_cases hq : x = q <;>
        simp [residual, transfer, oneDefect, ← zero_cost_entry,
          hd, hd0, hc, hcz, hle, h1, hres, hq, @eq_comm _ q x]

private theorem transfer_count (n : ℕ) :
    (literalCount (q := 3) ∅ edges 1 (n + 1) : ℤ) =
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ n).mulVec terminal) := by
  let C (p : Column) (r : Fin 5 → Fin 3) : ℕ := bondDefects edges (columnEquiv p) r
  have ctr (p q : Column) : C p (columnEquiv q) = cost p q := rfl
  apply lumped_count ∅ edges columnEquiv.symm C (fun _ d => d ≤ 1) residual transfer
    (Sum.elim (1 : Column → ℤ) 0) terminal 1
  · intro r t; simp [C]
  · intro p d _
    by_cases hd : d = 0 <;> simp [residual, terminal, hd]
  · intro p d hd r _; exact (Nat.sub_le _ _).trans hd
  · intro p d hd s
    rw [← columnEquiv.sum_comp]
    have entry (q : Column) := transition_entry p q d s
    simp only [Nat.not_lt_of_ge hd, false_and, if_false, sub_eq_zero] at entry
    simp_rw [bondDefects_empty, Nat.add_zero, ctr, columnEquiv.symm_apply_apply, entry]
    simp [Finset.sum_ite_eq']
  · intro r _; exact Nat.sub_le _ _
  · intro s
    rw [← columnEquiv.sum_comp]
    simp_rw [bondDefects_empty, Nat.zero_le, Nat.sub_zero, true_and, columnEquiv.symm_apply_apply]
    cases s with
    | inl s => simp [residual, Finset.sum_ite_eq', Finset.sum_ite_eq]
    | inr s => simp [residual]

theorem labelled_scale {k : ℕ} (H V : Finset (Fin k × Fin k)) (D n : ℕ) :
    literalCount (q := 3) H V D n +
      (if k = 0 ∨ n = 0 then (if D = 0 then 5 else 0)
       else if D = H.card + n.pred * (V.card + H.card) then 3 else 0) =
      6 * canonicalCount H V D n := by
  classical
  let C := Fin k × Fin n
  let lo : LinearOrder C := LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
  let P : (C → Fin 3) → Prop := fun A => defects H V (List.ofFn fun i j => A (j, i)) = D
  let K : (C → Fin 3) → Prop := fun A => @Canonical C lo.toLT 3 A
  let s := Finset.univ.filter P
  let t := s.filter K
  let e := Equiv.arrowCongr (Equiv.prodComm (Fin n) (Fin k)) (Equiv.refl (Fin 3))
  have hlabel : literalCount (q := 3) H V D n = s.card := by
    have h := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
      defects H V (List.ofFn fun i j => A (i, j)) = D) (q := P) (fun _ => Iff.rfl))
    simpa only [literalCount, s, Fintype.card_subtype] using h
  have hcanon : canonicalCount H V D n = t.card := by
    unfold canonicalCount
    exact congrArg Finset.card
      (Finset.filter_filter (p := P) (q := K) (Finset.univ : Finset (C → Fin 3))).symm
  rw [hlabel, hcanon]
  by_cases hempty : k = 0 ∨ n = 0
  · letI : IsEmpty C := by
      change IsEmpty (Fin k × Fin n)
      simpa only [isEmpty_prod, Fin.isEmpty_iff] using hempty
    letI : Unique (C → Fin 3) := Pi.uniqueOfIsEmpty _
    have hK (A : C → Fin 3) : K A := fun x => isEmptyElim x
    have ht : t = s := Finset.filter_true_of_mem fun A _ => hK A
    have hP (A : C → Fin 3) : P A ↔ D = 0 := by
      have hA : A = fun _ => 0 := Subsingleton.elim _ _
      rw [hA]
      rcases n with _ | m
      · simp [P, defects, eq_comm]
      · have hk : k = 0 := hempty.resolve_right (Nat.succ_ne_zero _)
        subst k
        change defects H V (List.ofFn fun _ : Fin (m + 1) => fun _ : Fin 0 => (0 : Fin 3)) = D ↔ D = 0
        rw [Finset.eq_empty_of_isEmpty H, Finset.eq_empty_of_isEmpty V]
        rw [List.ofFn_const, DefectTransfer.constant_defects]
        simp only [Finset.card_empty, Nat.add_zero, Nat.mul_zero, eq_comm]
    have hs : s = (Finset.univ : Finset (C → Fin 3)).filter (fun _ => D = 0) := by
      ext A
      simp only [s, Finset.mem_filter, hP]
    rw [ht, hs, Finset.filter_const]
    have hcard : (Finset.univ : Finset (C → Fin 3)).card = 1 := Fintype.card_unique
    by_cases hD : D = 0 <;> simp [hempty, hD, hcard]
  have hk : k ≠ 0 := fun h => hempty (Or.inl h)
  have hn : n ≠ 0 := fun h => hempty (Or.inr h)
  rw [ite_eq_right hempty]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.pred_succ]
  let NC : (C → Fin 3) → Prop := fun A => ∃ x y, A x ≠ A y
  have invariant (perm : Equiv.Perm (Fin 3)) (A : C → Fin 3) :
      (P (perm ∘ A) ∧ NC (perm ∘ A)) ↔ P A ∧ NC A := by
    have hP : P (perm ∘ A) ↔ P A := by
      dsimp [P, Function.comp_apply]
      rw [show (List.ofFn fun i j => perm (A (j, i))) =
        (List.ofFn fun i j => A (j, i)).map (fun r => perm ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    exact and_congr hP (by simp only [NC, Function.comp_apply, ne_eq, perm.injective.eq_iff])
  have horbit : (s.filter NC).card = 6 * (t.filter NC).card := by
    have h := @canonical_pattern_card C inferInstance lo
      (fun A => P A ∧ NC A) invariant (fun _ h => h.2)
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    simpa only [s, t, K, Finset.filter_filter, and_right_comm] using h
  let : Nonempty C := ⟨(0, 0)⟩
  let const : Fin 3 ↪ (C → Fin 3) := ⟨Function.const C, Function.const_injective⟩
  have constant_array (A : C → Fin 3) (h : ¬ NC A) : A = const (A (0, 0)) :=
    funext fun i => Classical.byContradiction fun hi => h ⟨i, (0, 0), hi⟩
  have constant_budget (c : Fin 3) : P (const c) ↔ D = H.card + m * (V.card + H.card) := by
    change defects H V (List.ofFn fun _ : Fin (m + 1) => fun _ : Fin (k + 1) => c) = D ↔ _
    simp only [List.ofFn_const, DefectTransfer.constant_defects, eq_comm]
  have hS : s.filter (fun A => ¬ NC A) =
      if D = H.card + m * (V.card + H.card) then Finset.univ.map const else ∅ := by
    ext A
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hP, hN⟩
      have h := constant_array A hN
      rw [ite_eq_left ((constant_budget _).mp (h ▸ hP)), h]
      exact Finset.mem_map.mpr ⟨A (0, 0), Finset.mem_univ _, rfl⟩
    · by_cases hD : D = H.card + m * (V.card + H.card)
      · rw [ite_eq_left hD, Finset.mem_map]
        rintro ⟨c, _, rfl⟩
        exact ⟨(constant_budget c).mpr hD, fun ⟨_, _, h⟩ => h rfl⟩
      · simp only [ite_eq_right hD, Finset.notMem_empty, false_implies]
  have hzero (c : Fin 3) : K (const c) ↔ c = 0 := by
    constructor
    · intro h
      by_contra hn
      obtain ⟨_, _, he⟩ := h (0, 0) 0 (Fin.pos_iff_ne_zero.mpr hn)
      exact hn he
    · rintro rfl i b hb
      exact (Fin.not_lt_zero b hb).elim
  have hcanonical_constants : (Finset.univ.map const).filter K = {const 0} := by
    rw [Finset.filter_map]
    have h : Finset.univ.filter (K ∘ const) = ({0} : Finset (Fin 3)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Function.comp_apply]
      exact hzero c
    rw [h, Finset.map_singleton]
  have ssplit := Finset.card_filter_add_card_filter_not (s := s) NC
  have tsplit := Finset.card_filter_add_card_filter_not (s := t) NC
  have hT : t.filter (fun A => ¬ NC A) = (s.filter fun A => ¬ NC A).filter K :=
    Finset.filter_comm K (fun A => ¬ NC A) s
  rw [← ssplit, ← tsplit, horbit, hT, hS]
  by_cases hD : D = H.card + m * (V.card + H.card)
  · simp only [ite_eq_left hD, Finset.card_map, Finset.card_univ, Fintype.card_fin,
      hcanonical_constants, Finset.card_singleton]
    omega
  · simp only [ite_eq_right hD, Finset.filter_empty, Finset.card_empty, Nat.add_zero]

attribute [local irreducible] a

/-- Hardin's order-twenty recurrence, starting at width twenty-three. -/
theorem result (n : ℕ) :
    (a (n + 23) : ℤ) = 12 * (a (n + 22) : ℤ) + 26 * (a (n + 21) : ℤ) - 566 * (a (n + 20) : ℤ) -
      123 * (a (n + 19) : ℤ) + 8804 * (a (n + 18) : ℤ) - 4121 * (a (n + 17) : ℤ) -
      59620 * (a (n + 16) : ℤ) + 55115 * (a (n + 15) : ℤ) + 183692 * (a (n + 14) : ℤ) -
      256127 * (a (n + 13) : ℤ) - 211910 * (a (n + 12) : ℤ) + 498819 * (a (n + 11) : ℤ) -
      48036 * (a (n + 10) : ℤ) - 371692 * (a (n + 9) : ℤ) + 214008 * (a (n + 8) : ℤ) +
      43848 * (a (n + 7) : ℤ) - 64656 * (a (n + 6) : ℤ) + 8640 * (a (n + 5) : ℤ) +
      5184 * (a (n + 4) : ℤ) - 1296 * (a (n + 3) : ℤ) := by
  have bridge (m : ℕ) :
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ m).mulVec terminal) =
        6 * (a (m + 1) : ℤ) := by
    rw [← transfer_count]
    have hD := (cut_total_exclusion 1).mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by decide)) m
    have hscale : literalCount (q := 3) ∅ edges 1 (m + 1) = 6 * a (m + 1) := by
      simpa only [Finset.card_empty, Nat.zero_add, Nat.add_zero, Nat.pred_succ, Nat.succ_ne_zero,
        or_self, ite_false, ite_eq_right hD, a] using labelled_scale ∅ edges 1 (m + 1)
    rw [hscale]
    push_cast
    rfl
  have h := (transfer_readout transfer terminal 20 2 _).mp
    vector_polynomial (Sum.elim (1 : Column → ℤ) 0) n
  simp only [smul_eq_mul] at h
  rw [bridge (n + 2 + 20)] at h
  simp_rw [fun k : Fin 20 => bridge (n + 2 + k.val)] at h
  norm_num [coefficients538, Fin.sum_univ_succ, Nat.add_assoc] at h
  linarith

end

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip
