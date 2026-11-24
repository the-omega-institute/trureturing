/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate
   digest: Parity-triple boundary classes and zero-cost data for six-column strips. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203981Strip.result)
between_six: proof_shape=bind-only; consumers=HardinA203981Strip.scale_count, HardinA203981StripSymmetry.cost_formula
parityRows: proof_shape=bind-only; consumers=HardinA203981StripCertificate.allocated_counts, HardinA203981StripCertificate.exact_cost_split, HardinA203981StripCertificate.initial_counts, HardinA203981StripCertificate.representative_counts, HardinA203981StripSymmetry.boundary_recolor, HardinA203981StripSymmetry.boundary_reflect, HardinA203981StripSymmetry.lift_counts, HardinA203981StripSymmetry.pair_match, HardinA203981StripSymmetry.recolor_match, HardinA229508StripCertificate.representative_counts, HardinA229683StripCertificate.representative_counts, boundary, boundary.eq_1, boundary_at_rep, cls_at_rep, representatives, representatives.eq_1
sorted_pair_mem: proof_shape=bind-only; consumers=pairClassLookup._proof_1
classPair_eq_mapDiagM: proof_shape=bind-only; consumers=sorted_pair_mem
pairClassLookup: proof_shape=bind-only; consumers=pairClass_eq_lookup, pairClass_eq_lookup._proof_1_1
pairClass_eq_lookup: proof_shape=bind-only; consumers=HardinA203981StripSymmetry.boundary_reflect, HardinA203981StripSymmetry.pair_match
classPair: proof_shape=bind-only; consumers=HardinA203981StripCertificate.allocated_counts, HardinA203981StripCertificate.pair_indicator, HardinA203981StripCertificate.pair_indicator._proof_1, HardinA203981StripCertificate.pair_sum, HardinA203981StripCertificate.representative_counts, HardinA203981StripSymmetry.boundary_reflect, HardinA203981StripSymmetry.pair_match, HardinA229508StripCertificate.representative_counts, HardinA229683StripCertificate.representative_counts, boundary_at_rep, classProduct, cls_at_rep, pairClassLookup, pairClassLookup._proof_1, pairClass_eq_lookup, representatives, representatives.eq_1, sorted_pair_mem, sorted_pair_mem._proof_1_1, unordered, unordered.eq_1
pairClass: proof_shape=bind-only; consumers=HardinA203981StripCertificate.allocated_counts, HardinA203981StripCertificate.initial_counts, HardinA203981StripCertificate.pair_indicator, HardinA203981StripCertificate.pair_indicator._proof_1, HardinA203981StripCertificate.pair_sum, HardinA203981StripSymmetry.boundary_recolor, HardinA203981StripSymmetry.boundary_reflect, HardinA203981StripSymmetry.lift_counts, HardinA203981StripSymmetry.pair_match, boundary, boundary.eq_1, boundary_at_rep, pairClass_eq_lookup, pairClass_eq_lookup._proof_1_1
boundary: proof_shape=bind-only; consumers=HardinA203981Strip.counting_bridge, HardinA203981StripCertificate.allocated_counts, HardinA203981StripCertificate.counts, HardinA203981StripCertificate.initial_counts, HardinA203981StripCertificate.representative_counts, HardinA203981StripSymmetry.boundary_recolor, HardinA203981StripSymmetry.boundary_reflect, HardinA203981StripSymmetry.lift_counts, HardinA229508Strip.counting_bridge, HardinA229508StripCertificate.one_counts, HardinA229508StripCertificate.representative_counts, HardinA229508StripCertificate.transition_counts, HardinA229508StripData.cl, HardinA229508StripData.cl.eq_1, HardinA229683Strip.counting_bridge, HardinA229683StripCertificate.cut_inherited, HardinA229683StripCertificate.cut_terminal, HardinA229683StripCertificate.representative_counts, HardinA229683StripCertificate.transition_counts, HardinA229683StripCertificate.transition_counts._simp_1, HardinA229683StripCertificate.two_counts, HardinA229683StripData.cl, HardinA229683StripData.cl.eq_1, boundary.eq_1, boundary_at_rep
representatives: proof_shape=bind-only; consumers=HardinA203981StripCertificate.counts, HardinA203981StripCertificate.representative_counts, HardinA203981StripSymmetry.lift_counts, HardinA203981StripSymmetry.pair_match, HardinA229508StripCertificate.one_counts, HardinA229508StripCertificate.representative_counts, HardinA229683StripCertificate.representative_counts, HardinA229683StripCertificate.two_counts, boundary_at_rep, cls_at_rep, representatives.eq_1
cls_at_rep: proof_shape=bind-only; consumers=HardinA203981StripCertificate.representative_counts, HardinA203981StripSymmetry.pair_match, HardinA229508StripCertificate.representative_counts, HardinA229683StripCertificate.representative_counts, boundary_at_rep
boundary_at_rep: proof_shape=bind-only; consumers=HardinA203981StripCertificate.counts, HardinA229508StripCertificate.one_counts, HardinA229683StripCertificate.two_counts
T: proof_shape=bind-only; consumers=HardinA203981Strip.counting_bridge, HardinA203981Strip.counting_bridge._proof_1_3, HardinA203981Strip.result, HardinA203981StripCertificate.counts, HardinA203981StripCertificate.finite_certificate, HardinA203981StripCertificate.forward_step, HardinA203981StripCertificate.forward_step._proof_1, HardinA203981StripCertificate.forward_step._proof_10, HardinA203981StripCertificate.forward_step._proof_11, HardinA203981StripCertificate.forward_step._proof_12, HardinA203981StripCertificate.forward_step._proof_13, HardinA203981StripCertificate.forward_step._proof_14, HardinA203981StripCertificate.forward_step._proof_15, HardinA203981StripCertificate.forward_step._proof_16, HardinA203981StripCertificate.forward_step._proof_17, HardinA203981StripCertificate.forward_step._proof_18, HardinA203981StripCertificate.forward_step._proof_19, HardinA203981StripCertificate.forward_step._proof_2, HardinA203981StripCertificate.forward_step._proof_20, HardinA203981StripCertificate.forward_step._proof_3, HardinA203981StripCertificate.forward_step._proof_4, HardinA203981StripCertificate.forward_step._proof_5, HardinA203981StripCertificate.forward_step._proof_6, HardinA203981StripCertificate.forward_step._proof_7, HardinA203981StripCertificate.forward_step._proof_8, HardinA203981StripCertificate.forward_step._proof_9, HardinA203981StripCertificate.forward_table, HardinA203981StripCertificate.representative_counts, HardinA229508StripCertificate.finite_certificate, HardinA229508StripCertificate.forward_step, HardinA229508StripCertificate.forward_step._proof_1, HardinA229508StripCertificate.forward_step._proof_10, HardinA229508StripCertificate.forward_step._proof_11, HardinA229508StripCertificate.forward_step._proof_12, HardinA229508StripCertificate.forward_step._proof_13, HardinA229508StripCertificate.forward_step._proof_14, HardinA229508StripCertificate.forward_step._proof_15, HardinA229508StripCertificate.forward_step._proof_16, HardinA229508StripCertificate.forward_step._proof_17, HardinA229508StripCertificate.forward_step._proof_18, HardinA229508StripCertificate.forward_step._proof_19, HardinA229508StripCertificate.forward_step._proof_2, HardinA229508StripCertificate.forward_step._proof_20, HardinA229508StripCertificate.forward_step._proof_3, HardinA229508StripCertificate.forward_step._proof_4, HardinA229508StripCertificate.forward_step._proof_5, HardinA229508StripCertificate.forward_step._proof_6, HardinA229508StripCertificate.forward_step._proof_7, HardinA229508StripCertificate.forward_step._proof_8, HardinA229508StripCertificate.forward_step._proof_9, HardinA229508StripCertificate.forward_zeroth, HardinA229508StripCertificate.inherited_relation, HardinA229508StripCertificate.transition_counts, HardinA229508StripData.T, HardinA229508StripData.T.eq_1, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.forward_two._proof_1, HardinA229683StripCertificate.forward_two._proof_10, HardinA229683StripCertificate.forward_two._proof_11, HardinA229683StripCertificate.forward_two._proof_12, HardinA229683StripCertificate.forward_two._proof_13, HardinA229683StripCertificate.forward_two._proof_14, HardinA229683StripCertificate.forward_two._proof_15, HardinA229683StripCertificate.forward_two._proof_16, HardinA229683StripCertificate.forward_two._proof_17, HardinA229683StripCertificate.forward_two._proof_18, HardinA229683StripCertificate.forward_two._proof_19, HardinA229683StripCertificate.forward_two._proof_2, HardinA229683StripCertificate.forward_two._proof_20, HardinA229683StripCertificate.forward_two._proof_3, HardinA229683StripCertificate.forward_two._proof_4, HardinA229683StripCertificate.forward_two._proof_5, HardinA229683StripCertificate.forward_two._proof_6, HardinA229683StripCertificate.forward_two._proof_7, HardinA229683StripCertificate.forward_two._proof_8, HardinA229683StripCertificate.forward_two._proof_9, HardinA229683StripData.T
initial: proof_shape=bind-only; consumers=HardinA203981Strip.counting_bridge, HardinA203981Strip.counting_bridge._proof_1_3, HardinA203981Strip.result, HardinA203981StripCertificate.finite_certificate, HardinA203981StripCertificate.forward_table, HardinA203981StripCertificate.initial_counts, HardinA229508Strip.counting_bridge, HardinA229508StripCertificate.finite_certificate, HardinA229508StripCertificate.forward_zeroth, HardinA229508StripCertificate.inherited_relation, HardinA229508StripData.initial, HardinA229508StripData.initial.eq_1, HardinA229683Strip.counting_bridge
classProduct: proof_shape=bind-only; consumers=HardinA229508StripData.costOne, HardinA229683StripData.costTwo, T
columnRows: proof_shape=bind-only; consumers=HardinA203981StripCertificate.halfCost, HardinA203981StripCertificate.halfCost.eq_1, HardinA203981StripCertificate.initial_counts, HardinA203981StripCertificate.reverseColumn, HardinA203981StripCertificate.reversed_count, HardinA203981StripCertificate.zero_exact, HardinA229508StripCertificate.one_exact, HardinA229683StripCertificate.two_exact, parityRows
halfZero: proof_shape=bind-only; consumers=HardinA203981StripCertificate.representative_counts, HardinA203981StripCertificate.zero_exact, HardinA229508StripCertificate.representative_counts, HardinA229508StripData.costOne, HardinA229683StripCertificate.representative_counts, HardinA229683StripData.costTwo, T
unordered: proof_shape=bind-only; consumers=HardinA203981StripCertificate.W, HardinA203981StripCertificate.allocated_counts, HardinA203981StripCertificate.initial_counts, HardinA203981StripCertificate.pair_sum, HardinA203981StripCertificate.representative_counts, HardinA229508StripCertificate.W, HardinA229508StripCertificate.representative_counts, HardinA229683StripCertificate.W, HardinA229683StripCertificate.representative_counts, classProduct, initial, unordered.eq_1
halfInitial: proof_shape=bind-only; consumers=HardinA203981StripCertificate.halfForwardZero, HardinA203981StripCertificate.initial_counts, initial
-/

import Init.Data.List.Basic
import Init.Control.State
import Init.Data.List.Find
import Init.Data.List.FinRange
import Init.Data.List.OfFn
import Init.Tactics
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData

open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row)

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer (Col cls Q column)

/-- The diagonal and antidiagonal bonds between rows of width six. -/
theorem between_six :
    StripDefects.HardinA229637RowColumn.betw 6 =
      {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5), (5, 4)} := by
  rw [CrossedStripDefectsWide.P5b.HardinA229635Literal.same_between]
  decide +kernel

/-- Read the three coordinates of a column as a function. -/
def columnRows : Col ≃ Row 3 3 :=
  let e : Col ≃ Row 3 3 := ((Fin.consEquiv (fun _ : Fin 3 => Fin 3)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 3)) (finTwoArrowEquiv (Fin 3)))).symm
  { toFun := column
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- Read the even columns from the left and the odd columns from the right. -/
def parityRows : Row 3 6 ≃ Col × Col :=
  let onGrid := Equiv.arrowCongr (finProdFinEquiv (m := 3) (n := 2)).symm
    (Equiv.refl (Fin 3))
  let toPairPerPosition := (Equiv.curry (Fin 3) (Fin 2) (Fin 3)).trans
    (Equiv.arrowCongr (Equiv.refl (Fin 3)) (finTwoArrowEquiv (Fin 3)))
  let toPairOfTriples := Equiv.arrowProdEquivProdArrow (Fin 3) (fun _ => Fin 3) (fun _ => Fin 3)
  let toColumns := Equiv.prodCongr columnRows.symm
    ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 3))).trans columnRows.symm)
  onGrid.trans (toPairPerPosition.trans (toPairOfTriples.trans toColumns))

/-- The sorted pair of triple classes for each boundary index. -/
def classPair : Fin 15 → Fin 5 × Fin 5 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)]

private theorem classPair_eq_mapDiagM :
    List.ofFn classPair =
      ((List.finRange 5).mapDiagM'
        (m := StateM (List (Fin 5 × Fin 5)))
        (fun a b => modify ((a, b) :: ·)) |>.run []).2.reverse := by
  rfl

private theorem sorted_pair_mem : ∀ x y : Fin 5,
    (min x y, max x y) ∈ List.ofFn classPair := by
  rw [classPair_eq_mapDiagM]
  decide +kernel

private def pairClassLookup (x y : Fin 5) : Fin 15 :=
  ⟨(List.ofFn classPair).idxOf (min x y, max x y),
    by simpa only [List.length_ofFn] using List.idxOf_lt_length_of_mem (sorted_pair_mem x y)⟩

/-- The materialized indexed lookup for two triple patterns. -/
def pairClass : Fin 5 → Fin 5 → Fin 15 :=
  ![![0, 1, 2, 3, 4],
    ![1, 5, 6, 7, 8],
    ![2, 6, 9, 10, 11],
    ![3, 7, 10, 12, 13],
    ![4, 8, 11, 13, 14]]

/-- The table gives the position of the sorted pair in the representative enumeration. -/
theorem pairClass_eq_lookup (x y : Fin 5) :
    (pairClass x y).val = (List.ofFn classPair).idxOf (min x y, max x y) := by
  have eq : ∀ a b : Fin 5, pairClass a b = pairClassLookup a b := by decide +kernel
  exact congrArg Fin.val (eq x y)

/-- Classify the even columns from the left and the odd columns from the right. -/
def boundary (p : Row 3 6) : Fin 15 :=
  pairClass (cls (parityRows p).1) (cls (parityRows p).2)

/-- Interleave the labelled triple representatives. -/
def representatives (i : Fin 15) : Row 3 6 :=
  parityRows.symm
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.representatives (classPair i).1,
     D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.representatives (classPair i).2)

/-- The two parity triples of a representative have the listed classes in order. -/
theorem cls_at_rep (i : Fin 15) :
    cls (parityRows (representatives i)).1 = (classPair i).1 ∧
    cls (parityRows (representatives i)).2 = (classPair i).2 := by
  simp only [representatives, Equiv.apply_symm_apply]
  revert i
  decide +kernel

/-- Reading the boundary class recovers the index of its representative. -/
theorem boundary_at_rep (i : Fin 15) : boundary (representatives i) = i := by
  have lookup : ∀ j : Fin 15, pairClass (classPair j).1 (classPair j).2 = j := by
    decide +kernel
  rw [boundary, (cls_at_rep i).1, (cls_at_rep i).2]
  exact lookup i

/-- Aggregate a labelled pair into an unordered boundary class. -/
def unordered {α : Type*} [Mul α] [Add α] [Zero α] (u v : Fin 5 → α) (j : Fin 15) : α :=
  let (c, d) := classPair j
  u c * v d + if c = d then 0 else u d * v c

/-- The half-strip zero-cost matrix with the target triple reversed. -/
def halfZero : Matrix (Fin 5) (Fin 5) ℤ :=
  Q.submatrix id (Equiv.swap 1 3)

/-- Transfer one class of each parity, then read the unordered target. -/
def classProduct {α : Type*} [Mul α] [Add α] [Zero α]
    (A B : Matrix (Fin 5) (Fin 5) α) (i j : Fin 15) : α :=
  unordered (A (classPair i).1) (B (classPair i).2) j

/-- Multiply the two half-strip counts and include both orders of distinct target classes. -/
def T : Matrix (Fin 15) (Fin 15) ℤ := classProduct halfZero halfZero

/-- The initial class populations for one half-strip. -/
def halfInitial : Fin 5 → ℤ :=
  fun i => D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip.initial (i.castAdd 5)

/-- Numbers of labelled single rows in the fifteen classes. -/
def initial : Fin 15 → ℤ := unordered halfInitial halfInitial

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
