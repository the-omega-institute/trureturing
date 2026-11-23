/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate
   digest: Exact zero-cost transitions and the order-six recurrence certificate. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203981Strip.result)
reverseColumn: proof_shape=bind-only; consumers=halfCost, halfCost.eq_1, reversed_count, reversed_count._proof_1
pair_indicator: proof_shape=bind-only; consumers=pair_sum
representative_counts: proof_shape=bind-only; consumers=counts
counts: proof_shape=bind-only; consumers=HardinA203981Strip.counting_bridge, HardinA229508StripCertificate.transition_counts, HardinA229683StripCertificate.transition_counts
initial_counts: proof_shape=bind-only; consumers=HardinA203981Strip.counting_bridge, HardinA229508Strip.counting_bridge, HardinA229683Strip.counting_bridge
W: proof_shape=bind-only; consumers=HardinA229508StripCertificate.forward_one, HardinA229508StripCertificate.forward_one._proof_1, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.forward_two._proof_1, finite_certificate, finite_certificate._proof_1, forward_table, forward_table._proof_1
coeff: proof_shape=bind-only; consumers=HardinA203981Strip.result, HardinA203981StripCertificate.coeff.eq_1, HardinA229508StripCertificate.inherited_relation, finite_certificate, finite_certificate._proof_1, monicCoeff
monicCoeff: proof_shape=bind-only; consumers=HardinA229508StripCertificate.squareMonicCoeff, HardinA229683StripCertificate.coeff
forward_step: proof_shape=content; consumers=HardinA229508StripCertificate.forward_step, forward_table
forward_table_of_steps: proof_shape=bind-only; consumers=HardinA229508StripCertificate.forward_one, HardinA229683StripCertificate.forward_two, forward_table
forward_table: proof_shape=content; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=HardinA203981Strip.result, HardinA229508StripCertificate.inherited_relation
allocated_counts: proof_shape=bind-only; consumers=representative_counts
allocation_indicator: proof_shape=bind-only; consumers=allocated_counts
exact_cost_split: proof_shape=bind-only; consumers=allocated_counts
halfCost: proof_shape=bind-only; consumers=allocated_counts
pair_sum: proof_shape=bind-only; consumers=allocated_counts
reversed_count: proof_shape=bind-only; consumers=zero_exact
zero_exact: proof_shape=bind-only; consumers=representative_counts
halfForwardZero: proof_shape=bind-only; consumers=W
-/

import Batteries.Data.List.Basic
import Init.Data.List.OfFn
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Prod
import Mathlib.Basic.Logic.Basic
import Init.Omega
import Init.PropLemmas
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Function
import Init.Data.Int.Basic
import Init.Prelude
import Init.SimpLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Iterate
import Init.ByCases
import Init.Core
import Init.Data.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate

open HardinA203981StripData hiding representatives
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA233258PairTransfer (Col cls)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects forward)
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option Elab.async false

private def reverseColumn : Col ≃ Col :=
  columnRows.trans ((Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin 3))
    (Equiv.refl (Fin 3))).trans columnRows.symm)

/-- The defect cost on one parity class, measured in the half-strip orientation. -/
def halfCost (a b : Col) : ℕ :=
  bondDefects HardinA229588Strip.between (columnRows a) (columnRows (reverseColumn b))

private theorem exact_cost_split (p r : Row 3 6) :
    bondDefects (betw 6) p r =
      halfCost (parityRows p).1 (parityRows r).2 + halfCost (parityRows p).2 (parityRows r).1 := by
  change _ =
    bondDefects HardinA229588Strip.between ![p 0, p 2, p 4] ![r 1, r 3, r 5] +
      bondDefects HardinA229588Strip.between ![p 5, p 3, p 1] ![r 4, r 2, r 0]
  rw [HardinA203981StripSymmetry.cost_formula]
  unfold bondDefects
  rw [HardinA229588Strip.between]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  norm_num only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Finset.sum_insert, Finset.sum_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.fst, Prod.snd, Fin.reduceEq,
    and_false, false_and, or_false, false_or, not_false_eq_true, Fin.val_natCast,
    Nat.reduceSub, Nat.reduceMod, Fin.mk_one, Fin.mk_zero]
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    Matrix.cons_val_zero]
  ac_rfl

private theorem pair_indicator : ∀ (j : Fin 15) (x y : Fin 5),
    let c := (classPair j).1
    let d := (classPair j).2
    (if pairClass x y = j then (1 : ℤ) else 0) =
      (if x = d then 1 else 0) * (if y = c then 1 else 0) +
        if c = d then 0 else (if x = c then 1 else 0) * (if y = d then 1 else 0) := by
  decide +kernel

private theorem pair_sum (P R : Col → Prop) [DecidablePred P] [DecidablePred R]
    (j : Fin 15) :
    (∑ x : Col, ∑ y : Col, if (P y ∧ R x) ∧ pairClass (cls x) (cls y) = j
      then (1 : ℤ) else 0) =
      unordered (fun c => ∑ y : Col, if P y ∧ cls y = c then 1 else 0)
        (fun c => ∑ x : Col, if R x ∧ cls x = c then 1 else 0) j := by
  let c := (classPair j).1
  let d := (classPair j).2
  let f (y : Col) (k : Fin 5) : ℤ := if P y ∧ cls y = k then 1 else 0
  let g (x : Col) (k : Fin 5) : ℤ := if R x ∧ cls x = k then 1 else 0
  have entry (x y : Col) :
      (if (P y ∧ R x) ∧ pairClass (cls x) (cls y) = j then (1 : ℤ) else 0) =
        g x d * f y c + if c = d then 0 else g x c * f y d := by
    by_cases hp : P y <;> by_cases hr : R x <;>
      simp only [f, g, hp, hr, true_and, false_and, and_false, if_false, mul_zero,
        zero_mul, zero_add, ite_self]
    exact pair_indicator j (cls x) (cls y)
  simp_rw [entry]
  change _ = (∑ y, f y c) * (∑ x, g x d) +
    if c = d then 0 else (∑ y, f y d) * (∑ x, g x c)
  rw [mul_comm (∑ y, f y c) (∑ x, g x d), mul_comm (∑ y, f y d) (∑ x, g x c)]
  by_cases h : c = d <;>
    simp only [h, if_true, if_false, add_zero, Finset.sum_add_distrib, Fintype.sum_mul_sum]

private theorem allocation_indicator (u v d : ℕ) (P : Prop) [Decidable P] :
    (if u + v = d ∧ P then (1 : ℤ) else 0) =
      ∑ k : Fin (d + 1), if (u = k.val ∧ v = d - k.val) ∧ P then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if (u = k ∧ v = d - k) ∧ P then (1 : ℤ) else 0) (d + 1),
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => if (u = x ∧ v = y) ∧ P then (1 : ℤ) else 0)]
  by_cases h : P
  · simp only [h, and_true, ← Prod.mk.injEq]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

/-- Each full-strip transition is the sum of products for the exact-cost allocations. -/
theorem allocated_counts (d : ℕ) (K : Fin (d + 1) → Matrix (Fin 5) (Fin 5) ℤ)
    (i j : Fin 15)
    (h : ∀ (k : Fin (d + 1)) (a : Col) (c : Fin 5),
      (a = (parityRows (HardinA203981StripData.representatives i)).1 ∨
        a = (parityRows (HardinA203981StripData.representatives i)).2) →
      (c = (classPair j).1 ∨ c = (classPair j).2) →
      (∑ b : Col, if halfCost a b = k.val ∧ cls b = c then (1 : ℤ) else 0) = K k (cls a) c) :
    (∑ r : Row 3 6, if bondDefects (betw 6) (HardinA203981StripData.representatives i) r = d ∧
      boundary r = j then (1 : ℤ) else 0) =
      ∑ k : Fin (d + 1), classProduct (K k) (K k.rev) i j := by
  let p := HardinA203981StripData.representatives i
  let a := (parityRows p).1
  let b := (parityRows p).2
  have hcls : ∀ i : Fin 15,
      cls (parityRows (HardinA203981StripData.representatives i)).1 = (classPair i).1 ∧
      cls (parityRows (HardinA203981StripData.representatives i)).2 = (classPair i).2 := by
    simp only [HardinA203981StripData.representatives, Equiv.apply_symm_apply]
    decide +kernel
  calc
    _ = ∑ t : Col × Col, if bondDefects (betw 6) p (parityRows.symm t) = d ∧
        boundary (parityRows.symm t) = j then (1 : ℤ) else 0 :=
      (parityRows.symm.sum_comp _).symm
    _ = ∑ x : Col, ∑ y : Col, ∑ k : Fin (d + 1),
        if (halfCost a y = k.val ∧ halfCost b x = d - k.val) ∧
          pairClass (cls x) (cls y) = j then (1 : ℤ) else 0 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [exact_cost_split, boundary, Equiv.apply_symm_apply]
      exact allocation_indicator (halfCost a y) (halfCost b x) d (pairClass (cls x) (cls y) = j)
    _ = _ := by
      rw [Finset.sum_comm_cycle]
      apply Finset.sum_congr rfl
      intro k _
      rw [pair_sum (fun y => halfCost a y = k.val) (fun x => halfCost b x = d - k.val)]
      have ha : cls a = (classPair i).1 := (hcls i).1
      have hb : cls b = (classPair i).2 := (hcls i).2
      have first (c : Fin 5) (hc : c = (classPair j).1 ∨ c = (classPair j).2) :
          (∑ y : Col, if halfCost a y = k.val ∧ cls y = c then (1 : ℤ) else 0) = K k (cls a) c :=
        h k a c (Or.inl rfl) hc
      have second (c : Fin 5) (hc : c = (classPair j).1 ∨ c = (classPair j).2) :
          (∑ x : Col, if halfCost b x = d - k.val ∧ cls x = c then (1 : ℤ) else 0) =
            K k.rev (cls b) c := by
        simpa only [Fin.val_rev, Nat.succ_sub_succ_eq_sub] using h k.rev b c (Or.inr rfl) hc
      simp only [classProduct, unordered, first _ (Or.inl rfl), first _ (Or.inr rfl),
        second _ (Or.inl rfl), second _ (Or.inr rfl), ha, hb]

/-- Reverse the target before applying a half-strip class count. -/
theorem reversed_count (n : ℕ) (a : Col) (j : Fin 5) :
    (∑ b : Col, if halfCost a b = n ∧ cls b = j then (1 : ℤ) else 0) =
      ∑ b : Col, if bondDefects HardinA229588Strip.between (columnRows a) (columnRows b) = n ∧
        cls b = Equiv.swap 1 3 j then (1 : ℤ) else 0 := by
  have hrev : ∀ b : Col, cls (reverseColumn b) = Equiv.swap 1 3 (cls b) := by
    decide +kernel
  rw [← reverseColumn.sum_comp (fun b =>
    if halfCost a b = n ∧ cls b = j then (1 : ℤ) else 0)]
  apply Finset.sum_congr rfl
  intro b _
  have hinv : reverseColumn (reverseColumn b) = b := reverseColumn.symm_apply_apply b
  have hclass : cls (reverseColumn b) = j ↔ cls b = Equiv.swap 1 3 j := by
    rw [hrev, Equiv.swap_apply_eq_iff]
  simp only [halfCost, hinv, hclass]

/-- Apply the frozen transition law at budget zero. -/
theorem zero_exact (a : Col) (j : Fin 5) :
    (∑ b : Col, if halfCost a b = 0 ∧ cls b = j then (1 : ℤ) else 0) = halfZero (cls a) j := by
  rw [reversed_count]
  have h := HardinA229588Strip.finite_certificate.2.2.1 (columnRows a) 0
    (show HardinA229588Strip.Valid (columnRows a) 0 from Nat.zero_le 1)
    ((Equiv.swap 1 3 j).natAdd 5)
  rw [← columnRows.sum_comp] at h
  have hh (r : Col) : bondDefects HardinA229588Strip.horizontal (columnRows r) (columnRows r) = 0 := rfl
  have hcol (r : Col) : (columnRows r 0, columnRows r 1, columnRows r 2) = r :=
    columnRows.symm_apply_apply r
  simp only [hh, Nat.add_zero, Fin.val_zero, Nat.le_zero, Nat.zero_sub,
    HardinA229588Strip.cl, Nat.zero_ne_one, ite_false, ite_true, hcol,
    HardinA229588Strip.T, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂] at h
  refine (Finset.sum_congr rfl fun b _ => ?_).trans h
  exact if_congr (and_congr_right' (Fin.natAdd_inj 5).symm) rfl rfl

private theorem representative_counts (i j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) (HardinA203981StripData.representatives i) r = 0 ∧
      boundary r = j then (1 : ℤ) else 0) = T i j := by
  have h := allocated_counts 0 (fun _ => halfZero) i j (fun k a c _ _ => by
    fin_cases k
    exact zero_exact a c)
  rw [Fin.sum_univ_one] at h
  exact h

/-- The exact zero-cost class counts. -/
theorem counts (p : Row 3 6) (j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 0 ∧ boundary r = j
      then (1 : ℤ) else 0) = T (boundary p) j :=
  (HardinA203981StripSymmetry.lift_counts 0 p j).trans (representative_counts (boundary p) j)

/-- The distribution of labelled single rows. -/
theorem initial_counts (j : Fin 15) :
    (∑ r : Row 3 6, if boundary r = j then (1 : ℤ) else 0) = initial j := by
  have half : (fun c : Fin 5 =>
      ∑ r : Col, if True ∧ cls r = c then (1 : ℤ) else 0) = halfInitial := by
    funext c
    have h := HardinA229588Strip.finite_certificate.2.2.2.2.1 (c.castAdd 5)
    rw [← columnRows.sum_comp] at h
    have hh (r : Col) :
        bondDefects HardinA229588Strip.horizontal (columnRows r) (columnRows r) = 0 := rfl
    have hcol (r : Col) : (columnRows r 0, columnRows r 1, columnRows r 2) = r :=
      columnRows.symm_apply_apply r
    simp only [hh, Nat.zero_le, Nat.sub_zero, HardinA229588Strip.cl, ite_true, true_and, hcol] at h
    simp only [true_and]
    refine (Finset.sum_congr rfl fun b _ => ?_).trans h
    exact if_congr Fin.castAdd_inj.symm rfl rfl
  calc
    _ = ∑ p : Col × Col, if boundary (parityRows.symm p) = j then (1 : ℤ) else 0 :=
      (parityRows.symm.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [boundary, Equiv.apply_symm_apply]
      have h := pair_sum (fun _ => True) (fun _ => True) j
      rw [half] at h
      simp only [and_true, true_and] at h
      exact h

set_option maxHeartbeats 0

/-- The half-strip forward vectors in exact-cost degree 0. -/
def halfForwardZero : Fin 21 → Fin 5 → ℤ :=
  Matrix.vecCons halfInitial (Matrix.vecCons HardinA233258PairTransfer.weights
    ![fun j : Fin 5 => HardinA229588Strip.W 2 (j.castAdd 5),
    fun j : Fin 5 => HardinA229588Strip.W 3 ((Equiv.swap 1 3 j).castAdd 5),
    ![2304, 2124, 1512, 2304, 612],
    ![10548, 9648, 6912, 10548, 2736],
    ![48204, 44028, 31644, 48204, 12384],
    ![220284, 201024, 144612, 220284, 56412],
    ![1006488, 918288, 660852, 1006488, 257436],
    ![4598604, 4195188, 3019464, 4598604, 1175724],
    ![21010464, 19166724, 13795812, 21010464, 5370912],
    ![95993928, 87569028, 63031392, 95993928, 24537636],
    ![438582204, 400088448, 287981784, 438582204, 112106664],
    ![2003816844, 1827941724, 1315746612, 2003816844, 512195112],
    ![9155138868, 8351587368, 6011450532, 9155138868, 2340136836],
    ![41828454504, 38157140808, 27465416604, 41828454504, 10691724204],
    ![191107920924, 174334228524, 125485363512, 191107920924, 48848865012],
    ![873143354808, 796506856308, 573323762772, 873143354808, 223183093536],
    ![3989260683504, 3639120014268, 2619430064424, 3989260683504, 1019689949844],
    ![18226332129204, 16626592014624, 11967782050512, 18226332129204, 4658809964112],
    ![83273370452748, 75964398366348, 54678996387612, 83273370452748, 21285401978736]])

/-- Aggregate the half-strip forward vectors in total cost degree 0. -/
def W (i : Fin 21) : Fin 15 → ℤ :=
  unordered (halfForwardZero i) (halfForwardZero i)

/-- Recurrence coefficients in increasing order of the input index. -/
def coeff : Fin 6 → ℤ := ![-6561, 3645, 2025, -963, -45, 25]

/-- The coefficients of the monic polynomial associated to the order-six recurrence. -/
def monicCoeff (n : ℕ) : ℤ :=
  if h : n < 6 then -coeff ⟨n, h⟩ else if n = 6 then 1 else 0

/-- A finite table with the prescribed start and each successive update gives the forward vectors. -/
theorem forward_table_of_steps {s α : Type*} [Fintype s] [NonUnitalNonAssocSemiring α] {n : ℕ}
    (t : Matrix s s α) (v : s → α) (table : Fin (n + 1) → s → α) :
    (∀ i : Fin (n + 1), (fun w => Matrix.vecMul w t)^[i.val] v = table i) ↔
      table 0 = v ∧ ∀ k : Fin n, Matrix.vecMul (table k.castSucc) t = table k.succ := by
  constructor
  · intro h
    refine ⟨(h 0).symm, fun k => ?_⟩
    rw [← h k.castSucc, ← h k.succ]
    exact (Function.iterate_succ_apply' (fun w => Matrix.vecMul w t) k.val v).symm
  · rintro ⟨h0, step⟩ i
    have chain : (List.ofFn table).IsChain (fun x y => Matrix.vecMul x t = y) :=
      List.isChain_ofFn.mpr fun k hk => step ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    have h := chain.iterate_eq_of_apply_eq i.val (by simpa only [List.length_ofFn] using i.isLt)
    simp only [List.getElem_ofFn] at h
    have zero : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    change (fun w => Matrix.vecMul w t)^[i.val] (table ⟨0, Nat.zero_lt_succ n⟩) = table i at h
    simpa only [zero, h0] using h

/-- Check one zero-degree update for each adjacent pair of rows in the table. -/
theorem forward_step (k : Fin 20) : Matrix.vecMul (W k.castSucc) T = W k.succ := by
  fin_cases k <;> decide +kernel

theorem forward_table (i : Fin 21) : forward T initial i.val = W i :=
  (forward_table_of_steps T initial W).2 ⟨rfl, forward_step⟩ i

/-- One forward relation suffices to propagate the recurrence. -/
theorem finite_certificate :
    forward T initial (1 + 6) = ∑ j : Fin 6, coeff j • forward T initial (1 + j.val) := by
  rw [show forward T initial (1 + 6) = W 7 from forward_table 7]
  have table_at (j : Fin 6) :
      forward T initial (1 + j.val) = W (Fin.castLE (by decide : 7 ≤ 21) j.succ) := by
    rw [Nat.add_comm 1 j.val]
    exact forward_table (Fin.castLE (by decide : 7 ≤ 21) j.succ)
  simp_rw [table_at]
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
