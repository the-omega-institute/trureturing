/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.finite_certificate
   digest: Exact one-cost transitions and the order-twelve recurrence certificate. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229508Strip.result)
representative_counts: proof_shape=bind-only; consumers=one_counts
one_counts: proof_shape=bind-only; consumers=HardinA229683StripCertificate.transition_counts, transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229683StripCertificate.transition_counts
block_projection: proof_shape=bind-only; consumers=HardinA229683StripCertificate.forward_inherited, forward_zeroth
forward_zeroth: proof_shape=bind-only; consumers=finite_certificate
W: proof_shape=bind-only; consumers=HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.forward_two._proof_1, HardinA229683StripCertificate.forward_two._proof_10, HardinA229683StripCertificate.forward_two._proof_11, HardinA229683StripCertificate.forward_two._proof_12, HardinA229683StripCertificate.forward_two._proof_13, HardinA229683StripCertificate.forward_two._proof_14, HardinA229683StripCertificate.forward_two._proof_15, HardinA229683StripCertificate.forward_two._proof_16, HardinA229683StripCertificate.forward_two._proof_17, HardinA229683StripCertificate.forward_two._proof_18, HardinA229683StripCertificate.forward_two._proof_19, HardinA229683StripCertificate.forward_two._proof_2, HardinA229683StripCertificate.forward_two._proof_20, HardinA229683StripCertificate.forward_two._proof_3, HardinA229683StripCertificate.forward_two._proof_4, HardinA229683StripCertificate.forward_two._proof_5, HardinA229683StripCertificate.forward_two._proof_6, HardinA229683StripCertificate.forward_two._proof_7, HardinA229683StripCertificate.forward_two._proof_8, HardinA229683StripCertificate.forward_two._proof_9, finite_certificate, finite_certificate._proof_1, forward_one, forward_step, forward_step._proof_1, forward_step._proof_10, forward_step._proof_11, forward_step._proof_12, forward_step._proof_13, forward_step._proof_14, forward_step._proof_15, forward_step._proof_16, forward_step._proof_17, forward_step._proof_18, forward_step._proof_19, forward_step._proof_2, forward_step._proof_20, forward_step._proof_3, forward_step._proof_4, forward_step._proof_5, forward_step._proof_6, forward_step._proof_7, forward_step._proof_8, forward_step._proof_9
coeff: proof_shape=bind-only; consumers=HardinA229508Strip.result, HardinA229683StripCertificate.inherited_relation, coeff_values, coeff_values._proof_1, coeff_values._proof_10, coeff_values._proof_11, coeff_values._proof_12, coeff_values._proof_2, coeff_values._proof_3, coeff_values._proof_4, coeff_values._proof_5, coeff_values._proof_6, coeff_values._proof_7, coeff_values._proof_8, coeff_values._proof_9, finite_certificate, inherited_relation
squareMonicCoeff: proof_shape=bind-only; consumers=HardinA229683StripCertificate.coeff, coeff
coeff_values: proof_shape=bind-only; consumers=HardinA229508Strip.result, HardinA229683StripCertificate.inherited_relation, finite_certificate, inherited_relation
forward_step: proof_shape=content; consumers=HardinA229683StripCertificate.forward_two, forward_one
forward_one: proof_shape=content; consumers=finite_certificate
shifted_coordinate: proof_shape=bind-only; consumers=HardinA229683StripCertificate.inherited_relation, inherited_relation
inherited_relation: proof_shape=content; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=HardinA229508Strip.result, HardinA229683StripCertificate.inherited_relation
budget_cut: proof_shape=bind-only; consumers=HardinA229683StripCertificate.cut_terminal, HardinA229683StripCertificate.two_exact, one_exact, transition_counts
one_exact: proof_shape=bind-only; consumers=HardinA229683StripCertificate.representative_counts, representative_counts
halfForwardOne: proof_shape=bind-only; consumers=HardinA229683StripCertificate.W, W
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Basic.Logic.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Int.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Sum.Basic
import Init.Data.Sum.Lemmas
import Init.Prelude
import Init.SimpLemmas
import Init.Tactics
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Conjugate

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
open HardinA229508StripData
open HardinA203981StripData (boundary representatives cls_at_rep boundary_at_rep)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects forward forward_eq forward_shift)
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
set_option maxRecDepth 100000
set_option Elab.async false

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer (Col cls)
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA203981StripCertificate (halfCost reversed_count zero_exact allocated_counts halfForwardZero)
open HardinA203981StripData (halfZero columnRows unordered)

/-- A cost within the budget spends it exactly when the remainder is zero. -/
theorem budget_cut (c d : ℕ) : (c ≤ d ∧ d - c = 0) ↔ c = d := by
  rw [Nat.sub_eq_zero_iff_le]
  exact le_antisymm_iff.symm

/-- Project the exact-one count from the frozen terminal sector. -/
theorem one_exact (a : Col) (j : Fin 5) :
    (∑ b : Col, if halfCost a b = 1 ∧ cls b = j then (1 : ℤ) else 0) =
      halfOne (cls a) j := by
  rw [reversed_count]
  have h := HardinA229588Strip.finite_certificate.2.2.1 (columnRows a) 1
    (show HardinA229588Strip.Valid (columnRows a) 1 from le_rfl)
    ((Equiv.swap 1 3 j).natAdd 5)
  rw [← columnRows.sum_comp] at h
  have hh (r : Col) : bondDefects HardinA229588Strip.horizontal (columnRows r) (columnRows r) = 0 := rfl
  have hcol (r : Col) : (columnRows r 0, columnRows r 1, columnRows r 2) = r :=
    columnRows.symm_apply_apply r
  have terminal (r : Col) :
      HardinA229588Strip.cl (columnRows r) (1 - bondDefects HardinA229588Strip.between
        (columnRows a) (columnRows r)) = (Equiv.swap 1 3 j).natAdd 5 ↔
      1 - bondDefects HardinA229588Strip.between (columnRows a) (columnRows r) = 0 ∧
        cls r = Equiv.swap 1 3 j := by
    let m := 1 - bondDefects HardinA229588Strip.between (columnRows a) (columnRows r)
    change HardinA229588Strip.cl (columnRows r) m = (Equiv.swap 1 3 j).natAdd 5 ↔
      m = 0 ∧ cls r = Equiv.swap 1 3 j
    have hm : m ≤ 1 := Nat.sub_le _ _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h0 | h1
    · simp only [h0, HardinA229588Strip.cl, Nat.zero_ne_one, ite_false, ite_true,
        hcol, Fin.natAdd_inj 5, true_and]
    · simp only [h1, HardinA229588Strip.cl, ite_true, Nat.one_ne_zero, false_and, hcol]
      apply iff_false_intro
      intro he
      exact Sum.inl_ne_inr
        ((finSumFinEquiv : Fin 5 ⊕ Fin 5 ≃ Fin (5 + 5)).injective he)
  simp only [hh, Nat.add_zero] at h
  have sourceClass : HardinA229588Strip.cl (columnRows a) (1 : Fin 2).val = (cls a).castAdd 5 := by
    change HardinA229588Strip.cl (columnRows a) 1 = _
    simp only [HardinA229588Strip.cl, ite_true, hcol]
  rw [sourceClass] at h
  refine (Finset.sum_congr rfl fun r _ => ?_).trans h
  apply if_congr ?_ rfl rfl
  let c := bondDefects HardinA229588Strip.between (columnRows a) (columnRows r)
  change (c = 1 ∧ cls r = Equiv.swap 1 3 j) ↔
    (c ≤ 1 ∧ HardinA229588Strip.cl (columnRows r) (1 - c) = (Equiv.swap 1 3 j).natAdd 5)
  rw [terminal r, ← and_assoc, budget_cut]

private theorem representative_counts (i j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) (representatives i) r = 1 ∧ boundary r = j
      then (1 : ℤ) else 0) = costOne i j := by
  have h := allocated_counts 1 ![halfZero, halfOne] (representatives i) j (fun k a c _ _ => by
      fin_cases k
      · exact zero_exact a c
      · exact one_exact a c
    )
  rw [Fin.sum_univ_two] at h
  rw [(cls_at_rep i).1, (cls_at_rep i).2] at h
  exact h

/-- Counts into a specified class across a single defect. -/
theorem one_counts (p : Row 3 6) (j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 1 ∧ boundary r = j
      then (1 : ℤ) else 0) = costOne (boundary p) j := by
  exact (HardinA203981StripSymmetry.lift_counts 1 p (representatives (boundary p)) j
    (boundary_at_rep (boundary p)).symm).trans (representative_counts (boundary p) j)

theorem transition_counts (p : Row 3 6) (d : Fin 2) (s : Fin 15 ⊕ Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ d.val ∧
      cl r (d.val - bondDefects (betw 6) p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  fin_cases d
  · cases s with
    | inl j =>
      simp only [Fin.val_zero, Nat.zero_sub, cl, ite_true, Sum.inr_ne_inl, and_false, ite_false,
        Finset.sum_const_zero, T, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    | inr j =>
      simpa only [Fin.val_zero, Nat.le_zero, Nat.zero_sub, cl, ite_true,
        Sum.inr.injEq, T, Matrix.fromBlocks_apply₂₂] using HardinA203981StripCertificate.counts p j
  · cases s with
    | inl j =>
      have cut (r : Row 3 6) :
          (bondDefects (betw 6) p r ≤ 1 ∧ cl r (1 - bondDefects (betw 6) p r) = Sum.inl j) ↔
          bondDefects (betw 6) p r = 0 ∧ boundary r = j := by
        constructor
        · rintro ⟨hc, hs⟩
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with hz | ho
          · exact ⟨hz, by simpa only [hz, Nat.sub_zero, cl, Nat.one_ne_zero,
              ite_false, Sum.inl.injEq] using hs⟩
          · simp only [ho, Nat.sub_self, cl, ite_true, Sum.inr_ne_inl] at hs
        · rintro ⟨hz, hb⟩
          simp only [hz, Nat.zero_le, Nat.sub_zero, cl, Nat.one_ne_zero,
            ite_false, Sum.inl.injEq, hb, true_and]
      change (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ 1 ∧
        cl r (1 - bondDefects (betw 6) p r) = Sum.inl j then (1 : ℤ) else 0) =
          T (cl p 1) (Sum.inl j)
      simp_rw [cut]
      simpa only [cl, Nat.one_ne_zero, ite_false,
        T, Matrix.fromBlocks_apply₁₁] using HardinA203981StripCertificate.counts p j
    | inr j =>
      have cut (r : Row 3 6) :
          (bondDefects (betw 6) p r ≤ 1 ∧ cl r (1 - bondDefects (betw 6) p r) = Sum.inr j) ↔
          bondDefects (betw 6) p r = 1 ∧ boundary r = j := by
        constructor
        · rintro ⟨hc, hs⟩
          rw [cl] at hs
          split at hs
          · rename_i hz
            exact ⟨(budget_cut _ _).mp ⟨hc, hz⟩, Sum.inr.injEq.mp hs⟩
          · exact (Sum.inl_ne_inr hs).elim
        · rintro ⟨hc, hb⟩
          obtain ⟨hle, hz⟩ := (budget_cut _ _).mpr hc
          exact ⟨hle, by simp only [hz, cl, ite_true, Sum.inr.injEq, hb]⟩
      change (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ 1 ∧
        cl r (1 - bondDefects (betw 6) p r) = Sum.inr j then (1 : ℤ) else 0) =
          T (cl p 1) (Sum.inr j)
      simp_rw [cut]
      simpa only [cl, Nat.one_ne_zero, ite_false,
        T, Matrix.fromBlocks_apply₁₂] using one_counts p j

theorem block_projection {l r α : Type*} [Fintype l] [Fintype r] [NonUnitalNonAssocSemiring α]
    (a : Matrix l l α) (b : Matrix l r α) (c : Matrix r r α) (v : l ⊕ r → α) (n : ℕ) :
    ((fun w => Matrix.vecMul w (Matrix.fromBlocks a b 0 c))^[n] v) ∘ Sum.inl =
      (fun w => Matrix.vecMul w a)^[n] (v ∘ Sum.inl) := by
  have h : Function.Semiconj (fun w : l ⊕ r → α => w ∘ Sum.inl)
      (fun w => Matrix.vecMul w (Matrix.fromBlocks a b 0 c)) (fun w => Matrix.vecMul w a) := by
    intro w
    change Matrix.vecMul w (Matrix.fromBlocks a b 0 c) ∘ Sum.inl = Matrix.vecMul (w ∘ Sum.inl) a
    rw [Matrix.vecMul_fromBlocks]
    funext j
    simp [Function.comp_def]
  exact h.iterate_right n v

/-- The first sector is the zero-defect forward system at every exponent. -/
theorem forward_zeroth (n : ℕ) : forward T initial n ∘ Sum.inl =
    forward HardinA203981StripData.T HardinA203981StripData.initial n := by
  exact block_projection _ _ _ _ n

/-- The half-strip forward vectors in exact-cost degree 1. -/
def halfForwardOne : Fin 21 → Fin 5 → ℤ :=
  Matrix.vecCons (0 : Fin 5 → ℤ) (Matrix.vecCons (fun j => HardinA229588Strip.W 1 (j.natAdd 5))
    ![fun j : Fin 5 => HardinA229588Strip.W 2 ((Equiv.swap 1 3 j).natAdd 5),
    ![1644, 2406, 1602, 2436, 1632],
    ![10380, 13470, 8892, 13908, 8286],
    ![59946, 73344, 49104, 75966, 41160],
    ![331590, 387510, 261558, 404562, 203100],
    ![1777398, 2010720, 1367730, 2110506, 995358],
    ![9320448, 10280940, 7035318, 10841808, 4855182],
    ![48062886, 51972294, 35741484, 55012938, 23584278],
    ![244626816, 260291310, 179732718, 276379104, 114154620],
    ![1232038140, 1293572766, 896272632, 1377107340, 550794234],
    ![6151560582, 6386839908, 4438054080, 6814356114, 2650075116],
    ![30493060134, 31358474490, 21844483506, 33521267202, 12718073172],
    ![150226357422, 153222899172, 106966659546, 164061769962, 60895203666],
    ![736199319228, 745515804252, 521439011046, 799411222140, 290960009814],
    ![3591284854602, 3613865018010, 2531889435744, 3880090505550, 1387554925614],
    ![17448371454444, 17460226198758, 12250924641810, 18767880996324, 6605447597328],
    ![84472101194124, 84109078953726, 59093625304332, 90500741777316, 31394234901822],
    ![407656599056970, 404091950193120, 284249234984832, 435200551114398, 148986407380296],
    ![1961740076499606, 1936745253298374, 1363840823481174, 2087584250909826, 706057576313820]])

/-- Aggregate the half-strip forward vectors in total cost degree 1. -/
def W (i : Fin 21) : Fin 15 → ℤ :=
  fun j => unordered (halfForwardZero i) (halfForwardOne i) j +
    unordered (halfForwardOne i) (halfForwardZero i) j

/-- The squared monic polynomial, computed as a Cauchy product. -/
def squareMonicCoeff (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
    HardinA203981StripCertificate.monicCoeff p.1 * HardinA203981StripCertificate.monicCoeff p.2

/-- Recurrence coefficients in increasing order of the input index. -/
def coeff (k : Fin 12) : ℤ :=
  -squareMonicCoeff k.val

/-- The computed expansion in increasing order of the input index. -/
theorem coeff_values : coeff = ![-43046721, 47829690, 13286025, -27398736, 2329155, 4556250, -940491, -180630, 50175, 324, -715, 50] := by
  funext k
  fin_cases k <;> decide +kernel

/-- Check the update on the whole table of zero- and one-degree vectors. -/
theorem forward_step (k : Fin 20) :
    Matrix.vecMul (Sum.elim (HardinA203981StripCertificate.W k.castSucc) (W k.castSucc)) T =
      Sum.elim (HardinA203981StripCertificate.W k.succ) (W k.succ) := by
  have step : Matrix.vecMul (HardinA203981StripCertificate.W k.castSucc) costOne +
      Matrix.vecMul (W k.castSucc) HardinA203981StripData.T = W k.succ := by
    fin_cases k <;> decide +kernel
  rw [show Matrix.vecMul _ T = _ from
    Matrix.vecMul_fromBlocks HardinA203981StripData.T costOne 0 HardinA203981StripData.T _]
  change Sum.elim
    (Matrix.vecMul (HardinA203981StripCertificate.W k.castSucc) HardinA203981StripData.T +
      Matrix.vecMul (W k.castSucc) 0)
    (Matrix.vecMul (HardinA203981StripCertificate.W k.castSucc) costOne +
      Matrix.vecMul (W k.castSucc) HardinA203981StripData.T) = _
  simp only [Matrix.vecMul_zero, add_zero, HardinA203981StripCertificate.forward_step k, step]

theorem forward_one (i : Fin 21) : forward T initial i.val ∘ Sum.inr = W i := by
  let table (k : Fin 21) := Sum.elim (HardinA203981StripCertificate.W k) (W k)
  have zero : table 0 = initial := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  exact congrArg (· ∘ (Sum.inr : Fin 15 → Fin 15 ⊕ Fin 15))
    ((HardinA203981StripCertificate.forward_table_of_steps (fun w => Matrix.vecMul w T) initial table).2 ⟨zero, forward_step⟩ i)

/-- A base forward relation is equivalent to its coordinate equations at all shifts. -/
theorem shifted_coordinate {s : Type*} [Fintype s] (t : Matrix s s ℤ)
    (v : s → ℤ) (d b : ℕ) (c : Fin d → ℤ) :
    (forward t v (b + d) = ∑ i : Fin d, c i • forward t v (b + i.val)) ↔
      ∀ (n : ℕ) (j : s), forward t v (n + b + d) j =
        ∑ i : Fin d, c i * forward t v (n + b + i.val) j := by
  constructor
  · intro h n j
    classical
    have coordinate (k : ℕ) :
        dotProduct v ((t ^ k).mulVec (Pi.single j 1)) = forward t v k j := by
      rw [Matrix.dotProduct_mulVec, forward_eq, dotProduct_single_one]
    simpa only [coordinate] using forward_shift t v (Pi.single j 1) d b c h n
  · intro h
    funext j
    simpa only [Nat.zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h 0 j

private theorem inherited_relation (j : Fin 15) :
    forward HardinA203981StripData.T HardinA203981StripData.initial (1 + 12) j =
      ∑ k : Fin 12, coeff k * forward HardinA203981StripData.T HardinA203981StripData.initial (1 + k.val) j := by
  have rel (n : ℕ) := (shifted_coordinate HardinA203981StripData.T HardinA203981StripData.initial
    6 1 HardinA203981StripCertificate.coeff).1 HardinA203981StripCertificate.finite_certificate n j
  have h0 := rel 0
  have h1 := rel 1
  have h2 := rel 2
  have h3 := rel 3
  have h4 := rel 4
  have h5 := rel 5
  have h6 := rel 6
  simp only [coeff_values, HardinA203981StripCertificate.coeff,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.val_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, add_zero] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith only [h0, h1, h2, h3, h4, h5, h6]

theorem finite_certificate :
    forward T initial (1 + 12) = ∑ k : Fin 12, coeff k • forward T initial (1 + k.val) := by
  funext j
  cases j with
  | inl j =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ← Function.comp_apply (f := forward T initial _) (g := Sum.inl), forward_zeroth]
    exact inherited_relation j
  | inr j =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [show forward T initial (1 + 12) (Sum.inr j) = W 13 j from congrFun (forward_one 13) j]
    simp_rw [show ∀ k : Fin 12, forward T initial (1 + k.val) (Sum.inr j) = W (Fin.castLE (by decide : 13 ≤ 21) k.succ) j from
      fun k => by
        rw [Nat.add_comm 1 k.val]
        exact congrFun (forward_one (Fin.castLE (by decide : 13 ≤ 21) k.succ)) j]
    have fresh : ∀ j : Fin 15, W 13 j = ∑ k : Fin 12, coeff k * W (Fin.castLE (by decide : 13 ≤ 21) k.succ) j := by
      rw [coeff_values]
      decide +kernel
    exact fresh j

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
