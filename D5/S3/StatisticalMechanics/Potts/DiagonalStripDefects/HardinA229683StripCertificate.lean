/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.finite_certificate
   digest: The two-cost transitions and order-eighteen recurrence certificate. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229683Strip.result)
representative_counts: proof_shape=bind-only; consumers=two_counts
two_counts: proof_shape=bind-only; consumers=transition_counts
cut_inherited: proof_shape=bind-only; consumers=transition_counts
cut_terminal: proof_shape=bind-only; consumers=transition_counts._simp_1
transition_counts: proof_shape=bind-only; consumers=HardinA229683Strip.counting_bridge
forward_inherited: proof_shape=bind-only; consumers=finite_certificate
W: proof_shape=bind-only; consumers=finite_certificate, finite_certificate._proof_1, forward_two, forward_two._proof_1
coeff: proof_shape=bind-only; consumers=coeff_values, finite_certificate, HardinA229683Strip.result
coeff_values: proof_shape=bind-only; consumers=finite_certificate, inherited_relation, HardinA229683Strip.result
forward_two: proof_shape=content; consumers=finite_certificate
inherited_relation: proof_shape=content; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=HardinA229683Strip.result
two_exact: proof_shape=bind-only; consumers=representative_counts
halfForwardTwo: proof_shape=bind-only; consumers=W
-/

import Mathlib.Order.Fin.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Prod
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Sum.Basic
import Init.Data.Sum.Lemmas
import Init.Prelude
import Init.Tactics
import Init.SimpLemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Function.Iterate
import Init.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate

open HardinA229683StripData
open HardinA203981StripData (boundary classPair parityRows representatives)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects forward)
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
set_option maxRecDepth 100000
set_option Elab.async false

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer (Col cls)
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA203981StripCertificate (halfCost reversed_count zero_exact allocated_counts halfForwardZero)
open HardinA203981StripData (halfZero columnRows unordered)
open D5.S3.StatisticalMechanics.Potts.StripDefectsTwo
open HardinA229508StripData (halfOne)
open HardinA229508StripCertificate (one_exact halfForwardOne)

/-- Project the exact-two count from the frozen terminal sector. -/
private theorem two_exact (a : Col) (j : Fin 5) :
    (∑ b : Col, if halfCost a b = 2 ∧ cls b = j then (1 : ℤ) else 0) =
      halfTwo (cls a) j := by
  rw [reversed_count]
  have h := HardinA229696Strip.finite_certificate.2.2.1 (columnRows a) 2
    (show HardinA229696StripData.Valid (columnRows a) 2 from le_rfl)
    ((Equiv.swap 1 3 j).natAdd 10)
  rw [← columnRows.sum_comp] at h
  have hh (r : Col) : bondDefects HardinA229588Strip.horizontal (columnRows r) (columnRows r) = 0 := rfl
  have hcol (r : Col) : (columnRows r 0, columnRows r 1, columnRows r 2) = r :=
    columnRows.symm_apply_apply r
  have terminal (r : Col) (m : ℕ) :
      HardinA229696StripData.cl (columnRows r) m = (Equiv.swap 1 3 j).natAdd 10 ↔ m = 0 ∧ cls r = Equiv.swap 1 3 j := by
    cases m with
    | zero => simp only [HardinA229696StripData.cl, Nat.lt_irrefl, ite_false, hcol,
        Fin.natAdd_inj 10, true_and]
    | succ m =>
      simp only [HardinA229696StripData.cl, Nat.succ_ne_zero, Nat.zero_lt_succ, ite_true, ite_false, false_and]
      apply iff_false_intro
      intro he
      exact Sum.inl_ne_inr
        ((finSumFinEquiv : Fin 10 ⊕ Fin 5 ≃ Fin (10 + 5)).injective he)
  simp only [hh, Nat.add_zero] at h
  have sourceClass : HardinA229696StripData.cl (columnRows a) (2 : Fin 3).val = (cls a).castAdd 10 := by
    have hA : HardinA229588Strip.cl (columnRows a) 1 = (cls a).castAdd 5 := by
      simp only [HardinA229588Strip.cl, ite_true, hcol]
    change (HardinA229588Strip.cl (columnRows a) 1).castAdd 5 = _
    exact congrArg (Fin.castAdd 5) hA
  rw [sourceClass] at h
  refine (Finset.sum_congr rfl fun r _ => ?_).trans h
  apply if_congr ?_ rfl rfl
  let c := bondDefects HardinA229588Strip.between (columnRows a) (columnRows r)
  change (c = 2 ∧ cls r = Equiv.swap 1 3 j) ↔
    (c ≤ 2 ∧ HardinA229696StripData.cl (columnRows r) (2 - c) = (Equiv.swap 1 3 j).natAdd 10)
  rw [terminal r]
  constructor
  · rintro ⟨hc, hj⟩
    exact ⟨hc ▸ le_rfl, hc ▸ Nat.sub_self _, hj⟩
  · rintro ⟨hle, hz, hj⟩
    exact ⟨Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hz), hj⟩

private theorem representative_counts (i j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) (representatives i) r = 2 ∧ boundary r = j
      then (1 : ℤ) else 0) = costTwo i j := by
  have h := allocated_counts 2 ![halfZero, halfOne, halfTwo] (representatives i) j (fun k a c _ _ => by
      fin_cases k
      · exact zero_exact a c
      · exact one_exact a c
      · exact two_exact a c
    )
  rw [Fin.sum_univ_three] at h
  have cls_at_rep : ∀ i : Fin 15,
      cls (parityRows (representatives i)).1 = (classPair i).1 ∧
      cls (parityRows (representatives i)).2 = (classPair i).2 := by
    simp only [representatives, Equiv.apply_symm_apply]
    decide +kernel
  rw [(cls_at_rep i).1, (cls_at_rep i).2] at h
  exact h

theorem two_counts (p : Row 3 6) (j : Fin 15) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 2 ∧ boundary r = j
      then (1 : ℤ) else 0) = costTwo (boundary p) j := by
  have boundary_at_rep : ∀ i : Fin 15, boundary (representatives i) = i := by
    decide +kernel
  exact (HardinA203981StripSymmetry.lift_counts 2 p (representatives (boundary p)) j
    (boundary_at_rep (boundary p)).symm).trans (representative_counts (boundary p) j)

private theorem cut_inherited (p r : Row 3 6) (d : ℕ) (s : Fin 15 ⊕ Fin 15) :
    (bondDefects (betw 6) p r ≤ d + 1 ∧
      cl r (d + 1 - bondDefects (betw 6) p r) = Sum.inl s) ↔
    (bondDefects (betw 6) p r ≤ d ∧
      HardinA229508StripData.cl r (d - bondDefects (betw 6) p r) = s) := by
  let c := bondDefects (betw 6) p r
  change (c ≤ d + 1 ∧ cl r (d + 1 - c) = Sum.inl s) ↔
    (c ≤ d ∧ HardinA229508StripData.cl r (d - c) = s)
  by_cases h : c ≤ d
  · have hlt : c < d + 1 := Nat.lt_succ_of_le h
    have hle : c ≤ d + 1 := Nat.le_of_lt hlt
    rw [cl, if_neg (Nat.sub_ne_zero_iff_lt.mpr hlt), Sum.inl.injEq,
      Nat.succ_sub h, Nat.succ_sub_one]
    simp only [h, hle, true_and]
  · have hz : d + 1 - c = 0 := Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
    simp only [h, hz, cl, ite_true, Sum.inr_ne_inl, and_false, false_and]

private theorem cut_terminal (p r : Row 3 6) (d : ℕ) (j : Fin 15) :
    (bondDefects (betw 6) p r ≤ d ∧
      cl r (d - bondDefects (betw 6) p r) = Sum.inr j) ↔
    (bondDefects (betw 6) p r = d ∧ boundary r = j) := by
  constructor
  · rintro ⟨hc, hs⟩
    rw [cl] at hs
    split at hs
    · rename_i hz
      exact ⟨Nat.le_antisymm hc (Nat.sub_eq_zero_iff_le.mp hz), Sum.inr.inj hs⟩
    · exact (Sum.inl_ne_inr hs).elim
  · rintro ⟨hc, hb⟩
    simp only [hc, Nat.le_refl, Nat.sub_self, cl, ite_true, hb, true_and]

theorem transition_counts (p : Row 3 6) (d : Fin 3) (s : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15)) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ d.val ∧
      cl r (d.val - bondDefects (betw 6) p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s := by
  cases s with
  | inl s =>
    fin_cases d
    · change (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ 0 ∧
        cl r (0 - bondDefects (betw 6) p r) = Sum.inl s then (1 : ℤ) else 0) = 0
      simp only [Nat.zero_sub, cl, ite_true, Sum.inr_ne_inl, and_false,
        ite_false, Finset.sum_const_zero]
    · change (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ 0 + 1 ∧
        cl r (0 + 1 - bondDefects (betw 6) p r) = Sum.inl s then (1 : ℤ) else 0) =
          T (cl p 1) (Sum.inl s)
      refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_)
        (HardinA229508StripCertificate.transition_counts p 0 s)
      exact if_congr (cut_inherited p r 0 s) rfl rfl
    · change (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ 1 + 1 ∧
        cl r (1 + 1 - bondDefects (betw 6) p r) = Sum.inl s then (1 : ℤ) else 0) =
          T (cl p 2) (Sum.inl s)
      refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_)
        (HardinA229508StripCertificate.transition_counts p 1 s)
      exact if_congr (cut_inherited p r 1 s) rfl rfl
  | inr j =>
    simp only [cut_terminal]
    fin_cases d
    · exact HardinA203981StripCertificate.counts p j
    · exact HardinA229508StripCertificate.one_counts p j
    · exact two_counts p j

/-- The two inherited sectors retain their one-budget forward system. -/
theorem forward_inherited (n : ℕ) : forward T initial n ∘ Sum.inl =
    forward HardinA229508StripData.T HardinA229508StripData.initial n := by
  exact HardinA229508StripCertificate.block_projection _ _ _ _ n

/-- The half-strip forward vectors in exact-cost degree 2. -/
private def halfForwardTwo : Fin 21 → Fin 5 → ℤ :=
  Matrix.vecCons (0 : Fin 5 → ℤ) (Matrix.vecCons (fun j => HardinA229696StripData.W 1 (j.natAdd 10))
    ![fun j : Fin 5 => HardinA229696StripData.W 2 ((Equiv.swap 1 3 j).natAdd 10),
    ![4260, 7254, 5496, 7296, 6156],
    ![33714, 52152, 38220, 52206, 38874],
    ![237060, 335064, 238440, 340806, 230352],
    ![1527588, 2041512, 1437360, 2089626, 1308054],
    ![9331776, 11934084, 8344668, 12297270, 7224648],
    ![54803898, 67754670, 47215734, 70168290, 39067716],
    ![312537492, 375930786, 261497496, 391018602, 207849336],
    ![1741685184, 2048052354, 1423541634, 2138093160, 1091348382],
    ![9527295600, 10991408502, 7638684996, 11511279588, 5668519848],
    ![51323541552, 58252399386, 40493423814, 61177792254, 29175082752],
    ![272947413348, 305448829662, 212431541808, 321578071986, 148993363536],
    ![1435760689086, 1586972644800, 1104394427556, 1674431498220, 755766518808],
    ![7481320233948, 8179390024572, 5696236047324, 8647086935712, 3811000142652],
    ![38662730713278, 41861213646558, 29175077375430, 44333049164208, 19116956819370],
    ![198359964365976, 212906164658754, 148501548557544, 225838963341156, 95449545328056],
    ![1011156130689210, 1076811497607804, 751669231172136, 1143886537051206, 474582056479986],
    ![5124872433867084, 5418897392947692, 3785638286159040, 5764115710799886, 2350751099448444],
    ![25840495210128840, 27146315366727504, 18979013148575640, 28911042163897566, 11604064264473702]])

/-- Aggregate the half-strip forward vectors in total cost degree 2. -/
def W (i : Fin 21) : Fin 15 → ℤ :=
  fun j => unordered (halfForwardZero i) (halfForwardTwo i) j +
    unordered (halfForwardOne i) (halfForwardOne i) j +
    unordered (halfForwardTwo i) (halfForwardZero i) j

/-- The missing lag-sixteen term has coefficient zero. -/
def coeff (k : Fin 18) : ℤ :=
  -(∑ p ∈ Finset.HasAntidiagonal.antidiagonal k.val,
    HardinA229508StripCertificate.squareMonicCoeff p.1 * HardinA203981StripCertificate.monicCoeff p.2)

/-- The computed expansion in increasing order of the input index. -/
theorem coeff_values : coeff = ![-282429536481, 470715894135, 0, -366499782594, 132368667075, 92909172825, -54520532190, -6257717775, 8082823950, -601275555, -435322350, 70536825, 7404210, -2206575, 60075, 19486, -2010, 75] := by
  funext k
  fin_cases k <;> decide +kernel

theorem forward_two (i : Fin 21) : forward T initial i.val ∘ Sum.inr = W i := by
  let previous (k : Fin 21) :=
    Sum.elim (HardinA203981StripCertificate.W k) (HardinA229508StripCertificate.W k)
  let table (k : Fin 21) := Sum.elim (previous k) (W k)
  have right_step (k : Fin 20) :
      Matrix.vecMul (HardinA203981StripCertificate.W k.castSucc) costTwo +
        Matrix.vecMul (HardinA229508StripCertificate.W k.castSucc) HardinA229508StripData.costOne +
        Matrix.vecMul (W k.castSucc) HardinA203981StripData.T = W k.succ := by
    fin_cases k <;> decide +kernel
  have step (k : Fin 20) : Matrix.vecMul (table k.castSucc) T = table k.succ := by
    have incoming :
        Matrix.vecMul (previous k.castSucc) (Matrix.fromRows costTwo HardinA229508StripData.costOne) =
          Matrix.vecMul (HardinA203981StripCertificate.W k.castSucc) costTwo +
            Matrix.vecMul (HardinA229508StripCertificate.W k.castSucc) HardinA229508StripData.costOne :=
      Matrix.sumElim_vecMul_fromRows costTwo HardinA229508StripData.costOne
        (HardinA203981StripCertificate.W k.castSucc) (HardinA229508StripCertificate.W k.castSucc)
    rw [show Matrix.vecMul (table k.castSucc) T = _ from
      Matrix.vecMul_fromBlocks HardinA229508StripData.T
        (Matrix.fromRows costTwo HardinA229508StripData.costOne) 0 HardinA203981StripData.T _]
    change Sum.elim
      (Matrix.vecMul (previous k.castSucc) HardinA229508StripData.T + Matrix.vecMul (W k.castSucc) 0)
      (Matrix.vecMul (previous k.castSucc) (Matrix.fromRows costTwo HardinA229508StripData.costOne) +
        Matrix.vecMul (W k.castSucc) HardinA203981StripData.T) = table k.succ
    have left_step : Matrix.vecMul (previous k.castSucc) HardinA229508StripData.T =
        previous k.succ :=
      HardinA229508StripCertificate.forward_step k
    simp only [Matrix.vecMul_zero, add_zero, left_step, incoming, right_step k, table]
  have zero : table 0 = initial := by
    funext j
    rcases j with (j | j) | j
    · rfl
    · fin_cases j <;> rfl
    · fin_cases j <;> rfl
  exact congrArg (· ∘ (Sum.inr : Fin 15 → (Fin 15 ⊕ Fin 15) ⊕ Fin 15))
    ((HardinA203981StripCertificate.forward_table_of_steps (fun w => Matrix.vecMul w T) initial table).2 ⟨zero, step⟩ i)

private theorem inherited_relation (j : Fin 15 ⊕ Fin 15) :
    forward HardinA229508StripData.T HardinA229508StripData.initial (2 + 18) j =
      ∑ k : Fin 18, coeff k * forward HardinA229508StripData.T HardinA229508StripData.initial (2 + k.val) j := by
  have rel (n : ℕ) := (HardinA229508StripCertificate.shifted_coordinate
    HardinA229508StripData.T HardinA229508StripData.initial
    12 1 HardinA229508StripCertificate.coeff).1 HardinA229508StripCertificate.finite_certificate n j
  have h1 := rel 1
  have h2 := rel 2
  have h3 := rel 3
  have h4 := rel 4
  have h5 := rel 5
  have h6 := rel 6
  have h7 := rel 7
  simp only [coeff_values, HardinA229508StripCertificate.coeff_values,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.reduceAdd, add_zero] at h1 h2 h3 h4 h5 h6 h7 ⊢
  linarith only [h1, h2, h3, h4, h5, h6, h7]

theorem finite_certificate :
    forward T initial (2 + 18) = ∑ k : Fin 18, coeff k • forward T initial (2 + k.val) := by
  funext j
  cases j with
  | inl j =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ← Function.comp_apply (f := forward T initial _) (g := Sum.inl), forward_inherited]
    exact inherited_relation j
  | inr j =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [show forward T initial (2 + 18) (Sum.inr j) = W 20 j from congrFun (forward_two 20) j]
    simp_rw [show ∀ k : Fin 18, forward T initial (2 + k.val) (Sum.inr j) = W k.succ.succ.castSucc j from
      fun k => by
        rw [Nat.add_comm 2 k.val]
        exact congrFun (forward_two k.succ.succ.castSucc) j]
    have fresh : ∀ j : Fin 15, W 20 j = ∑ k : Fin 18, coeff k * W k.succ.succ.castSucc j := by
      rw [coeff_values]
      decide +kernel
    exact fresh j

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
