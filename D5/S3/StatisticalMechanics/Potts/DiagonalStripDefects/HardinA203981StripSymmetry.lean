/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.finite_certificate
   digest: Colour and reflection symmetries of the six-column boundary. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203981Strip.result)
recolor: proof_shape=bind-only; consumers=boundary_recolor, cost_recolor, lift_counts, recolor.eq_1, recolor_match
reflect: proof_shape=bind-only; consumers=boundary_reflect, cost_reflect, lift_counts, reflect.eq_1
cost_formula: proof_shape=bind-only; consumers=HardinA203981StripCertificate.exact_cost_split, cost_recolor, cost_reflect
cost_recolor: proof_shape=bind-only; consumers=lift_counts
cost_reflect: proof_shape=bind-only; consumers=lift_counts
boundary_recolor: proof_shape=bind-only; consumers=lift_counts
boundary_reflect: proof_shape=bind-only; consumers=lift_counts
triple_match: proof_shape=bind-only; consumers=recolor_match
pair_match: proof_shape=bind-only; consumers=lift_counts
recolor_match: proof_shape=bind-only; consumers=lift_counts
lift_counts: proof_shape=bind-only; consumers=HardinA203981StripCertificate.counts, HardinA229508StripCertificate.one_counts, HardinA229683StripCertificate.two_counts
-/

import Init.Core
import Init.Ext
import Init.SimpLemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fin.Rev
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import Batteries.Logic
import Init.Data.Function
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.LinearOrder
import Init.Data.Fin.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Find
import Init.Data.List.OfFn

/-! Parity recolouring and simultaneous reflection of rows preserve diagonal defect counts. -/

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry

open HardinA203981StripData
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
  (Col cls relabel class_relabel class_rep)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects)
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def recolor (e f : Equiv.Perm (Fin 3)) : Row 3 6 ≃ Row 3 6 :=
  Equiv.piCongrRight (fun i : Fin 6 => if i.val % 2 = 0 then e else f)

private def reflect : Row 3 6 ≃ Row 3 6 :=
  Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin 6)) (Equiv.refl (Fin 3))

/-- The defect cost is the sum of the ten diagonal-bond indicators. -/
theorem cost_formula {q : ℕ} (p r : Row q 6) :
    bondDefects (betw 6) p r =
      (if p 0 = r 1 then 1 else 0) + (if p 1 = r 0 then 1 else 0) +
      (if p 1 = r 2 then 1 else 0) + (if p 2 = r 1 then 1 else 0) +
      (if p 2 = r 3 then 1 else 0) + (if p 3 = r 2 then 1 else 0) +
      (if p 3 = r 4 then 1 else 0) + (if p 4 = r 3 then 1 else 0) +
      (if p 4 = r 5 then 1 else 0) + (if p 5 = r 4 then 1 else 0) := by
  simp only [bondDefects, HardinA203981StripData.between_six, Finset.card_eq_sum_ones, Finset.sum_filter]
  norm_num only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.reduceEq, and_false, false_and, or_false, false_or, not_false_eq_true,
    Finset.sum_singleton, Prod.fst, Prod.snd]
  ac_rfl

private theorem cost_recolor (e f : Equiv.Perm (Fin 3)) (p r : Row 3 6) :
    bondDefects (betw 6) (recolor e f p) (recolor f e r) = bondDefects (betw 6) p r := by
  norm_num [cost_formula, recolor, Equiv.piCongrRight_apply, Fin.val_natCast,
    e.injective.eq_iff, f.injective.eq_iff]

private theorem cost_reflect (p r : Row 3 6) :
    bondDefects (betw 6) (reflect p) (reflect r) = bondDefects (betw 6) p r := by
  norm_num [cost_formula, reflect, Equiv.arrowCongr_apply, Fin.revPerm, Fin.rev,
    Fin.val_natCast]
  first | ac_rfl | omega

private theorem boundary_recolor (e f : Equiv.Perm (Fin 3)) (p : Row 3 6) :
    boundary (recolor e f p) = boundary p := by
  exact congrArg₂ pairClass (class_relabel e (parityRows p).1)
    (class_relabel f (parityRows p).2)

private theorem boundary_reflect (p : Row 3 6) : boundary (reflect p) = boundary p := by
  have exchange (i j : Fin 5) : pairClass i j = pairClass j i := by
    apply Fin.ext
    simp only [pairClass_eq_lookup, min_comm i j, max_comm i j]
  exact exchange _ _

private theorem triple_match (p r : Col) (h : cls p = cls r) :
    ∃ e : Equiv.Perm (Fin 3), relabel e p = r := by
  obtain ⟨e, he⟩ := class_rep p
  obtain ⟨f, hf⟩ := class_rep r
  rw [h, ← hf] at he
  exact ⟨e.trans f.symm, (congrArg (relabel f).symm he).trans ((relabel f).symm_apply_apply r)⟩

private theorem pair_match (i j : Fin 5) :
    let r := parityRows (representatives (pairClass i j))
    let a := cls r.1
    let b := cls r.2
    (i = a ∧ j = b) ∨ (j = a ∧ i = b) := by
  have index_lt : (pairClass i j).val < (List.ofFn classPair).length := by
    simpa only [List.length_ofFn] using (pairClass i j).isLt
  have lookup_lt := index_lt
  rw [pairClass_eq_lookup] at lookup_lt
  have readback := List.getElem?_idxOf (List.idxOf_lt_length_iff.mp lookup_lt)
  rw [← pairClass_eq_lookup, List.getElem?_eq_getElem index_lt, List.getElem_ofFn] at readback
  have coordinates : classPair (pairClass i j) = (min i j, max i j) :=
    Option.some.inj readback
  dsimp only
  rw [(cls_at_rep (pairClass i j)).1, (cls_at_rep (pairClass i j)).2, coordinates]
  rcases le_total i j with h | h
  · exact Or.inl ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
  · exact Or.inr ⟨(min_eq_right h).symm, (max_eq_left h).symm⟩

private theorem recolor_match (p r : Row 3 6)
    (h₀ : cls (parityRows p).1 = cls (parityRows r).1)
    (h₁ : cls (parityRows p).2 = cls (parityRows r).2) :
    ∃ e f : Equiv.Perm (Fin 3), recolor e f p = r := by
  obtain ⟨e, he⟩ := triple_match _ _ h₀
  obtain ⟨f, hf⟩ := triple_match _ _ h₁
  refine ⟨e, f, parityRows.injective ?_⟩
  exact Prod.ext he hf

/-- Exact-cost transition counts agree for source rows of the same boundary class. -/
theorem lift_counts (d : ℕ) (p q : Row 3 6) (j : Fin 15) (h : boundary p = boundary q) :
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = d ∧ boundary r = j
      then (1 : ℤ) else 0) =
    ∑ r : Row 3 6, if bondDefects (betw 6) q r = d ∧ boundary r = j
      then (1 : ℤ) else 0 := by
  have at_rep (p : Row 3 6) :
      (∑ r : Row 3 6, if bondDefects (betw 6) p r = d ∧ boundary r = j
        then (1 : ℤ) else 0) =
      ∑ r : Row 3 6, if bondDefects (betw 6) (representatives (boundary p)) r = d ∧
        boundary r = j then (1 : ℤ) else 0 := by
    have transport (q : Row 3 6)
        (heq : ∃ e f : Equiv.Perm (Fin 3), recolor e f q = representatives (boundary p)) :
        (∑ r : Row 3 6, if bondDefects (betw 6) q r = d ∧ boundary r = j
          then (1 : ℤ) else 0) =
        ∑ r : Row 3 6, if bondDefects (betw 6) (representatives (boundary p)) r = d ∧
          boundary r = j then (1 : ℤ) else 0 := by
      obtain ⟨e, f, hr⟩ := heq
      calc
        _ = ∑ r : Row 3 6, if bondDefects (betw 6) (recolor e f q) (recolor f e r) = d ∧
            boundary (recolor f e r) = j then (1 : ℤ) else 0 := by
              simp only [cost_recolor, boundary_recolor]
        _ = _ := by
          rw [hr]
          exact (recolor f e).sum_comp (fun r =>
            if bondDefects (betw 6) (representatives (boundary p)) r = d ∧ boundary r = j
              then (1 : ℤ) else 0)
    rcases pair_match (cls (parityRows p).1) (cls (parityRows p).2) with
      ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact transport p (recolor_match _ _ h₀ h₁)
    · calc
        _ = ∑ r : Row 3 6, if bondDefects (betw 6) (reflect p) (reflect r) = d ∧
            boundary (reflect r) = j then (1 : ℤ) else 0 := by
              simp only [cost_reflect, boundary_reflect]
        _ = _ := reflect.sum_comp _ |>.trans
          (transport (reflect p) (recolor_match _ _ h₀ h₁))
  exact (at_rep p).trans (h.symm ▸ (at_rep q).symm)

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
