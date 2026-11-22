/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: finite_certificate, result
canonicalCount: proof_shape=bind-only; consumers=a, canonical_count_scale, HardinA229604Strip.a
canonical_count_scale: proof_shape=bind-only; consumers=result, HardinA229604Strip.result
a: proof_shape=bind-only; consumers=result
map_start: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=result, HardinA229604Strip.finite_certificate
result: proof_shape=content; consumers=none (external open-problem-resolution #31660)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229532Strip
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457Strip
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix
open DefectTransfer (defects literalCount lumped_count forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
/-- Literal row-major canonical arrays with exactly the prescribed number of square bonds of equal colours. -/
def canonicalCount (d n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin n × Fin 6 → Fin 3 =>
    @Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun f : Fin n × Fin 6 → Fin 3 =>
    defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = d ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

theorem canonical_count_scale (d m : ℕ) (hd : d < 5) :
    literalCount (q := 3) horizontal ProperTransfer.between d (m + 1) =
      6 * canonicalCount d (m + 1) := by
  classical
  let predicate : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun f =>
    defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = d
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, predicate (e ∘ f) ↔ predicate f := by
    intro e f
    change defects horizontal ProperTransfer.between _ = d ↔ _
    rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
      (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      DefectTransfer.relabel_defects]
  have nonconstant : ∀ f, predicate f → ∃ x y, f x ≠ f y := by
    intro f h
    by_contra he
    push Not at he
    have const : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
    change defects horizontal ProperTransfer.between _ = d at h
    rw [const] at h
    simp only [List.ofFn_const] at h
    rw [DefectTransfer.constant_defects] at h
    have cards : horizontal.card = 5 ∧ ProperTransfer.between.card = 6 := by decide +kernel
    rw [cards.1, cards.2] at h
    omega
  have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
    (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) predicate invariant nonconstant
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
  unfold literalCount canonicalCount
  convert orbit using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, predicate]

/-- Literal row-major canonical arrays with one monochromatic bond. -/
def a (n : ℕ) : ℕ := canonicalCount 1 n

private theorem map_start (r : Row) (hr : HardinA229635State.h r ≤ 2) :
    (HardinA229635State.startClass r).bind startImage =
      (if HardinA229635State.h r ≤ 1
        then some (cl r (1 - HardinA229635State.h r)) else none) := by
  obtain ⟨q, ⟨hq, e, he⟩, _⟩ := HardinA233177Canonical.canonical_exists_unique r
  have hh : HardinA229635State.h q = HardinA229635State.h r := by
    rw [he, HardinA229635State.h_relabel]
  have hrep := HardinA229635Laws.representatives_complete q hq (by rw [hh]; exact hr)
  let d := 2 - HardinA229635State.h r
  have hfresh : ¬ HardinA229635State.h q + d ≤ 1 := by dsimp [d]; omega
  have hclass : HardinA229635State.cl q d = HardinA229635State.cl r d := by
    rw [he, HardinA229635State.cl_relabel]
  rw [HardinA229635State.startClass, ite_eq_left hr]
  change startImage (HardinA229635State.cl r d) = _
  rw [← hclass, HardinA229635State.cl, ite_eq_right hfresh, startImage, Fin.addCases_right,
    hrep, hh, he, HardinA229457StripClasses.class_relabel]

theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 42,
      (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 42, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) := by
  refine ⟨by decide +kernel, ?_, HardinA229457StripClasses.transition_counts,
    HardinA229532Strip.finite_certificate.2.2.2.1, ?_⟩
  · intro p d hp r hr
    dsimp only [Valid,
      D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData.Valid] at hp ⊢
    omega
  · intro s
    by_cases hproper : s.val < 10
    · let i : Fin 10 := ⟨s.val, hproper⟩
      have hs : s = i.castAdd 32 := rfl
      rw [hs]
      let t := HardinA229457StripCut.crossedProperSlot (i.castAdd 10)
      have fibre (r : Row) :
          (bondDefects horizontal r r ≤ 1 ∧ cl r (1 - bondDefects horizontal r r) = i.castAdd 32) ↔
          (bondDefects horizontal r r ≤ 1 ∧
            HardinA229532StripData.cl r (1 - bondDefects horizontal r r) = t.castAdd 11) :=
        and_congr_right fun _ =>
          HardinA229457StripCut.proper_class_map r
            ⟨1 - bondDefects horizontal r r, by omega⟩ (i.castAdd 10)
      have weight (j : Fin 10) :
          initial (j.castAdd 32) =
            HardinA229532StripData.initial
              ((HardinA229457StripCut.crossedProperSlot (j.castAdd 10)).castAdd 11) := by
        fin_cases j <;> decide +kernel
      simp_rw [fibre, weight i]
      exact HardinA229532Strip.finite_certificate.2.2.2.2.1 (t.castAdd 11)
    · let squareIndex : Fin 6 → Fin 42 := ![20, 22, 23, 27, 35, 38]
      let crossedIndex : Fin 6 → Fin 31 := ![26, 30, 29, 25, 22, 21]
      by_cases hcrossed : ∃ k, s = squareIndex k
      · obtain ⟨k, rfl⟩ := hcrossed
        have fibre (r : Row) :
            (bondDefects horizontal r r ≤ 1 ∧ cl r (1 - bondDefects horizontal r r) = squareIndex k) ↔
            (bondDefects horizontal r r ≤ 1 ∧
              HardinA229532StripData.cl r (1 - bondDefects horizontal r r) = crossedIndex k) := by
          generalize h0 : r 0 = c0
          generalize h1 : r 1 = c1
          fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
        have weight : initial (squareIndex k) = HardinA229532StripData.initial (crossedIndex k) := by
          fin_cases k <;> rfl
        simp_rw [fibre, weight]
        exact HardinA229532Strip.finite_certificate.2.2.2.2.1 (crossedIndex k)
      · let j : Fin 32 := ⟨s.val - 10, by omega⟩
        have hs : s = j.natAdd 10 := by apply Fin.ext; dsimp [j]; omega
        have excluded (k : Fin 6) : j.val ≠ (squareIndex k).val - 10 := by
          intro hk
          apply hcrossed
          refine ⟨k, Fin.ext ?_⟩
          have hmin : 10 ≤ (squareIndex k).val := by fin_cases k <;> decide
          dsimp [j] at hk
          omega
        rw [hs, HardinA229457StripData.initial, Fin.append_right]
        have h10 : j ≠ 10 := fun h => excluded 0 (congrArg Fin.val h)
        have h12 : j ≠ 12 := fun h => excluded 1 (congrArg Fin.val h)
        have h13 : j ≠ 13 := fun h => excluded 2 (congrArg Fin.val h)
        have h17 : j ≠ 17 := fun h => excluded 3 (congrArg Fin.val h)
        have h25 : j ≠ 25 := fun h => excluded 4 (congrArg Fin.val h)
        have h28 : j ≠ 28 := fun h => excluded 5 (congrArg Fin.val h)
        simp only [ite_eq_right h10, ite_eq_right h12, ite_eq_right h13, ite_eq_right h17,
          ite_eq_right h25, ite_eq_right h28]
        change (∑ r : Row, if HardinA229635State.h r ≤ 1 ∧
          cl r (1 - HardinA229635State.h r) = j.natAdd 10 then (1 : ℤ) else 0) = _
        classical
        let rows := Finset.univ.filter fun r : Row => HardinA229635State.h r ≤ 2
        let firstClass (r : Row) := HardinA229635State.cl r (2 - HardinA229635State.h r)
        let mark (s : HardinA229635State.State) : ℤ :=
          if startImage s = some (j.natAdd 10) then 1 else 0
        calc
          _ = ∑ r ∈ rows, mark (firstClass r) := by
            simp only [rows, Finset.sum_filter, mark]
            apply Finset.sum_congr rfl
            intro r _
            by_cases hr : HardinA229635State.h r ≤ 2
            · have hm := map_start r hr
              rw [HardinA229635State.startClass, ite_eq_left hr, Option.bind_some] at hm
              by_cases h : HardinA229635State.h r ≤ 1 <;>
                simp [firstClass, hr, hm, h]
            · have h : ¬ HardinA229635State.h r ≤ 1 := by omega
              simp [hr, h]
          _ = ∑ s : HardinA229635State.State, ∑ r ∈ rows with firstClass r = s, mark s :=
            (Finset.sum_fiberwise' rows firstClass mark).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases h : startImage s = some (j.natAdd 10)
            · rw [ite_eq_left h, ← HardinA229635Transfer.initial_correct]
              simp only [mark, ite_eq_left h, rows]
              rw [Finset.filter_filter, Finset.sum_filter]
            · simp [mark, h]

attribute [local irreducible] a

theorem result (n : ℕ) :
    (a (n + 16) : ℤ) = 60 * a (n + 15) - 1482 * a (n + 14) + 20016 * a (n + 13) - 167163 * a (n + 12) + 924894 * a (n + 11) - 3537110 * a (n + 10) + 9593166 * a (n + 9) - 18693789 * a (n + 8) + 26218062 * a (n + 7) - 26188161 * a (n + 6) + 18139608 * a (n + 5) - 8262712 * a (n + 4) + 2220864 * a (n + 3) - 266256 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal ProperTransfer.between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal ProperTransfer.between id (bondDefects ProperTransfer.between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, canonical_count_scale 1 m (by decide)]
    push_cast
    simp only [a]
  have poly := HardinA229457StripPowers.forward_relation
  have h := forward_shift T initial terminal 14 1 ![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at h
  have h0 := bridge (n + 1)
  have h1 := bridge (n + 2)
  have h2 := bridge (n + 3)
  have h3 := bridge (n + 4)
  have h4 := bridge (n + 5)
  have h5 := bridge (n + 6)
  have h6 := bridge (n + 7)
  have h7 := bridge (n + 8)
  have h8 := bridge (n + 9)
  have h9 := bridge (n + 10)
  have h10 := bridge (n + 11)
  have h11 := bridge (n + 12)
  have h12 := bridge (n + 13)
  have h13 := bridge (n + 14)
  have h14 := bridge (n + 15)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457Strip
