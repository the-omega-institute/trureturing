/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31660)
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457Strip
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row horizontal)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604Strip
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229604StripData
open DefectTransfer (defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun f : Fin n × Fin 6 → Fin 3 =>
    @Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun f : Fin n × Fin 6 → Fin 3 =>
    defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = 2 ∧
    (@Canonical (Fin n × Fin 6)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 96,
      (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 96, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) := by
  refine ⟨by decide +kernel, ?_, HardinA229604StripClasses.transition_counts,
    ?_, ?_⟩
  · intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega
  · intro r hr
    dsimp only [Valid]
    omega

  · intro s
    by_cases hs : s.val < 42
    · let j : Fin 42 := ⟨s.val, hs⟩
      have he : s = j.castAdd 54 := rfl
      rw [he]
      have cut (r : Row) :
          (bondDefects horizontal r r ≤ 2 ∧
            cl r (2 - bondDefects horizontal r r) = j.castAdd 54) ↔
          (bondDefects horizontal r r ≤ 1 ∧
            HardinA229457StripData.cl r (1 - bondDefects horizontal r r) = j) :=
        HardinA229604StripCut.active_cut r (bondDefects horizontal r r) 2 j (by decide)
      simp_rw [cut]
      simpa only [HardinA229604StripData.initial, Fin.append_left] using
        HardinA229457Strip.finite_certificate.2.2.2.2 j
    · have new_counts : ∀ j : Fin 54,
          (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
            cl r (2 - bondDefects horizontal r r) = j.natAdd 42
            then (1 : ℤ) else 0) = initial (j.natAdd 42) := by decide +kernel
      let j : Fin 54 := ⟨s.val - 42, by omega⟩
      have he : s = j.natAdd 42 := by apply Fin.ext; dsimp [j]; omega
      rw [he]
      exact new_counts j

attribute [local irreducible] a

theorem result (n : ℕ) :
    (a (n + 24) : ℤ) = 90 * a (n + 23) - 3573 * a (n + 22) + 83214 * a (n + 21) - 1278486 * a (n + 20) + 13836015 * a (n + 19) - 110021385 * a (n + 18) + 661896144 * a (n + 17) - 3076398702 * a (n + 16) + 11214272853 * a (n + 15) - 32398609896 * a (n + 14) + 74677395474 * a (n + 13) - 137758028106 * a (n + 12) + 203308881255 * a (n + 11) - 239066083215 * a (n + 10) + 222060410955 * a (n + 9) - 160604595216 * a (n + 8) + 88409012652 * a (n + 7) - 35729023024 * a (n + 6) + 9979813584 * a (n + 5) - 1718948736 * a (n + 4) + 137388096 * a (n + 3) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal ProperTransfer.between 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal ProperTransfer.between id (bondDefects ProperTransfer.between) Valid cl T initial terminal 2
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2
  have tab (i : Fin 25) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact HardinA229604StripPowers.steps.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (funext (HardinA229604StripPowers.steps.2 i)).symm
  have poly : forward T initial (3 + 21) =
      ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) • forward T initial (3 + j.val) := by
    rw [tab ⟨24, by omega⟩]
    simp_rw [show ∀ j : Fin 21, forward T initial (3 + j.val) = W ⟨3 + j.val, by omega⟩
      from fun j => tab ⟨3 + j.val, by omega⟩]
    rw [show (⟨24, by omega⟩ : Fin 25) = (24 : Fin 25) by decide]
    funext s
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      HardinA229604StripPowers.relation s
  have scale (m : ℕ)  :
      literalCount (q := 3) horizontal ProperTransfer.between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let predicate : (Fin (m + 1) × Fin 6 → Fin 3) → Prop := fun f =>
      defects horizontal ProperTransfer.between (List.ofFn fun i j => f (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ f, predicate (e ∘ f) ↔ predicate f := by
      intro e f
      change defects horizontal ProperTransfer.between _ = 2 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
        (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ f, predicate f → ∃ x y, f x ≠ f y := by
      intro f h
      by_contra he
      push_neg at he
      have const : f = fun _ => f (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal ProperTransfer.between _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 5 ∧ ProperTransfer.between.card = 6 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 6) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) predicate invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, predicate]
  have bridge (m : ℕ)  :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m]
    push_cast
    rfl
  have scalar (i : Fin 25) : dotProduct (W i) terminal =
      dotProduct initial ((T ^ i.val).mulVec terminal) := by
    rw [← tab i, DefectTransfer.forward_eq, ← Matrix.dotProduct_mulVec]
  have h : dotProduct initial ((T ^ (n + 23)).mulVec terminal) =
      ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) *
        dotProduct initial ((T ^ (n + 2 + j.val)).mulVec terminal) := by
    cases n with
    | zero =>
      have h := HardinA229604StripPowers.initial_relation
      have h23 : (23 : Fin 25).val = 23 := by decide +kernel
      simpa only [scalar, h23, Nat.zero_add] using h
    | succ m =>
      have h := forward_shift T initial terminal 21 3 ![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] poly m
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 2)
  have h1 := bridge (n + 3)
  have h2 := bridge (n + 4)
  have h3 := bridge (n + 5)
  have h4 := bridge (n + 6)
  have h5 := bridge (n + 7)
  have h6 := bridge (n + 8)
  have h7 := bridge (n + 9)
  have h8 := bridge (n + 10)
  have h9 := bridge (n + 11)
  have h10 := bridge (n + 12)
  have h11 := bridge (n + 13)
  have h12 := bridge (n + 14)
  have h13 := bridge (n + 15)
  have h14 := bridge (n + 16)
  have h15 := bridge (n + 17)
  have h16 := bridge (n + 18)
  have h17 := bridge (n + 19)
  have h18 := bridge (n + 20)
  have h19 := bridge (n + 21)
  have h20 := bridge (n + 22)
  have h21 := bridge (n + 23)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604Strip
