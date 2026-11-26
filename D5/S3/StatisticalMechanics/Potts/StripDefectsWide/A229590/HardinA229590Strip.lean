/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate
   digest: The one-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229590Strip.result)
a: proof_shape=bind-only; consumers=scale_count, result
finite_certificate: proof_shape=bind-only; consumers=count_transfer, result
count_transfer: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31329)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact five-row one-defect class transfers and suffix counts. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
  (bondDefects defects literalCount lumped_count)
open HardinA229590StripData
set_option maxRecDepth 100000
set_option Elab.async false

def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 5 × Fin n → Fin 3 =>
    @Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 5 × Fin n → Fin 3 =>
    defects ∅ between (List.ofFn fun j i => A (i, j)) = 1 ∧
    (@Canonical (Fin 5 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

set_option maxHeartbeats 0 in
theorem finite_certificate :
    (∀ p (d : Fin 2) (s : Fin 41 ⊕ Fin 41),
      (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
        cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ s : Fin 41 ⊕ Fin 41,
      (∑ r : Fin 5 → Fin 3, if cl (boundary r) 1 = s then (1 : ℤ) else 0) = initial s) ∧
    (T ^ (4+14)).mulVec terminal =
      ∑ j : Fin 14, (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ) • (T ^ (4+j.val)).mulVec terminal :=
  ⟨HardinA229590StripCut.transition_counts, HardinA229590StripCut.initial_counts,
    HardinA229590StripPowers.power_polynomial⟩

attribute [local irreducible] a T initial terminal cl

set_option maxHeartbeats 0 in
private theorem count_transfer (m : ℕ) :
    (literalCount (q := 3) ∅ between 1 (m+1) : ℤ) =
      dotProduct initial ((T ^ m).mulVec terminal) := by
  apply lumped_count ∅ between boundary cross (fun (_ : Col) d => d ≤ 1)
    cl T initial terminal 1
  · intro r t
    simp only [cross, HardinA229590StripCut.column_boundary]
  · intro p d hd
    by_cases h : d = 0 <;> simp [terminal, cl, h]
  · intro p d hd r hr
    change d - (cross p r + bondDefects ∅ r r) ≤ 1
    omega
  · intro p d hd s
    simpa only [bondDefects, Finset.filter_empty, Finset.card_empty, add_zero] using
      finite_certificate.1 p ⟨d, by omega⟩ s
  · intro r hr
    change 1 - bondDefects ∅ r r ≤ 1
    omega
  · intro s
    simpa only [bondDefects, Finset.filter_empty, Finset.card_empty,
      zero_le, true_and, Nat.sub_zero] using finite_certificate.2.1 s

set_option maxHeartbeats 0 in
private theorem scale_count (m : ℕ) : literalCount (q := 3) ∅ between 1 (m + 1) = 6 * a (m + 1) := by
  classical
  let S : (Fin 5 × Fin (m + 1) → Fin 3) → Prop := fun A =>
    defects ∅ between (List.ofFn fun j i => A (i, j)) = 1
  have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    change defects ∅ between _ = 1 ↔ _
    rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
      (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.relabel_defects]
  have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
    intro A h
    by_contra he
    push Not at he
    have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
    change defects ∅ between _ = 1 at h
    rw [const] at h
    simp only [List.ofFn_const] at h
    rw [D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer.constant_defects] at h
    have cards : (∅ : Finset (Fin 5 × Fin 5)).card = 0 ∧ between.card = 9 := by decide +kernel
    rw [cards.1, cards.2] at h
    omega
  have orbit := @canonical_pattern_card (Fin 5 × Fin (m + 1)) inferInstance
    (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
  let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 5)) (Equiv.refl (Fin 3))
  have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
    defects ∅ between (List.ofFn fun i j => A (i, j)) = 1) (q := S) (fun _ => Iff.rfl))
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
  unfold literalCount a
  convert card.trans orbit using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]

set_option maxHeartbeats 0 in
theorem result (n : ℕ) :
    (a (n + 19) : ℤ) = 32 * (a (n + 18) : ℤ) - 384 * (a (n + 17) : ℤ) + 2200 * (a (n + 16) : ℤ) - 6494 * (a (n + 15) : ℤ) + 9016 * (a (n + 14) : ℤ) - 816 * (a (n + 13) : ℤ) - 14888 * (a (n + 12) : ℤ) + 18879 * (a (n + 11) : ℤ) - 5464 * (a (n + 10) : ℤ) - 7472 * (a (n + 9) : ℤ) + 8336 * (a (n + 8) : ℤ) - 3648 * (a (n + 7) : ℤ) + 768 * (a (n + 6) : ℤ) - 64 * (a (n + 5) : ℤ) := by
  have bridge (m : ℕ) : dotProduct initial ((T ^ m).mulVec terminal) =
      6 * (a (m+1) : ℤ) := by
    rw [← count_transfer, scale_count]
    push_cast
    rfl
  have h := congrArg (fun w => dotProduct initial ((T ^ n).mulVec w))
    finite_certificate.2.2
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← pow_add, dotProduct_sum, dotProduct_smul, smul_eq_mul] at h
  simp_rw [bridge] at h
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, Fin.val_one, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Nat.reduceAdd, Nat.add_assoc] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
