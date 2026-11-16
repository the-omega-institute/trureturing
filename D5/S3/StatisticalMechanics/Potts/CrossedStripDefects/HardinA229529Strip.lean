/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229529Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229529Strip.result)
Row: proof_shape=bind-only; consumers=result
horizontal: proof_shape=bind-only; consumers=result
between: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
cl: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
T: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
initial: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=result
W: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
finite_certificate: proof_shape=bind-only; consumers=result, HardinA229632Strip.finite_certificate
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31121)
-/

import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229529Strip
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev Row := Fin 3 → Fin 3
private def horizontal : Finset (Fin 3 × Fin 3) := HardinA229581Strip.horizontal
def between : Finset (Fin 3 × Fin 3) :=
  HardinA229581Strip.antidiagonal ∪ HardinA229581Strip.antidiagonal.image Prod.swap
def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 1 ∧ bondDefects horizontal p p ≤ 1 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Row) (d : ℕ) : Fin 5 :=
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = true then 0 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = false then 1 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = true then 2 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinThinGraphTransport.boundaryClass p = false then 3 else
  4
def T : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![(HardinThinGraphTransport.K true true : ℤ), (HardinThinGraphTransport.K true false : ℤ), 0, 2, 2],
    ![(HardinThinGraphTransport.K false true : ℤ), (HardinThinGraphTransport.K false false : ℤ), 2, 0, 0],
    ![0, 0, (HardinThinGraphTransport.K true true : ℤ), (HardinThinGraphTransport.K true false : ℤ), 0],
    ![0, 0, (HardinThinGraphTransport.K false true : ℤ), (HardinThinGraphTransport.K false false : ℤ), 0],
    ![0, 0, 1, 0, 0]]
def initial : Fin 5 → ℤ := ![6, 6, 0, 0, 12]
private def terminal : Fin 5 → ℤ := ![0, 0, 1, 1, 1]
def W : Fin 6 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 12],
    ![30, 24, 24, 12, 12],
    ![138, 108, 156, 132, 60],
    ![630, 492, 1008, 852, 276],
    ![2874, 2244, 5988, 4980, 1260],
    ![13110, 10236, 33672, 27684, 5748]]

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin n × Fin 3 → Fin 3 =>
    @Canonical (Fin n × Fin 3)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin n × Fin 3 → Fin 3 =>
    defects horizontal between (List.ofFn fun i j => A (i, j)) = 1 ∧
    (@Canonical (Fin n × Fin 3)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 5,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 5, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 5, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 5 = ∑ j : Fin 4, (![-4, 20, -29, 10] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  have cut : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 5,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) =
        if HardinThinGraphTransport.proper p ∧ ((d.val = 1 ∧ s = 0) ∨ (d.val = 1 ∧ s = 1) ∨ (d.val = 0 ∧ s = 2) ∨ (d.val = 0 ∧ s = 3)) then
          ((∑ q : Row, if HardinThinGraphTransport.proper q ∧
            HardinThinGraphTransport.compatible true p q ∧
            HardinThinGraphTransport.boundaryClass q = decide (s = 0 ∨ s = 2)
            then 1 else 0 : ℕ) : ℤ)
        else T (cl p d.val) s := by decide +kernel
  have table : ∀ p (d : Fin 2) (s : Fin 5),
      HardinThinGraphTransport.proper p ∧ ((d.val = 1 ∧ s = 0) ∨ (d.val = 1 ∧ s = 1) ∨ (d.val = 0 ∧ s = 2) ∨ (d.val = 0 ∧ s = 3)) →
      (HardinThinGraphTransport.K (HardinThinGraphTransport.boundaryClass p)
        (decide (s = 0 ∨ s = 2)) : ℤ) = T (cl p d.val) s := by decide +kernel
  intro p d hp s
  rw [cut p d hp s]
  split_ifs with hz
  · rw [HardinThinGraphTransport.transition_counts.2 true p hz.1]
    exact table p d s hz
  · rfl


attribute [local irreducible] a

/-- The registered recurrence at every index at least 6. -/
theorem result (n : ℕ) :
    (a (n + 6) : ℤ) = 10 * a (n + 5) - 29 * a (n + 4) + 20 * a (n + 3) - 4 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 1 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 1
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 6) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (1 + 4) =
      ∑ j : Fin 4, (![-4, 20, -29, 10] j : ℤ) • forward T initial (1 + j.val) := by
    rw [tab ⟨5, by omega⟩]
    simp_rw [show ∀ j : Fin 4, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
      from fun j => tab ⟨1 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 3 → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 1 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 2 ∧ between.card = 4 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 3) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m hm]
    push_cast
    rfl
  have h := forward_shift T initial terminal 4 1 ![-4, 20, -29, 10] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 1) (by omega)
  have h1 := bridge (n + 2) (by omega)
  have h2 := bridge (n + 3) (by omega)
  have h3 := bridge (n + 4) (by omega)
  have h4 := bridge (n + 5) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4
  rw [h0, h1, h2, h3, h4] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229529Strip
