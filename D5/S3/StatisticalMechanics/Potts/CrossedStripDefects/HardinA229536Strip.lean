/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229536Strip.result)
Row: proof_shape=bind-only; consumers=result
horizontal: proof_shape=bind-only; consumers=result
between: proof_shape=bind-only; consumers=result
Valid: proof_shape=bind-only; consumers=result
decidableValid: proof_shape=bind-only; consumers=finite_certificate._proof_2
cl: proof_shape=bind-only; consumers=result
T: proof_shape=bind-only; consumers=result
initial: proof_shape=bind-only; consumers=result
terminal: proof_shape=bind-only; consumers=result
W: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
a: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #31121)
-/

import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open HardinA233177Canonical (Canonical canonical_pattern_card)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev Row := Fin 3 → Fin 3
private def horizontal : Finset (Fin 3 × Fin 3) := HardinA229588Strip.horizontal
def between : Finset (Fin 3 × Fin 3) := {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)}
private def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 1 ∧ bondDefects horizontal p p ≤ 1 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
private def cl (p : Row) (d : ℕ) : Fin 8 :=
  if d = 1 ∧ (HardinColumnContinuations.classH p = 0) then 0 else
  if d = 1 ∧ (HardinColumnContinuations.classH p = 1) then 1 else
  if d = 1 ∧ (HardinColumnContinuations.classH p = 2) then 2 else
  if d = 1 ∧ (HardinColumnContinuations.classH p = 3) then 3 else
  if d = 0 ∧ (HardinColumnContinuations.classH p = 0) then 4 else
  if d = 0 ∧ (HardinColumnContinuations.classH p = 1) then 5 else
  if d = 0 ∧ (HardinColumnContinuations.classH p = 2) then 6 else
  7
private def T : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![(HardinColumnContinuations.Hfull 0 0 : ℤ), (HardinColumnContinuations.Hfull 0 1 : ℤ), (HardinColumnContinuations.Hfull 0 2 : ℤ), (HardinColumnContinuations.Hfull 0 3 : ℤ), 0, 0, 0, 0],
    ![(HardinColumnContinuations.Hfull 1 0 : ℤ), (HardinColumnContinuations.Hfull 1 1 : ℤ), (HardinColumnContinuations.Hfull 1 2 : ℤ), (HardinColumnContinuations.Hfull 1 3 : ℤ), 0, 3, 2, 1],
    ![(HardinColumnContinuations.Hfull 2 0 : ℤ), (HardinColumnContinuations.Hfull 2 1 : ℤ), (HardinColumnContinuations.Hfull 2 2 : ℤ), (HardinColumnContinuations.Hfull 2 3 : ℤ), 0, 4, 1, 0],
    ![(HardinColumnContinuations.Hfull 3 0 : ℤ), (HardinColumnContinuations.Hfull 3 1 : ℤ), (HardinColumnContinuations.Hfull 3 2 : ℤ), (HardinColumnContinuations.Hfull 3 3 : ℤ), 0, 2, 0, 1],
    ![0, 0, 0, 0, (HardinColumnContinuations.Hfull 0 0 : ℤ), (HardinColumnContinuations.Hfull 0 1 : ℤ), (HardinColumnContinuations.Hfull 0 2 : ℤ), (HardinColumnContinuations.Hfull 0 3 : ℤ)],
    ![0, 0, 0, 0, (HardinColumnContinuations.Hfull 1 0 : ℤ), (HardinColumnContinuations.Hfull 1 1 : ℤ), (HardinColumnContinuations.Hfull 1 2 : ℤ), (HardinColumnContinuations.Hfull 1 3 : ℤ)],
    ![0, 0, 0, 0, (HardinColumnContinuations.Hfull 2 0 : ℤ), (HardinColumnContinuations.Hfull 2 1 : ℤ), (HardinColumnContinuations.Hfull 2 2 : ℤ), (HardinColumnContinuations.Hfull 2 3 : ℤ)],
    ![0, 0, 0, 0, (HardinColumnContinuations.Hfull 3 0 : ℤ), (HardinColumnContinuations.Hfull 3 1 : ℤ), (HardinColumnContinuations.Hfull 3 2 : ℤ), (HardinColumnContinuations.Hfull 3 3 : ℤ)]]
private def initial : Fin 8 → ℤ := ![3, 12, 6, 6, 0, 0, 0, 0]
private def terminal : Fin 8 → ℤ := ![0, 0, 0, 0, 1, 1, 1, 1]
private def W : Fin 9 → Fin 8 → ℤ :=
  ![![3, 12, 6, 6, 0, 0, 0, 0],
    ![24, 24, 6, 0, 0, 72, 30, 18],
    ![78, 120, 48, 0, 102, 168, 54, 24],
    ![324, 432, 156, 0, 426, 1128, 492, 120],
    ![1236, 1728, 648, 0, 2472, 4752, 1872, 432],
    ![4848, 6672, 2472, 0, 11568, 22416, 9048, 1728],
    ![18840, 26064, 9696, 0, 54600, 98592, 38952, 6672],
    ![73440, 101424, 37680, 0, 246744, 433968, 171024, 26064],
    ![285984, 395184, 146880, 0, 1098480, 1875936, 734016, 101424]]

/-- The literal row-major canonical filtered array count. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 3 × Fin n → Fin 3 =>
    @Canonical (Fin 3 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 3 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 1 ∧
    (@Canonical (Fin 3 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

private theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 8,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 8, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 8, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 8 = ∑ j : Fin 6, (![-4, 16, -4, -28, -1, 6] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨by decide +kernel, (by
    intro p d hp r hr
    dsimp only [Valid] at hp ⊢
    omega), ?_, by decide +kernel, ?_,
    by decide +kernel, by decide +kernel⟩
  · have cut : ∀ (p r : Row) (d : Fin 2) (s : Fin 8),
        ((d.val = 1 ∧ s.val < 4) ∨ (d.val = 0 ∧ 4 ≤ s.val)) →
        ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s) ↔
          HardinColumnContinuations.cross p r ∧
            HardinColumnContinuations.classH r = ⟨s.val % 4, Nat.mod_lt _ (by omega)⟩) := by
      decide +kernel
    have table : ∀ p (d : Fin 2) (s : Fin 8),
        ((d.val = 1 ∧ s.val < 4) ∨ (d.val = 0 ∧ 4 ≤ s.val)) →
        (HardinColumnContinuations.Hfull (HardinColumnContinuations.classH p)
          ⟨s.val % 4, Nat.mod_lt _ (by omega)⟩ : ℤ) = T (cl p d.val) s := by
      decide +kernel
    have remaining : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 8,
        ¬ ((d.val = 1 ∧ s.val < 4) ∨ (d.val = 0 ∧ 4 ≤ s.val)) →
        (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
          cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
          then (1 : ℤ) else 0) = T (cl p d.val) s := by
      decide +kernel
    intro p d hp s
    by_cases hz : (d.val = 1 ∧ s.val < 4) ∨ (d.val = 0 ∧ 4 ≤ s.val)
    · simp_rw [cut p _ d s hz]
      have h := HardinColumnContinuations.column_certificate.2.1 p
        ⟨s.val % 4, Nat.mod_lt _ (by omega)⟩
      have cast : (∑ r : Row, if HardinColumnContinuations.cross p r ∧
          HardinColumnContinuations.classH r = ⟨s.val % 4, Nat.mod_lt _ (by omega)⟩
          then (1 : ℤ) else 0) =
          (HardinColumnContinuations.Hfull (HardinColumnContinuations.classH p)
            ⟨s.val % 4, Nat.mod_lt _ (by omega)⟩ : ℤ) := by exact_mod_cast h
      exact cast.trans (table p d s hz)
    · exact remaining p d hp s hz
  · have cut : ∀ (r : Row) (s : Fin 4),
        (bondDefects horizontal r r ≤ 1 ∧
          cl r (1 - bondDefects horizontal r r) = s.castAdd 4) ↔
          HardinColumnContinuations.classH r = s := by decide +kernel
    have table : ∀ s : Fin 4, (![3, 12, 6, 6] s : ℕ) = initial (s.castAdd 4) := by
      decide +kernel
    have remaining : ∀ s : Fin 8, 4 ≤ s.val →
        (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
          cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s := by
      decide +kernel
    intro s
    by_cases hs : s.val < 4
    · let j : Fin 4 := ⟨s.val, hs⟩
      have he : s = j.castAdd 4 := rfl
      rw [he]
      simp_rw [cut _ j]
      have h := HardinColumnContinuations.column_certificate.2.2.2 j
      have cast : (∑ r : Row, if HardinColumnContinuations.classH r = j
          then (1 : ℤ) else 0) = (![3, 12, 6, 6] j : ℕ) := by exact_mod_cast h
      exact cast.trans (table j)
    · exact remaining s (by omega)

attribute [local irreducible] a

/-- The registered recurrence at every index at least 9. -/
theorem result (n : ℕ) :
    (a (n + 9) : ℤ) = 6 * a (n + 8) - 1 * a (n + 7) - 28 * a (n + 6) - 4 * a (n + 5) + 16 * a (n + 4) - 4 * a (n + 3) := by
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
  have tab (i : Fin 9) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (2 + 6) =
      ∑ j : Fin 6, (![-4, 16, -4, -28, -1, 6] j : ℤ) • forward T initial (2 + j.val) := by
    rw [tab ⟨8, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (2 + j.val) = W ⟨2 + j.val, by omega⟩
      from fun j => tab ⟨2 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) (hm : 1 ≤ m) :
      literalCount (q := 3) horizontal between 1 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin 3 × Fin (m + 1) → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun j i => A (i, j)) = 1
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 1 ↔ _
      rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
        (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
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
      have cards : horizontal.card = 0 ∧ between.card = 7 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin 3 × Fin (m + 1)) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 3)) (Equiv.refl (Fin 3))
    have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 1) (q := S) (fun _ => Iff.rfl))
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
    unfold literalCount a
    convert card.trans orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale m hm]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 2 ![-4, 16, -4, -28, -1, 6] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 2) (by omega)
  have h1 := bridge (n + 3) (by omega)
  have h2 := bridge (n + 4) (by omega)
  have h3 := bridge (n + 5) (by omega)
  have h4 := bridge (n + 6) (by omega)
  have h5 := bridge (n + 7) (by omega)
  have h6 := bridge (n + 8) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip
