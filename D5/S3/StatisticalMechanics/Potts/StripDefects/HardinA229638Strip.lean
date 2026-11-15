/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229638Strip.result)
Row: proof_shape=bind-only; consumers=finite_certificate, result
horizontal: proof_shape=bind-only; consumers=finite_certificate, result
Valid: proof_shape=bind-only; consumers=finite_certificate, result
cl: proof_shape=bind-only; consumers=finite_certificate, result
T: proof_shape=bind-only; consumers=finite_certificate, result
initial: proof_shape=bind-only; consumers=finite_certificate, result
terminal: proof_shape=bind-only; consumers=finite_certificate, result
W: proof_shape=bind-only; consumers=finite_certificate, result
decidableValid: proof_shape=bind-only; consumers=finite_certificate
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #30838)
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229535Strip
import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal row-major canonical counts and column transfer. -/
open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229638Strip
open HardinA229535Strip (between)
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

abbrev Row := Fin 2 → Fin 3
def horizontal : Finset (Fin 2 × Fin 2) := ∅
def Valid (_ : Row) (d : ℕ) : Prop := d ≤ 2
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (d ≤ 2))
def cl (p : Row) (d : ℕ) : Fin 6 :=
  if d = 2 then (HardinColumnContinuations.classB p).castAdd 4
  else if d = 1 then ((HardinColumnContinuations.classB p).castAdd 2).natAdd 2
  else if d = 0 then (HardinColumnContinuations.classB p).natAdd 4
  else 5
def T : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6)
    (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6)
    (Matrix.fromBlocks (HardinA229535Strip.T)
      (Fin.append (![![0, 4], ![2, 2]])
        (HardinA229535Strip.T.submatrix (fun i : Fin 2 => i.castAdd 2)
          (fun j : Fin 2 => j.natAdd 2)))
      (0)
      (fun i j => (HardinColumnContinuations.B i j : ℤ)))
def initial : Fin 6 → ℤ :=
  Fin.append HardinA229535Strip.initial ![0, 0]
def terminal : Fin 6 → ℤ := ![0, 0, 0, 0, 1, 1]
def W : Fin 7 → Fin 6 → ℤ :=
  Fin.append (fun i => Fin.append (HardinA229535Strip.W i) ((![![0, 0],
      ![12, 24],
      ![60, 180],
      ![348, 384],
      ![1200, 1728]]) i))
    (![![624, 456, 960, 1248, 4464, 5184],
      ![1704, 1248, 3168, 3744, 15024, 17328]])
/-- Literal row-major canonical arrays, with columns swept only to count bonds. -/
def a (n : ℕ) : ℕ :=
  letI : DecidablePred (fun A : Fin 2 × Fin n → Fin 3 =>
    @Canonical (Fin 2 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A) :=
    fun _ => by unfold Canonical; infer_instance
  (Finset.univ.filter fun A : Fin 2 × Fin n → Fin 3 =>
    defects horizontal between (List.ofFn fun j i => A (i, j)) = 2 ∧
    (@Canonical (Fin 2 × Fin n)
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 A)).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 6,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 6, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 6, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 6 = ∑ j : Fin 6, (![8, 24, 12, -16, -6, 6] j : ℤ) • W ⟨0 + j.val, by omega⟩ := by
  decide +kernel

attribute [local irreducible] a

/-- The registered recurrence at every index at least 7. -/
theorem result (n : ℕ) :
    (a (n + 7) : ℤ) = 6 * a (n + 6) - 6 * a (n + 5) - 16 * a (n + 4) + 12 * a (n + 3) + 24 * a (n + 2) + 8 * a (n + 1) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal between 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal between id (bondDefects between) Valid cl T initial terminal 2
      (fun _ _ => rfl)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by change d ≤ 2 at h; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 7) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (0 + 6) =
      ∑ j : Fin 6, (![8, 24, 12, -16, -6, 6] j : ℤ) • forward T initial (0 + j.val) := by
    rw [tab ⟨6, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (0 + j.val) = W ⟨0 + j.val, by omega⟩
      from fun j => tab ⟨0 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal between 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin 2 × Fin (m + 1) → Fin 3) → Prop := fun A =>
      defects horizontal between (List.ofFn fun j i => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal between _ = 2 ↔ _
      rw [show (List.ofFn fun j i => (e ∘ A) (i, j)) =
        (List.ofFn fun j i => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal between _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 0 ∧ between.card = 4 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin 2 × Fin (m + 1)) inferInstance
      (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective) S invariant nonconstant
    let e := Equiv.arrowCongr (Equiv.prodComm (Fin (m + 1)) (Fin 2)) (Equiv.refl (Fin 3))
    have card := Fintype.card_congr (e.subtypeEquiv (p := fun A =>
      defects horizontal between (List.ofFn fun i j => A (i, j)) = 2) (q := S) (fun _ => Iff.rfl))
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit card
    unfold literalCount a
    convert card.trans orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 0 ![8, 24, 12, -16, -6, 6] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h0 := bridge (n + 0)
  have h1 := bridge (n + 1)
  have h2 := bridge (n + 2)
  have h3 := bridge (n + 3)
  have h4 := bridge (n + 4)
  have h5 := bridge (n + 5)
  have h6 := bridge (n + 6)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h0 h1 h2 h3 h4 h5 h6
  rw [h0, h1, h2, h3, h4, h5, h6] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229638Strip
