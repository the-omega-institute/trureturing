/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229580Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229580Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229580Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229580Strip.finite_certificate
   digest: The integer recurrence for one-defect normalized three-colour width-2 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none
Row: proof_shape=bind-only; consumers=finite_certificate, count_transfer
Boundary: proof_shape=bind-only; consumers=finite_certificate, count_transfer
horizontal: proof_shape=bind-only; consumers=a, finite_certificate
antidiagonal: proof_shape=bind-only; consumers=a, finite_certificate
boundary: proof_shape=bind-only; consumers=finite_certificate, count_transfer
cross: proof_shape=bind-only; consumers=finite_certificate, count_transfer
Valid: proof_shape=bind-only; consumers=finite_certificate, count_transfer
decidableValid: proof_shape=bind-only; consumers=finite_certificate
cl: proof_shape=bind-only; consumers=finite_certificate, count_transfer
T: proof_shape=bind-only; consumers=finite_certificate, result
initial: proof_shape=bind-only; consumers=finite_certificate, result
terminal: proof_shape=bind-only; consumers=finite_certificate, result
W: proof_shape=bind-only; consumers=finite_certificate, powers_table
cellOrder: proof_shape=bind-only; consumers=Normal, scale_count
Normal: proof_shape=bind-only; consumers=a, scale_count
decidableNormal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=result
edge: proof_shape=bind-only; consumers=count_transfer
finite_certificate: proof_shape=bind-only; consumers=count_transfer, powers_table, polynomial_relation
count_transfer: proof_shape=content; consumers=result
powers_table: proof_shape=bind-only; consumers=polynomial_relation
polynomial_relation: proof_shape=bind-only; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=external sequence A229580
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal defective colourings and their finite boundary transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229580Strip
open DefectTransfer (bondDefects defects literalCount continuation lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

abbrev Row := Fin 2 → Fin 3
abbrev Boundary := Fin 1 → Fin 3
def horizontal : Finset (Fin 2 × Fin 2) :=
  Finset.univ.image fun j : Fin 1 => (j.castSucc, j.succ)
def antidiagonal : Finset (Fin 2 × Fin 2) :=
  Finset.univ.image fun j : Fin 1 => (j.succ, j.castSucc)
def boundary (r : Row) : Boundary := Fin.tail r
def cross (p : Boundary) (r : Row) : ℕ :=
  bondDefects antidiagonal (Fin.cons 0 p) r
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 1 ∧ (Finset.univ.filter fun j : Fin 0 => p j.castSucc = p j.succ).card ≤ 1 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 2 :=
  if d = 1 then 0 else
  1
def T : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![4, 4],
    ![0, 4]]
def initial : Fin 2 → ℤ := ![6, 3]
def terminal : Fin 2 → ℤ := ![0, 1]
def W : Fin 3 → Fin 2 → ℤ :=
  ![![6, 3],
    ![24, 36],
    ![96, 240]]

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 2) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 2 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 2) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 2 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 2) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 2, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- The finite filter ranges over every three-colour array of the indicated shape. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 2 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1 ∧ Normal A).card

private theorem edge (r t : Row) : bondDefects antidiagonal r t = cross (boundary r) t := by
  unfold cross bondDefects
  apply congrArg Finset.card
  ext e
  by_cases he : e ∈ antidiagonal
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  · simp [he]

/-- Counts, budget preservation and the integer polynomial certificate. -/
theorem finite_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 2,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 2, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 2, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 2 = ∑ j : Fin 2, (![-16, 8] j : ℤ) • W ⟨0 + j.val, by omega⟩ := by
  decide +kernel

private theorem count_transfer (n : ℕ) :
    (literalCount (q := 3) horizontal antidiagonal 1 (n + 1) : ℤ) =
      dotProduct initial ((T ^ n).mulVec terminal) := by
  apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 1 edge
  · intro p d h
    exact finite_certificate.1 p ⟨d, by have := h.1; omega⟩ h
  · intro p d h r hr
    exact finite_certificate.2.1 p ⟨d, by have := h.1; omega⟩ h r hr
  · intro p d h s
    exact finite_certificate.2.2.1 p ⟨d, by have := h.1; omega⟩ h s
  · exact finite_certificate.2.2.2.1
  · exact finite_certificate.2.2.2.2.1

private theorem powers_table (i : Fin 3) : forward T initial i.val = W i := by
  induction i using Fin.induction with
  | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = W i.succ
    change forward T initial i.val = W i.castSucc at ih
    rw [ih]
    exact (finite_certificate.2.2.2.2.2.1.2 i).symm

private theorem polynomial_relation :
    forward T initial (0 + 2) =
      ∑ j : Fin 2, (![-16, 8] j : ℤ) • forward T initial (0 + j.val) := by
  rw [powers_table ⟨2, by omega⟩]
  simp_rw [show ∀ j : Fin 2, forward T initial (0 + j.val) = W ⟨0 + j.val, by omega⟩
    from fun j => powers_table ⟨0 + j.val, by omega⟩]
  exact finite_certificate.2.2.2.2.2.2

private theorem scale_count (n : ℕ) (hn : 2 ≤ n) :
    literalCount (q := 3) horizontal antidiagonal 1 n = 6 * a n := by
  classical
  let S : (Fin n × Fin 2 → Fin 3) → Prop := fun A =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 1
  have hinv : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
    intro e A
    have hm : (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) := by
      rw [List.map_ofFn]
      rfl
    change defects horizontal antidiagonal _ = 1 ↔ _
    rw [hm, DefectTransfer.relabel_defects]
  have huse : ∀ A, S A → ∃ i j, A i ≠ A j := by
    intro A ha
    by_contra hh
    push_neg at hh
    let z : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
    have he : A = fun _ => A z := funext fun i => hh i z
    change defects horizontal antidiagonal _ = 1 at ha
    rw [he] at ha
    simp only [List.ofFn_const] at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [DefectTransfer.constant_defects] at ha
    have hc : horizontal.card = 1 ∧ antidiagonal.card = 1 := by decide +kernel
    rw [hc.1, hc.2] at ha
    omega
  have h := @canonical_pattern_card (Fin n × Fin 2) inferInstance (cellOrder n) S hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, S] at h
  unfold literalCount a Normal
  convert h using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] a

/-- Hardin's registered recurrence, with its explicit starting shift. -/
theorem result (n : ℕ) :
    (a (n + 4) : ℤ) = 8 * a (n + 3) - 16 * a (n + 2) := by
  have bridge (m : ℕ) (hm : 2 ≤ m + 1) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← count_transfer, scale_count (m + 1) hm]
    push_cast
    rfl
  have h := forward_shift T initial terminal 2 0 ![-16, 8] polynomial_relation (n + 1)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one] at h
  have h4 := bridge (n + 3) (by omega)
  have h3 := bridge (n + 2) (by omega)
  have h2 := bridge (n + 1) (by omega)
  simp only [Nat.add_zero, show n + 1 + 2 = n + 3 by omega,
    show n + 1 + 1 = n + 2 by omega] at h
  rw [h4, h3, h2] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229580Strip
