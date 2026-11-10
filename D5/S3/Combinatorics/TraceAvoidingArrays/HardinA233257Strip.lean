/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.finite_certificate
   digest: Closed form, recurrence and generating function for the antidiagonal pair-exclusion strip. -/
/-
admission_basis: open-problem-resolution (#28792; Proved)
escape_witness: proper_count (last-column transfer induction), two_count (two-label classification).
normal: proof_shape=bind-only; consumers=Legal
Legal: proof_shape=bind-only; consumers=a, literal_card
a: proof_shape=bind-only; consumers=closed_form, recurrence, result
finite_certificate: proof_shape=content; consumers=result
closed_form: proof_shape=content; consumers=recurrence, result
recurrence: proof_shape=content; consumers=result
result: proof_shape=content; consumers=terminal result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def normal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)

def Legal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
  (∀ (j : Fin n) (h : j.val + 1 < n),
    (∀ r : Fin 2, A (r, j) ≠ A (r, ⟨j.val + 1, h⟩) ∧
      (A (r, j)).val + (A (r, ⟨j.val + 1, h⟩)).val ≠ 5) ∧
    (A (1, j) ≠ A (0, ⟨j.val + 1, h⟩) ∧
      (A (1, j)).val + (A (0, ⟨j.val + 1, h⟩)).val ≠ 5)) ∧ normal A

private instance decNormal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :
    Decidable (normal A) := inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decLegal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 2 × Fin n → Fin 6 => Legal A)).card

private def Proper {n : ℕ} (P : Fin 2 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n),
    (∀ r : Fin 2, P (r, j) ≠ P (r, ⟨j.val + 1, h⟩)) ∧
      P (1, j) ≠ P (0, ⟨j.val + 1, h⟩)

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin 2 × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private abbrev RowNormal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :=
  @HardinA233177Canonical.Normal (Fin 2 × Fin n) (cellOrder n).toLT A
private abbrev Canon {n : ℕ} (P : Fin 2 × Fin n → Fin 3) :=
  @HardinA233177Canonical.Canonical (Fin 2 × Fin n) (cellOrder n).toLT 3 P

private theorem literal_card {n : ℕ} (hn : 0 < n) :
    a n = Nat.card {A : Fin 2 × Fin n → Fin 6 //
      Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧ RowNormal A} := by
  classical
  have horder (p q : Fin 2 × Fin n) :
      @LT.lt _ (cellOrder n).toLT p q ↔
        p.1.val * n + p.2.val < q.1.val * n + q.2.val := by
    change p.2.val + n * p.1.val < q.2.val + n * q.1.val ↔ _
    simp only [Nat.add_comm, Nat.mul_comm]
  have hfirst (A : Fin 2 × Fin n → Fin 6) :
      (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ↔ A (0, ⟨0, hn⟩) = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = ⟨0, hn⟩ from Fin.ext hj] using h
    · exact fun h => ⟨⟨0, hn⟩, rfl, h⟩
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Legal, hfirst,
    normal, RowNormal, HardinA233177Canonical.Normal, horder, Proper,
    Function.comp_apply, HardinA233251TriangleStrip.colour_bond_iff]
  tauto

private abbrev Col := Fin 3 × Fin 3
private def step (u v : Col) : Prop := u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ u.2 ≠ v.1
private def cl (_ v : Col) : Fin 2 := if v.1 = v.2 then 0 else 1
private def T : Matrix (Fin 2) (Fin 2) ℤ := !![2, 2; 1, 1]
private def v : Fin 2 → ℤ := ![12, 12]

private theorem transfer_certificate :
    (∀ u w : Col, step u w → ∀ s,
      (∑ z : Col, if step w z ∧ True ∧ cl w z = s then (1 : ℤ) else 0) =
        T (cl u w) s) ∧
    (∀ s, (∑ u : Col, ∑ w : Col,
      if step u w ∧ cl u w = s then (1 : ℤ) else 0) = v s) := by
  decide +kernel

private theorem proper_word {n : ℕ} (P : Fin 2 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good step (fun _ _ _ => True)
      (List.ofFn (fun j => (P (0, j), P (1, j)))) := by
  rw [TransferMatrix.good_iff_local]
  have get (k : ℕ) (hk : k < n) :
      (List.ofFn (fun j => (P (0, j), P (1, j)))).getD k default =
        (P (0, ⟨k, hk⟩), P (1, ⟨k, hk⟩)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  simp only [List.length_ofFn, implies_true, forall_const, and_true]
  constructor
  · intro h k hk
    have hh := h ⟨k, by omega⟩ hk
    simpa only [get k (by omega), get (k+1) hk, step, Fin.forall_fin_two] using hh
  · intro h j hj
    have hh := h j.val hj
    simpa only [get j.val j.isLt, get (j.val+1) hj, step, Fin.forall_fin_two] using hh

private theorem proper_count (n : ℕ) :
    (Nat.card {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P} : ℤ) = 24 * 3 ^ n := by
  classical
  let E : {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P} ≃
      {w : Fin (n+2) → Col // TransferMatrix.good step (fun _ _ _ => True) (List.ofFn w)} := {
    toFun := fun P => ⟨fun j => (P.val (0, j), P.val (1, j)), (proper_word _).mp P.property⟩
    invFun := fun w => ⟨fun p => if p.1 = 0 then (w.val p.2).1 else (w.val p.2).2, by
      apply (proper_word _).mpr
      simpa only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false] using w.property⟩
    left_inv := by
      intro P
      apply Subtype.ext
      funext p
      rcases p with ⟨r, j⟩
      fin_cases r <;> rfl
    right_inv := by intro w; apply Subtype.ext; funext j; exact Prod.eta _ }
  rw [Nat.card_congr E]
  rw [TransferMatrix.cardMatrix step (fun _ _ _ => True) cl T v
    transfer_certificate.1 transfer_certificate.2]
  induction n with
  | zero => norm_num [T, v, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, v, T,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one] at ih ⊢
    rw [pow_succ]
    linear_combination 3 * ih

/-- The empty coefficient and the one-column literal count. -/
theorem finite_certificate : a 0 = 0 ∧ a 1 = 3 := by
  constructor <;> decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
