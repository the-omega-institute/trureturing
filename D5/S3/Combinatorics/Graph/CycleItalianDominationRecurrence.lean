/- GID: D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CycleItalianDominationRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Italian dominating functions on labelled cycles obey an order-five recurrence. -/

/-
proof_shape: result: content
escape_witness: a_trace_T proves the all-length count/closed-walk trace identity by
  the explicit closedEquiv bijection and the inductive sum_pathWeight enumeration.
admission_basis: open-problem-resolution (#12435; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Private content:
  sum_pathWeight: induction and Fin.consEquiv reindex all intermediate states;
    the escape is the arbitrary-length matrix path-sum identity.
  closedEquiv: constructs inverse maps between Italian functions and overlapping
    closed state sequences; the escape is the verified counting correspondence.
  a_trace_T: the live bijection and path enumeration identify a closed-edge product
    with a zero/one indicator and establish its cardinality/trace identity.
Utility none: the result is a universal counting theorem proved by induction and
  an explicit bijection, not a bounded enumeration, checker, numerical reduction,
  or certified instance; finite matrix identities are internal proof steps.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Linarith

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence

private abbrev State := Fin 3 × Fin 3

def IsItalian {n : ℕ} (f : Fin n → Fin 3) : Prop :=
  ∀ i, f i = 0 → 2 ≤ (f ((finRotate n).symm i)).val + (f (finRotate n i)).val

private instance italianDecidable {n : ℕ} (f : Fin n → Fin 3) : Decidable (IsItalian f) := by
  unfold IsItalian
  infer_instance

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin 3 => IsItalian f)).card

def claim : Prop :=
  (∀ n : ℕ, 3 ≤ n → (a (n + 5) : ℤ) =
    2 * (a (n + 4) : ℤ) + 2 * (a (n + 3) : ℤ) + (a (n + 2) : ℤ) -
      (a (n + 1) : ℤ) - (a n : ℤ)) ∧
  a 3 = 23 ∧ a 4 = 60 ∧ a 5 = 167 ∧ a 6 = 467 ∧ a 7 = 1297

private def Edge (s t : State) : Prop :=
  t.1 = s.2 ∧ (s.2 ≠ 0 ∨ 2 ≤ s.1.val + t.2.val)

private instance edgeDecidable : DecidableRel Edge := fun s t =>
  inferInstanceAs (Decidable (t.1 = s.2 ∧ (s.2 ≠ 0 ∨ 2 ≤ s.1.val + t.2.val)))

private def T : Matrix State State ℤ := fun s t => if Edge s t then 1 else 0

private def pathWeight {α : Type*} (M : Matrix α α ℤ) {n : ℕ}
    (u : α) (f : Fin n → α) (v : α) : ℤ :=
  let g : Fin (n + 1) → α := Fin.cons u f
  (∏ i : Fin n, M (g i.castSucc) (g i.succ)) * M (g (Fin.last n)) v

private theorem sum_pathWeight {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℤ) (n : ℕ) (u v : α) :
    (∑ f : Fin n → α, pathWeight M u f v) = (M ^ (n + 1)) u v := by
  induction n generalizing u with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hcons (x : α) (f : Fin n → α) :
        pathWeight M u (Fin.cons x f) v = M u x * pathWeight M x f v := by
      simp only [pathWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.cons_last, Fin.castSucc_zero, Fin.castSucc_succ]
      ring
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp
      (fun f => pathWeight M u f v), Fintype.sum_prod_type]
    change (∑ x : α, ∑ f : Fin n → α, pathWeight M u (Fin.cons x f) v) = _
    simp_rw [hcons, ← Finset.mul_sum, ih]
    conv_rhs => rw [pow_succ', Matrix.mul_apply]

private def cycleWeight {α : Type*} (M : Matrix α α ℤ) {n : ℕ}
    (f : Fin (n + 1) → α) : ℤ :=
  (∏ i : Fin n, M (f i.castSucc) (f i.succ)) * M (f (Fin.last n)) (f 0)

private def Closed {n : ℕ} (f : Fin n → State) : Prop :=
  ∀ i, Edge (f i) (f (finRotate n i))

private def closedEquiv (n : ℕ) :
    {f : Fin n → Fin 3 // IsItalian f} ≃ {s : Fin n → State // Closed s} where
  toFun f := ⟨(fun i => (f.val ((finRotate n).symm i), f.val i)), by
    intro i
    constructor
    · simp only [Equiv.symm_apply_apply]
    · by_cases hi : f.val i = 0
      · exact Or.inr (f.property i hi)
      · exact Or.inl hi⟩
  invFun s := ⟨(fun i => (s.val i).2), by
    intro i hi
    have hprev := (s.property ((finRotate n).symm i)).1
    simp only [Equiv.apply_symm_apply] at hprev
    have hc := (s.property i).2
    rcases hc with hc | hc
    · exact (hc hi).elim
    · simpa only [hprev] using hc⟩
  left_inv f := by rfl
  right_inv s := by
    apply Subtype.ext
    funext i
    apply Prod.ext
    · have hprev := (s.property ((finRotate n).symm i)).1
      simp only [Equiv.apply_symm_apply] at hprev
      exact hprev.symm
    · rfl

private theorem a_trace_T (n : ℕ) :
    (a (n + 1) : ℤ) = Matrix.trace (T ^ (n + 1)) := by
  classical
  have hw (f : Fin (n + 1) → State) :
      cycleWeight T f = if Closed f then 1 else 0 := by
    have hprod : cycleWeight T f =
        ∏ i : Fin (n + 1), T (f i) (f (finRotate (n + 1) i)) := by
      rw [Fin.prod_univ_castSucc]
      have hr (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ :=
        finRotate_of_lt i.isLt
      simp only [hr, finRotate_last]
      rfl
    rw [hprod]
    by_cases h : Closed f
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i _
      exact if_pos (h i)
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hi
  have hc : a (n + 1) = (Finset.univ.filter
      (fun s : Fin (n + 1) → State => Closed s)).card := by
    simpa only [a, Fintype.card_subtype] using Fintype.card_congr (closedEquiv (n + 1))
  have hcycle : (∑ f : Fin (n + 1) → State, cycleWeight T f) =
      Matrix.trace (T ^ (n + 1)) := by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => State)).sum_comp
      (fun f => cycleWeight T f), Fintype.sum_prod_type]
    change (∑ u : State, ∑ f : Fin n → State, pathWeight T u f u) = _
    simp_rw [sum_pathWeight]
    rfl
  rw [hc, ← hcycle]
  simp_rw [hw]
  exact (Finset.sum_boole Closed Finset.univ).symm

private def group (s : State) : Fin 5 :=
  if s.2 = 0 then ⟨s.1.val, by omega⟩ else if s.2 = 1 then 3 else 4
private def rep : Fin 5 → State := ![(0, 0), (1, 0), (2, 0), (0, 1), (0, 2)]
private def Q : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0,0,0,0,1; 0,0,0,1,1; 1,0,0,1,1; 0,1,0,1,1; 0,0,1,1,1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the finite factorization and matrix polynomial identities.
theorem result : claim := by
  have ha (n : ℕ) (hn : 0 < n) : (a n : ℤ) = Matrix.trace (Q ^ n) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    let R : Matrix State (Fin 5) ℤ :=
      (1 : Matrix (Fin 5) (Fin 5) ℤ).submatrix group id
    let S : Matrix (Fin 5) State ℤ := T.submatrix rep id
    have hfactor : T = R * S := by decide
    have hquot : S * R = Q := by decide
    have hp (k : ℕ) : (R * S) ^ k * R = R * (S * R) ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          (R * S) ^ (k + 1) * R = ((R * S) ^ k * R) * (S * R) := by
            rw [pow_succ]
            simp only [Matrix.mul_assoc]
          _ = (R * (S * R) ^ k) * (S * R) := by rw [ih]
          _ = R * (S * R) ^ (k + 1) := by rw [Matrix.mul_assoc, pow_succ]
    rw [a_trace_T, hfactor]
    calc
      Matrix.trace ((R * S) ^ (m + 1)) = Matrix.trace (((R * S) ^ m * R) * S) := by
        rw [pow_succ, Matrix.mul_assoc]
      _ = Matrix.trace ((R * (S * R) ^ m) * S) := by rw [hp]
      _ = Matrix.trace (S * (R * (S * R) ^ m)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((S * R) ^ (m + 1)) := by rw [← Matrix.mul_assoc, pow_succ']
      _ = Matrix.trace (Q ^ (m + 1)) := by rw [hquot]
  have hrec (n : ℕ) :
      Matrix.trace (Q ^ (n + 5)) = 2 * Matrix.trace (Q ^ (n + 4)) +
        2 * Matrix.trace (Q ^ (n + 3)) + Matrix.trace (Q ^ (n + 2)) -
        Matrix.trace (Q ^ (n + 1)) - Matrix.trace (Q ^ n) := by
    have hpoly : Q ^ 5 - 2 • Q ^ 4 - 2 • Q ^ 3 - Q ^ 2 + Q + 1 = 0 := by decide
    have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℤ => Matrix.trace (Q ^ n * M))
      hpoly
    simp only [mul_sub, mul_add, ← pow_add, mul_one, mul_zero,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_zero, two_nsmul, ← pow_succ] at h
    linarith
  constructor
  · intro n hn
    rw [ha (n + 5) (by omega), ha (n + 4) (by omega), ha (n + 3) (by omega),
      ha (n + 2) (by omega), ha (n + 1) (by omega), ha n (by omega)]
    exact hrec n
  · have h3 : (a 3 : ℤ) = 23 := by rw [ha 3 (by omega)]; decide
    have h4 : (a 4 : ℤ) = 60 := by rw [ha 4 (by omega)]; decide
    have h5 : (a 5 : ℤ) = 167 := by rw [ha 5 (by omega)]; decide
    have h6 : (a 6 : ℤ) = 467 := by rw [ha 6 (by omega)]; decide
    have h7 : (a 7 : ℤ) = 1297 := by rw [ha 7 (by omega)]; decide
    exact ⟨by exact_mod_cast h3, by exact_mod_cast h4, by exact_mod_cast h5,
      by exact_mod_cast h6, by exact_mod_cast h7⟩

end D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence
