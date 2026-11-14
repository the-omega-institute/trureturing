/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport
   mirror-E: none
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.transition_counts
   digest: Common boundary counts for distinct diagonal and square strips. -/

/-
admission_basis: escape-witness
Preregistered source obligation: the actual width-two and width-three diagonal
and square proper-colouring counts agree at every positive height.
escape_witness: continuation transport by induction on the number of rows,
consumed by the actual graph-colouring count, without identifying the graphs.
Finite transition counts alone are not an all-height statement.
Helpers are consumed by result; no generating-series theorem is duplicated.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

abbrev Row (k : ℕ) := Fin (k + 1) → Fin 3

def proper {k : ℕ} (p : Row k) : Prop :=
  ∀ j : Fin k, p j.castSucc ≠ p j.succ

def compatible {k : ℕ} (diagonal : Bool) (p q : Row k) : Prop :=
  if diagonal then ∀ j : Fin k,
    p j.castSucc ≠ q j.succ ∧ p j.succ ≠ q j.castSucc
  else ∀ j, p j ≠ q j

instance {k : ℕ} (p : Row k) : Decidable (proper p) :=
  inferInstanceAs (Decidable (∀ j : Fin k, _))

instance {k : ℕ} (d : Bool) (p q : Row k) : Decidable (compatible d p q) := by
  unfold compatible
  infer_instance

private def tailGood {k : ℕ} (d : Bool) : {n : ℕ} → Row k → (Fin n → Row k) → Prop
  | 0, _, _ => True
  | _ + 1, p, f => proper (f 0) ∧ compatible d p (f 0) ∧ tailGood d (f 0) (Fin.tail f)

private instance {k n : ℕ} (d : Bool) (p : Row k) (f : Fin n → Row k) :
    Decidable (tailGood d p f) := by
  induction n generalizing p with
  | zero => exact isTrue trivial
  | succ n ih =>
    exact @instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance (ih _ _))

private def continuation {k : ℕ} (d : Bool) : ℕ → Row k → ℕ
  | 0, _ => 1
  | m + 1, p => ∑ q : Row k, if proper q ∧ compatible d p q then continuation d m q else 0

private theorem tail_count {k : ℕ} (d : Bool) (n : ℕ) (p : Row k) :
    (∑ f : Fin n → Row k, if tailGood d p f then 1 else 0) = continuation d n p := by
  induction n generalizing p with
  | zero => simp [tailGood, continuation]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Row k)).sum_comp,
      Fintype.sum_prod_type]
    change (∑ q : Row k, ∑ f : Fin n → Row k,
      if tailGood d p (Fin.cons q f) then 1 else 0) = _
    rw [continuation]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : proper q ∧ compatible d p q
    · simp [tailGood, h.1, h.2, ih]
    · have hn : ¬ proper q ∨ ¬ compatible d p q := not_and_or.mp h
      rcases hn with h | h <;> simp [tailGood, h]

private def boundaryClass (p : Row 2) : Bool := decide (p 0 = p 2)

private def K (a b : Bool) : ℕ := if a then (if b then 3 else 2) else 2

private theorem transition_counts :
    (∀ (d : Bool) (p : Row 1), proper p →
      (∑ q : Row 1, if proper q ∧ compatible d p q then 1 else 0) = 3) ∧
    (∀ (d : Bool) (p : Row 2), proper p → ∀ b : Bool,
      (∑ q : Row 2, if proper q ∧ compatible d p q ∧ boundaryClass q = b then 1 else 0)
        = K (boundaryClass p) b) := by
  decide +kernel

private def w : ℕ → Bool → ℕ
  | 0, _ => 1
  | n + 1, a => K a true * w n true + K a false * w n false

private theorem continuation_two (d : Bool) (n : ℕ) (p : Row 1) (hp : proper p) :
    continuation d n p = 3 ^ n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [continuation]
    calc
      _ = ∑ q : Row 1, if proper q ∧ compatible d p q then 3 ^ n else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        split_ifs with h
        · exact ih q h.1
        · rfl
      _ = (∑ q : Row 1, if proper q ∧ compatible d p q then 1 else 0) * 3 ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> simp
      _ = 3 ^ (n + 1) := by rw [transition_counts.1 d p hp, pow_succ]; omega

private theorem continuation_three (d : Bool) (n : ℕ) (p : Row 2) (hp : proper p) :
    continuation d n p = w n (boundaryClass p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [continuation, w]
    calc
      _ = ∑ q : Row 2, if proper q ∧ compatible d p q then w n (boundaryClass q) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        split_ifs with h
        · exact ih q h.1
        · rfl
      _ = (∑ q : Row 2, if proper q ∧ compatible d p q ∧ boundaryClass q = true then 1 else 0) * w n true +
          (∑ q : Row 2, if proper q ∧ compatible d p q ∧ boundaryClass q = false then 1 else 0) * w n false := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q _
        cases hq : boundaryClass q <;> by_cases h : proper q ∧ compatible d p q <;>
          simp [hq, h, and_assoc]
      _ = _ := by rw [transition_counts.2 d p hp true, transition_counts.2 d p hp false]

private def forward (d : Bool) (n k : ℕ)
    (a b : Fin (n + 1) × Fin (k + 1)) : Prop :=
  (∃ i : Fin (n + 1), ∃ j : Fin k,
    a = (i, j.castSucc) ∧ b = (i, j.succ)) ∨
  if d then (∃ i : Fin n, ∃ j : Fin k,
    (a = (i.castSucc, j.castSucc) ∧ b = (i.succ, j.succ)) ∨
    (a = (i.castSucc, j.succ) ∧ b = (i.succ, j.castSucc)))
  else (∃ i : Fin n, ∃ j : Fin (k + 1), a = (i.castSucc, j) ∧ b = (i.succ, j))

private theorem forward_ne {d : Bool} {n k : ℕ}
    {a b : Fin (n + 1) × Fin (k + 1)} (h : forward d n k a b) : a ≠ b := by
  rcases h with ⟨i, j, rfl, rfl⟩ | h
  · intro he
    have hh := congrArg (fun x : Fin (n + 1) × Fin (k + 1) => x.2.val) he
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  · cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · rcases h with ⟨i, j, rfl, rfl⟩
      intro he
      have hh := congrArg (fun x : Fin (n + 1) × Fin (k + 1) => x.1.val) he
      simp only [Fin.val_castSucc, Fin.val_succ] at hh
      omega
    · rcases h with ⟨i, j, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩ <;>
        intro he <;>
        have hh := congrArg (fun x : Fin (n + 1) × Fin (k + 1) => x.1.val) he <;>
        simp only [Fin.val_castSucc, Fin.val_succ] at hh <;> omega

/-- Horizontal edges together with both diagonals, or with vertical edges. -/
def stripGraph (d : Bool) (n k : ℕ) : SimpleGraph (Fin (n + 1) × Fin (k + 1)) where
  Adj a b := forward d n k a b ∨ forward d n k b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => forward_ne h rfl) (fun h => forward_ne h rfl)⟩

private theorem colouring_iff (d : Bool) (n k : ℕ) (f : Fin (n + 1) → Row k) :
    (∀ a b, (stripGraph d n k).Adj a b → f a.1 a.2 ≠ f b.1 b.2) ↔
      (∀ i, proper (f i)) ∧ ∀ i : Fin n, compatible d (f i.castSucc) (f i.succ) := by
  constructor
  · intro h
    refine ⟨fun i j => h _ _ (Or.inl (Or.inl ⟨i, j, rfl, rfl⟩)), ?_⟩
    cases d
    · intro i j
      exact h _ _ (Or.inl (Or.inr ⟨i, j, rfl, rfl⟩))
    · intro i j
      exact ⟨h _ _ (Or.inl (Or.inr ⟨i, j, Or.inl ⟨rfl, rfl⟩⟩)),
        h _ _ (Or.inl (Or.inr ⟨i, j, Or.inr ⟨rfl, rfl⟩⟩))⟩
  · rintro ⟨hr, hc⟩
    have hf : ∀ a b, forward d n k a b → f a.1 a.2 ≠ f b.1 b.2 := by
      intro a b hab
      rcases hab with ⟨i, j, rfl, rfl⟩ | hab
      · exact hr i j
      · cases d
        · rcases hab with ⟨i, j, rfl, rfl⟩
          exact hc i j
        · rcases hab with ⟨i, j, hab | hab⟩ <;> rcases hab with ⟨rfl, rfl⟩
          · exact (hc i j).1
          · exact (hc i j).2
    intro a b hab
    exact hab.elim (hf a b) (fun h => (hf b a h).symm)

private theorem tail_local {k : ℕ} (d : Bool) (n : ℕ) (f : Fin (n + 1) → Row k) :
    (proper (f 0) ∧ tailGood d (f 0) (Fin.tail f)) ↔
      (∀ i, proper (f i)) ∧ ∀ i : Fin n, compatible d (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [tailGood, Fin.forall_fin_one]
  | succ n ih =>
    have ht := ih (Fin.tail f)
    simp only [Fin.forall_fin_succ] at ht ⊢
    simp only [tailGood, Fin.tail] at ht ⊢
    tauto

private noncomputable def colouringEquiv (d : Bool) (n k : ℕ) :
    (stripGraph d n k).Coloring (Fin 3) ≃
      {f : Fin (n + 1) → Row k // proper (f 0) ∧ tailGood d (f 0) (Fin.tail f)} where
  toFun p := ⟨fun i j => p (i, j),
    (tail_local d n (fun i j => p (i, j))).mpr
      ((colouring_iff d n k (fun i j => p (i, j))).mp (fun a b h => p.valid h))⟩
  invFun f := SimpleGraph.Coloring.mk (fun a => f.val a.1 a.2)
    (by
      intro a b h
      exact (colouring_iff d n k f.val).mpr
        ((tail_local d n f.val).mp f.property) a b h)
  left_inv p := DFunLike.ext _ _ (fun _ => rfl)
  right_inv f := Subtype.ext rfl

private theorem graph_count (d : Bool) (n k : ℕ) :
    Nat.card ((stripGraph d n k).Coloring (Fin 3)) =
      ∑ p : Row k, if proper p then continuation d n p else 0 := by
  classical
  rw [Nat.card_congr (colouringEquiv d n k), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Row k)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ p : Row k, ∑ f : Fin n → Row k,
    if proper p ∧ tailGood d p f then 1 else 0) = _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : proper p
  · simp only [hp, true_and, ↓reduceIte]
    exact tail_count d n p
  · simp [hp]

/-- Equality of the actual graph-colouring counts at every positive height. -/
theorem result (n : ℕ) :
    Nat.card ((stripGraph true n 1).Coloring (Fin 3)) =
      Nat.card ((stripGraph false n 1).Coloring (Fin 3)) ∧
    Nat.card ((stripGraph true n 2).Coloring (Fin 3)) =
      Nat.card ((stripGraph false n 2).Coloring (Fin 3)) := by
  constructor <;> rw [graph_count, graph_count] <;> apply Finset.sum_congr rfl
  · intro p _
    split_ifs with hp
    · rw [continuation_two true n p hp, continuation_two false n p hp]
    · rfl
  · intro p _
    split_ifs with hp
    · rw [continuation_three true n p hp, continuation_three false n p hp]
    · rfl

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
