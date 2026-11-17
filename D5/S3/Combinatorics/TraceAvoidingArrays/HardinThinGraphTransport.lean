/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
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
boundaryClass: proof_shape=bind-only; consumers=transition_counts, continuation_three
K: proof_shape=bind-only; consumers=transition_counts, continuation_three
transition_counts: proof_shape=bind-only; consumers=continuation_two, continuation_three
colouringEquiv: proof_shape=content; consumers=graph_count and the actual Reg family observations
rowMajor, orderedGraph, literalStrip: actual definitions consumed by literalEquiv
normal_rowMajor, legal_rowMajor, literalEquiv: proof_shape=content; consumers=normalized_transport, path_result
orderedIso: proof_shape=bind-only; consumers=normalized_transport, path_result
strip_preconnected: proof_shape=content; consumers=normalized_transport, path_result
parityColoring, strip_edge: consumed graph facts for normalized_transport and path_result
normalized_transport: proof_shape=content; consumer=normalized_result
square_two_count, square_three_count: proof_shape=bind-only; consumer=normalized_result
normalized_result: proof_shape=content; actual normalized strip equality
proper_cons: proof_shape=bind-only; consumer=proper_count
proper_count: proof_shape=content; consumer=path_result
path_result: proof_shape=content; actual arbitrary-width path count
All helpers are consumed by these results; no terminal generating-series theorem is duplicated.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
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

def boundaryClass (p : Row 2) : Bool := decide (p 0 = p 2)

def K (a b : Bool) : ℕ := if a then (if b then 3 else 2) else 2

theorem transition_counts :
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

noncomputable def colouringEquiv (d : Bool) (n k : ℕ) :
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


open HardinA233251TriangleStrip (widthLegal widthNormal colour_bond_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

/-- The actual row-major enumeration, with a positive-size codomain. -/
def rowMajor (n k : ℕ) : Fin (n + 1) × Fin (k + 1) ≃ Fin (n * (k + 1) + k + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

private theorem rowMajor_val (n k : ℕ) (a : Fin (n + 1) × Fin (k + 1)) :
    (rowMajor n k a).val = a.2.val + (k + 1) * a.1.val := rfl

private theorem rowMajor_lt (n k : ℕ) (a b : Fin (n + 1) × Fin (k + 1)) :
    rowMajor n k a < rowMajor n k b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 := by
  have hstep (i j : Fin (n + 1)) (h : i < j) :
      (k + 1) * i.val + (k + 1) ≤ (k + 1) * j.val := by
    simpa [Nat.mul_add] using Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt h)
  simp only [Fin.lt_def, rowMajor_val]
  constructor
  · intro h
    by_cases hr : a.1 < b.1
    · exact Or.inl hr
    · have he : a.1 = b.1 := by
        apply Fin.ext
        by_contra hn
        have hg : b.1 < a.1 := by simp only [Fin.lt_def] at *; omega
        have hm := hstep b.1 a.1 hg
        have hb := b.2.isLt
        omega
      exact Or.inr ⟨he, by simpa [he] using h⟩
  · rintro (h | ⟨h, hj⟩)
    · have hm := hstep a.1 b.1 h
      have ha := a.2.isLt
      omega
    · simpa [h] using hj

/-- The same graph on its literal row-major indices. -/
def orderedGraph (d : Bool) (n k : ℕ) : SimpleGraph (Fin (n * (k + 1) + k + 1)) :=
  (stripGraph d n k).comap (rowMajor n k).symm

private theorem normal_rowMajor (n k : ℕ) (A : Fin (n + 1) × Fin (k + 1) → Fin 6) :
    HardinGraphNormalization.Normal (A ∘ (rowMajor n k).symm) ↔
      A (0, 0) = 0 ∧ widthNormal (false, false) (fun i j => A (i,j)) := by
  have hz : (rowMajor n k).symm 0 = (0,0) := by
    apply (rowMajor n k).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    simp [rowMajor_val]
  have earlier (a : Fin (n + 1) × Fin (k + 1)) (c : Fin 6) :
      (∃ j, j < rowMajor n k a ∧ A ((rowMajor n k).symm j) = c) ↔
      ∃ i j, (i < a.1 ∨ i = a.1 ∧ j < a.2) ∧ A (i,j) = c := by
    constructor
    · rintro ⟨j,hj,hc⟩
      refine ⟨((rowMajor n k).symm j).1, ((rowMajor n k).symm j).2, ?_, hc⟩
      exact (rowMajor_lt n k _ a).mp (by simpa using hj)
    · rintro ⟨i,j,h,hc⟩
      exact ⟨rowMajor n k (i,j), (rowMajor_lt n k _ a).mpr h, by simpa using hc⟩
  change HardinGraphNormalization.Normal (A ∘ (rowMajor n k).symm) ↔
    A (0,0) = 0 ∧ ∀ i j,
      ((A (i,j) = 2 ∨ A (i,j) = 3 ∨ A (i,j) = 4) →
        false = true ∨ ∃ r t, (r < i ∨ r = i ∧ t < j) ∧ A (r,t) = 1) ∧
      (A (i,j) = 3 → false = true ∨ ∃ r t, (r < i ∨ r = i ∧ t < j) ∧ A (r,t) = 2)
  simp only [HardinGraphNormalization.Normal, HardinA233175PairStrip.good_iff,
    Bool.false_eq_true, false_or, Function.comp_apply, hz]
  constructor
  · rintro ⟨h0,h⟩
    refine ⟨h0, ?_⟩
    intro i j
    have hi := h (rowMajor n k (i,j))
    simpa only [Equiv.symm_apply_apply, earlier] using hi
  · rintro ⟨h0,h⟩
    refine ⟨h0, ?_⟩
    intro t
    obtain ⟨⟨i,j⟩,rfl⟩ := (rowMajor n k).surjective t
    simpa only [Equiv.symm_apply_apply, earlier] using h i j

/-- Literal rectangular arrays, with precisely the selected graph bonds. -/
def literalStrip (d : Bool) (n k : ℕ) :=
  {A : Fin (n + 1) × Fin (k + 1) → Fin 6 //
    widthLegal (fun c => proper (fun j => beta (c j)))
      (fun c e => compatible d (fun j => beta (c j)) (fun j => beta (e j))) A}

private theorem legal_rowMajor (d : Bool) (n k : ℕ)
    (A : Fin (n + 1) × Fin (k + 1) → Fin 6) :
    (HardinGraphNormalization.Normal (A ∘ (rowMajor n k).symm) ∧
      ∀ i j, (orderedGraph d n k).Adj i j →
        (A ∘ (rowMajor n k).symm) i ≠ (A ∘ (rowMajor n k).symm) j ∧
        ((A ∘ (rowMajor n k).symm) i).val + ((A ∘ (rowMajor n k).symm) j).val ≠ 5) ↔
    widthLegal (fun c => proper (fun j => beta (c j)))
      (fun c e => compatible d (fun j => beta (c j)) (fun j => beta (e j))) A := by
  rw [normal_rowMajor]
  have edges : (∀ i j, (orderedGraph d n k).Adj i j →
      (A ∘ (rowMajor n k).symm) i ≠ (A ∘ (rowMajor n k).symm) j ∧
      ((A ∘ (rowMajor n k).symm) i).val + ((A ∘ (rowMajor n k).symm) j).val ≠ 5) ↔
      (∀ i, proper (fun j => beta (A (i,j)))) ∧
        ∀ i : Fin n, compatible d (fun j => beta (A (i.castSucc,j)))
          (fun j => beta (A (i.succ,j))) := by
    rw [← colouring_iff d n k (fun i j => beta (A (i,j)))]
    simp only [colour_bond_iff]
    constructor
    · intro h a b hab
      simpa [orderedGraph] using h (rowMajor n k a) (rowMajor n k b) (by simpa [orderedGraph] using hab)
    · intro h i j hij
      exact h _ _ hij
  rw [edges]
  unfold widthLegal
  have first : (∃ i : Fin (n + 1), i.val = 0 ∧ A (i,0) = 0) ↔ A (0,0) = 0 := by
    constructor
    · rintro ⟨i,hi,h⟩; simpa [show i = 0 from Fin.ext hi] using h
    · intro h; exact ⟨0,rfl,h⟩
  rw [first]
  have next : (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1),
      compatible d (fun j => beta (A (i,j))) (fun j => beta (A (⟨i.val+1,h⟩,j)))) ↔
      ∀ i : Fin n, compatible d (fun j => beta (A (i.castSucc,j)))
        (fun j => beta (A (i.succ,j))) := by
    constructor
    · intro h i; exact h i.castSucc (Nat.succ_lt_succ i.isLt)
    · intro h i hi; exact h ⟨i.val,by omega⟩
  rw [next]
  tauto

/-- Reversible reconstruction of every literal normalized rectangular strip. -/
noncomputable def literalEquiv (d : Bool) (n k : ℕ) :
    literalStrip d n k ≃ HardinGraphNormalization.Legal (orderedGraph d n k) where
  toFun A := ⟨A.val ∘ (rowMajor n k).symm, (legal_rowMajor d n k A.val).mpr A.property⟩
  invFun f := ⟨f.val ∘ rowMajor n k, (legal_rowMajor d n k (f.val ∘ rowMajor n k)).mp
    (by simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using f.property)⟩
  left_inv A := Subtype.ext (by funext a; simp)
  right_inv f := Subtype.ext (by funext a; simp)


private def orderedIso (d : Bool) (n k : ℕ) :
    orderedGraph d n k ≃g stripGraph d n k :=
  SimpleGraph.Iso.comap (rowMajor n k).symm (stripGraph d n k)

private theorem strip_preconnected (d : Bool) (n k : ℕ) (hk : 0 < k) :
    (stripGraph d n k).Preconnected := by
  have horizontal (i : Fin (n + 1)) (j : Fin (k + 1)) :
      (stripGraph d n k).Reachable (i,0) (i,j) := by
    induction j using Fin.induction with
    | zero => exact .rfl
    | succ j ih =>
      exact ih.trans (SimpleGraph.Adj.reachable (Or.inl (Or.inl ⟨i,j,rfl,rfl⟩)))
  have rows (i : Fin (n + 1)) : (stripGraph d n k).Reachable (0,0) (i,0) := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih =>
      cases d
      · exact ih.trans (SimpleGraph.Adj.reachable (Or.inl (Or.inr ⟨i,0,rfl,rfl⟩)))
      · let j : Fin k := ⟨0,hk⟩
        have diagonal : (stripGraph true n k).Adj (i.castSucc,0) (i.succ,j.succ) :=
          Or.inl (Or.inr ⟨i,j,Or.inl ⟨rfl,rfl⟩⟩)
        exact (ih.trans diagonal.reachable).trans (horizontal i.succ j.succ).symm
  intro a b
  exact ((rows a.1).trans (horizontal a.1 a.2)).symm.trans
    ((rows b.1).trans (horizontal b.1 b.2))

private def parityColoring (d : Bool) (n k : ℕ) : (stripGraph d n k).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk
    (fun a => ⟨(a.2.val + if d then 0 else a.1.val) % 2, Nat.mod_lt _ (by decide)⟩)
    (by
      have hf : ∀ a b, forward d n k a b →
          (a.2.val + if d then 0 else a.1.val) % 2 ≠
          (b.2.val + if d then 0 else b.1.val) % 2 := by
        intro a b h
        rcases h with ⟨i,j,rfl,rfl⟩ | h
        · cases d <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_succ] <;> omega
        · cases d
          · rcases h with ⟨i,j,rfl,rfl⟩
            simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_succ]
            omega
          · rcases h with ⟨i,j,h | h⟩ <;> rcases h with ⟨rfl,rfl⟩ <;>
              simp only [↓reduceIte, Fin.val_castSucc, Fin.val_succ] <;> omega
      intro a b h he
      have hv := congrArg Fin.val he
      exact h.elim (fun hab => hf a b hab hv) (fun hba => hf b a hba hv.symm))

private theorem strip_edge (d : Bool) (n k : ℕ) (hk : 0 < k) :
    ∃ a b, (stripGraph d n k).Adj a b := by
  let j : Fin k := ⟨0,hk⟩
  exact ⟨(0,j.castSucc),(0,j.succ),Or.inl (Or.inl ⟨0,j,rfl,rfl⟩)⟩

private theorem normalized_transport (n k : ℕ) (hk : 0 < k)
    (h3 : Nat.card ((stripGraph true n k).Coloring (Fin 3)) =
      Nat.card ((stripGraph false n k).Coloring (Fin 3))) :
    Nat.card (literalStrip true n k) = Nat.card (literalStrip false n k) := by
  have count (d : Bool) := HardinGraphNormalization.connected_count (orderedGraph d n k)
    ((orderedIso d n k).preconnected_iff.mpr (strip_preconnected d n k hk))
    ⟨(parityColoring d n k).comp (orderedIso d n k).toHom⟩
    (by
      obtain ⟨a,b,hab⟩ := strip_edge d n k hk
      exact ⟨(rowMajor n k) a,(rowMajor n k) b,by simpa [orderedGraph] using hab⟩)
  have palette (d : Bool) : Nat.card ((orderedGraph d n k).Coloring (Fin 3)) =
      Nat.card ((stripGraph d n k).Coloring (Fin 3)) :=
    Nat.card_congr (SimpleGraph.coloringCongr (orderedIso d n k) (Equiv.refl _))
  have hd := (count true).2.2
  have hs := (count false).2.2
  rw [palette true,h3] at hd
  rw [palette false] at hs
  rw [Nat.card_congr (literalEquiv true n k), Nat.card_congr (literalEquiv false n k)]
  omega

private theorem square_two_count (n : ℕ) :
    Nat.card (literalStrip false n 1) = HardinA233123SquareStrip.a (n + 1) := by
  classical
  unfold literalStrip
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, HardinA233123SquareStrip.a]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [widthLegal, proper, compatible, Bool.false_eq_true, ↓reduceIte,
    HardinA233123SquareStrip.rowLegal, HardinA233123SquareStrip.bonds,
    colour_bond_iff, Fin.forall_fin_one]
  tauto

private theorem square_three_count (n : ℕ) :
    Nat.card (literalStrip false n 2) = HardinA233124SquareStrip.a (n + 1) := by
  classical
  unfold literalStrip
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, HardinA233124SquareStrip.a]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [HardinA233124SquareStrip.Legal, widthLegal, proper, compatible,
    Bool.false_eq_true, ↓reduceIte, HardinA233251TriangleStrip.rowLegal,
    HardinA233124SquareStrip.bonds, colour_bond_iff]

/-- The all-height transport identifies diagonal six-colour counts with the existing literal square owners. -/
theorem normalized_result (n : ℕ) :
    Nat.card (literalStrip true n 1) = HardinA233123SquareStrip.a (n + 1) ∧
    Nat.card (literalStrip true n 2) = HardinA233124SquareStrip.a (n + 1) :=
  ⟨(normalized_transport n 1 (by decide) (result n).1).trans (square_two_count n),
   (normalized_transport n 2 (by decide) (result n).2).trans (square_three_count n)⟩

private theorem proper_cons {k : ℕ} (c : Fin 3) (f : Row k) :
    proper (Fin.cons c f) ↔ c ≠ f 0 ∧ proper f := by
  simp [proper, Fin.forall_fin_succ]

private theorem proper_count (k : ℕ) :
    (∑ p : Row k, if proper p then 1 else 0) = 3 * 2^k := by
  induction k with
  | zero => simp [proper, Row]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k+2) => Fin 3)).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    have two (a : Fin 3) : (∑ c : Fin 3, if c ≠ a then (1 : ℕ) else 0) = 2 := by
      fin_cases a <;> decide
    calc
      _ = ∑ f : Row k, if proper f then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        change (∑ c : Fin 3, if proper (Fin.cons c f) then 1 else 0) =
          if proper f then 2 else 0
        by_cases hf : proper f
        · simp only [proper_cons, hf, and_true, ite_true]
          exact two (f 0)
        · simp [proper_cons,hf]
      _ = 2 * (∑ f : Row k, if proper f then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        split_ifs <;> simp
      _ = 3 * 2^(k+1) := by rw [ih,pow_succ]; omega

/-- The actual one-row path, including the two-vertex boundary of the closed form. -/
theorem path_result (k : ℕ) :
    2 * Nat.card (literalStrip true 0 (k+1)) = 4^k + 2^k := by
  have h3 : Nat.card ((stripGraph true 0 (k+1)).Coloring (Fin 3)) = 3 * 2^(k+1) := by
    rw [graph_count]
    simpa only [continuation] using proper_count (k+1)
  have h := HardinGraphNormalization.connected_count (orderedGraph true 0 (k+1))
    ((orderedIso true 0 (k+1)).preconnected_iff.mpr (strip_preconnected true 0 (k+1) (by omega)))
    ⟨(parityColoring true 0 (k+1)).comp (orderedIso true 0 (k+1)).toHom⟩
    (by
      obtain ⟨a,b,hab⟩ := strip_edge true 0 (k+1) (by omega)
      exact ⟨(rowMajor 0 (k+1)) a,(rowMajor 0 (k+1)) b,by simpa [orderedGraph] using hab⟩)
  have palette : Nat.card ((orderedGraph true 0 (k+1)).Coloring (Fin 3)) =
      Nat.card ((stripGraph true 0 (k+1)).Coloring (Fin 3)) :=
    Nat.card_congr (SimpleGraph.coloringCongr (orderedIso true 0 (k+1)) (Equiv.refl _))
  have ht := h.2.2
  rw [palette,h3,← Nat.card_congr (literalEquiv true 0 (k+1))] at ht
  have h4 : 4^k = 2^k * 2^k := by rw [← mul_pow]; norm_num
  simp only [Nat.zero_mul, Nat.zero_add, pow_succ] at ht
  nlinarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
