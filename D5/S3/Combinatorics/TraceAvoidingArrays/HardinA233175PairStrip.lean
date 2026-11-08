/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finite_certificate
   digest: Barker's generating function for the literal six-colour two-row exclusion strip count. -/

/-
admission_basis: open-problem-resolution (#27656; Proved)
Registration audit (CLAUDE.md §3.9): finish_fst, finish_snd, good_iff and edge_iff are
declared_unresolved (IE-C050); the unfinished audit is recorded in issue #27943.
escape_witness: none (open-problem-resolution; the settlement is the new content)
Direct frozen dependency: D5.S3.Observer.Separation.BooleanRankThreeK4.beta
(statement_id sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481), the complementary-pair label map.
Pinned Mathlib supplies finite sums and power-series coefficients.
Seen: proof_shape=bind-only; consumers=allowed, advance, good, finish, TailGood, step, v, count, total, seenCode
Col: proof_shape=bind-only; consumers=pairs, compatible, chain, TailGood, step, count, total, counting_bridge
allowed: proof_shape=bind-only; consumers=good, tailGood_cons, step, total, counting_bridge
instDecidableAllowed: proof_shape=bind-only; consumers=instDecidableGood, step, total
advance: proof_shape=bind-only; consumers=good, finish, tailGood_cons, step, total
good: proof_shape=bind-only; consumers=good_iff, TailGood, legal_iff
finish: proof_shape=bind-only; consumers=finish_fst, finish_snd, normal_iff, TailGood, counting_bridge
finish_fst: proof_shape=bind-only; consumers=normal_iff
finish_snd: proof_shape=bind-only; consumers=normal_iff
good_iff: proof_shape=bind-only; consumers=normal_iff
normal: proof_shape=bind-only; consumers=Legal, normal_iff
earlier_iff: proof_shape=bind-only; consumers=normal_iff
normal_iff: proof_shape=bind-only; consumers=legal_iff
pairs: proof_shape=bind-only; consumers=chain, step, total, legal_iff
compatible: proof_shape=bind-only; consumers=edge_iff, chain, step
instDecidableCompatible: proof_shape=bind-only; consumers=instDecidableChain, step
edge_iff: proof_shape=bind-only; consumers=legal_iff
chain: proof_shape=bind-only; consumers=chain_tail, TailGood
chain_tail: proof_shape=bind-only; consumers=legal_iff
Legal: proof_shape=bind-only; consumers=a, legal_iff
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge, initial, err, recurrence, result
legal_iff: proof_shape=bind-only; consumers=counting_bridge
TailGood: proof_shape=bind-only; consumers=tailGood_cons, count, counting_bridge
instDecidableChain: proof_shape=bind-only; consumers=instDecidableTailGood
instDecidableGood: proof_shape=bind-only; consumers=instDecidableTailGood
instDecidableTailGood: proof_shape=bind-only; consumers=count
tailGood_cons: proof_shape=bind-only; consumers=count_eq_v
step: proof_shape=bind-only; consumers=v, table_step0, table_step1, table_step2, table_step3, table_step4, table_step5, table_step6, vector_recurrence
v: proof_shape=bind-only; consumers=count_eq_v, counting_bridge, vector_certificate, finite_certificate, vector_recurrence, total_recurrence, initial, result
count: proof_shape=bind-only; consumers=count_eq_v, counting_bridge
count_eq_v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge, initial_table, finite_certificate, total_recurrence
counting_bridge: proof_shape=bind-only; consumers=initial, error_recurrence
tables: proof_shape=bind-only; consumers=table
seenCode: proof_shape=bind-only; consumers=table
table: proof_shape=bind-only; consumers=table_base, table_step0, table_step1, table_step2, table_step3, table_step4, table_step5, table_step6, v_table, table_certificate, initial_table
table_base: proof_shape=bind-only; consumers=v_table
table_step0: proof_shape=bind-only; consumers=table_steps
table_step1: proof_shape=bind-only; consumers=table_steps
table_step2: proof_shape=bind-only; consumers=table_steps
table_step3: proof_shape=bind-only; consumers=table_steps
table_step4: proof_shape=bind-only; consumers=table_steps
table_step5: proof_shape=bind-only; consumers=table_steps
table_step6: proof_shape=bind-only; consumers=table_steps
table_steps: proof_shape=bind-only; consumers=v_table
v_table: proof_shape=bind-only; consumers=vector_certificate, finite_certificate
table_certificate: proof_shape=bind-only; consumers=vector_certificate
vector_certificate: proof_shape=bind-only; consumers=finite_certificate
initial_table: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=vector_recurrence, initial
vector_recurrence: proof_shape=bind-only; consumers=total_recurrence
total_recurrence: proof_shape=bind-only; consumers=error_recurrence
initial: proof_shape=bind-only; consumers=error_vanish, result
err: proof_shape=bind-only; consumers=error_recurrence, error_vanish, recurrence
error_recurrence: proof_shape=bind-only; consumers=error_vanish
error_vanish: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Six-colour complementary-pair exclusion on two rows, with row-major normalization.
The continuation transfer retains the final top record and both current seen-colour records.
-/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip

open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

abbrev Seen := Bool × Bool
abbrev Col := Fin 2 → Fin 6

def allowed (s : Seen) (c : Fin 6) : Prop :=
  ((c = 2 ∨ c = 3 ∨ c = 4) → s.1 = true) ∧ (c = 3 → s.2 = true)
private instance instDecidableAllowed (s : Seen) (c : Fin 6) : Decidable (allowed s c) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _)))

def advance (s : Seen) (c : Fin 6) : Seen :=
  (s.1 || decide (c = 1), s.2 || decide (c = 2))

def good : {n : ℕ} → Seen → (Fin n → Fin 6) → Prop
  | 0, _, _ => True
  | _n + 1, s, f => allowed s (f 0) ∧ good (advance s (f 0)) (Fin.tail f)

def finish : {n : ℕ} → Seen → (Fin n → Fin 6) → Seen
  | 0, s, _ => s
  | _n + 1, s, f => finish (advance s (f 0)) (Fin.tail f)

theorem finish_fst {n : ℕ} (s : Seen) (f : Fin n → Fin 6) :
    (finish s f).1 = true ↔ s.1 = true ∨ ∃ i, f i = 1 := by
  induction n generalizing s with
  | zero => simp [finish]
  | succ n ih =>
    rw [finish, ih]
    simp [advance, Fin.exists_fin_succ, Fin.tail, or_assoc]

theorem finish_snd {n : ℕ} (s : Seen) (f : Fin n → Fin 6) :
    (finish s f).2 = true ↔ s.2 = true ∨ ∃ i, f i = 2 := by
  induction n generalizing s with
  | zero => simp [finish]
  | succ n ih =>
    rw [finish, ih]
    simp [advance, Fin.exists_fin_succ, Fin.tail, or_assoc]

theorem good_iff {n : ℕ} (s : Seen) (f : Fin n → Fin 6) :
    good s f ↔ ∀ i,
      ((f i = 2 ∨ f i = 3 ∨ f i = 4) →
        s.1 = true ∨ ∃ j, j < i ∧ f j = 1) ∧
      (f i = 3 → s.2 = true ∨ ∃ j, j < i ∧ f j = 2) := by
  induction n generalizing s with
  | zero => simp [good]
  | succ n ih =>
    simp only [good, ih, Fin.forall_fin_succ]
    have hp : ∀ i : Fin n, (0 : Fin (n + 1)) < i.succ := fun i => Nat.zero_lt_succ _
    simp [Fin.tail, Fin.exists_fin_succ, advance, allowed, or_assoc, hp]

private def normal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)

private theorem earlier_iff {n : ℕ} (A : Fin 2 × Fin n → Fin 6)
    (r : Fin 2) (j : Fin n) (c : Fin 6) :
    (∃ q, q.1.val * n + q.2.val < r.val * n + j.val ∧ A q = c) ↔
      (r = 1 ∧ ∃ k, A (0, k) = c) ∨ ∃ k, k < j ∧ A (r, k) = c := by
  simp only [Prod.exists]
  fin_cases r <;> simp only [Fin.exists_fin_two, Fin.val_zero, Fin.val_one,
    Nat.zero_mul, Nat.one_mul, zero_add]
  · constructor
    · rintro (⟨k, hk, hc⟩ | ⟨k, hk, hc⟩)
      · exact Or.inr ⟨k, hk, hc⟩
      · omega
    · rintro (⟨h, _⟩ | ⟨k, hk, hc⟩)
      · simp at h
      · exact Or.inl ⟨k, hk, hc⟩
  · constructor
    · rintro (⟨k, hk, hc⟩ | ⟨k, hk, hc⟩)
      · exact Or.inl ⟨rfl, k, hc⟩
      · exact Or.inr ⟨k, by omega, hc⟩
    · rintro (⟨_, k, hc⟩ | ⟨k, hk, hc⟩)
      · exact Or.inl ⟨k, by omega, hc⟩
      · exact Or.inr ⟨k, by omega, hc⟩

private theorem normal_iff {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :
    normal A ↔ good (false, false) (fun j => A (0, j)) ∧
      good (finish (false, false) (fun j => A (0, j))) (fun j => A (1, j)) := by
  simp only [normal, good_iff, earlier_iff, finish_fst, finish_snd]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · intro h
    constructor
    · intro j
      simpa using h (0, j)
    · intro j
      simpa using h (1, j)
  · rintro ⟨ht, hb⟩ ⟨r, j⟩
    fin_cases r
    · simpa using ht j
    · simpa using hb j

def pairs (c : Col) : Fin 3 × Fin 3 := (beta (c 0), beta (c 1))

private def compatible (p : Fin 3 × Fin 3) (c : Col) : Prop :=
  ∀ r, beta (c r) ≠ p.1 ∧ beta (c r) ≠ p.2

private instance instDecidableCompatible (p : Fin 3 × Fin 3) (c : Col) :
    Decidable (compatible p c) :=
  inferInstanceAs (Decidable (∀ _r : Fin 2, _ ∧ _))

theorem edge_iff (c d : Col) :
    (∀ r s, c r ≠ d s ∧ (c r).val + (d s).val ≠ 5) ↔ compatible (pairs c) d := by
  have h : ∀ x y : Fin 6, (x ≠ y ∧ x.val + y.val ≠ 5) ↔ beta x ≠ beta y := by
    decide +kernel
  simp only [h, compatible, pairs, Fin.forall_fin_two]
  tauto

private def chain : {n : ℕ} → (Fin 3 × Fin 3) → (Fin n → Col) → Prop
  | 0, _, _ => True
  | _n + 1, p, f => compatible p (f 0) ∧ chain (pairs (f 0)) (Fin.tail f)

private theorem chain_tail {n : ℕ} (f : Fin (n + 1) → Col) :
    chain (pairs (f 0)) (Fin.tail f) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simpa [chain, Fin.tail, Fin.forall_fin_succ] using
      (and_congr_right (fun _ => ih (Fin.tail f)))

private def Legal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
  (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 2),
    A (r, j) ≠ A (s, ⟨j.val + 1, h⟩) ∧
      (A (r, j)).val + (A (s, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A

private instance instDecidableNormal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Decidable (normal A) :=
  inferInstanceAs (Decidable (∀ _p : Fin 2 × Fin n, (_ → _) ∧ (_ → _)))

private instance instDecidableLegal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- The literal filtered count, including the zero value at width zero. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 2 × Fin n → Fin 6 => Legal A)).card

private theorem legal_iff {n : ℕ} (f : Fin (n + 1) → Col) :
    Legal (fun p => f p.2 p.1) ↔
      f 0 0 = 0 ∧ good (false, false) (fun j => f j 0) ∧
      good (finish (false, false) (fun j => f j 0)) (fun j => f j 1) ∧
      chain (pairs (f 0)) (Fin.tail f) := by
  have hf : (∃ j : Fin (n + 1), j.val = 0 ∧ f j 0 = 0) ↔ f 0 0 = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = 0 from Fin.ext hj] using h
    · exact fun h => ⟨0, rfl, h⟩
  have he : (∀ (j : Fin (n + 1)) (h : j.val + 1 < n + 1),
      ∀ r s, f j r ≠ f ⟨j.val + 1, h⟩ s ∧
        (f j r).val + (f ⟨j.val + 1, h⟩ s).val ≠ 5) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
    simp only [edge_iff]
    constructor
    · intro h i
      exact h i.castSucc (by simp)
    · intro h j hj
      exact h ⟨j.val, by omega⟩
  rw [Legal, hf, he, normal_iff, ← chain_tail]
  tauto

private def TailGood {n : ℕ} (q t b : Seen) (p : Fin 3 × Fin 3)
    (f : Fin n → Col) : Prop :=
  chain p f ∧ good t (fun i => f i 0) ∧ good b (fun i => f i 1) ∧
    finish t (fun i => f i 0) = q

private instance instDecidableChain {n : ℕ} (p : Fin 3 × Fin 3) (f : Fin n → Col) :
    Decidable (chain p f) := by
  induction n generalizing p with
  | zero => exact isTrue trivial
  | succ n ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)

private instance instDecidableGood {n : ℕ} (s : Seen) (f : Fin n → Fin 6) :
    Decidable (good s f) := by
  induction n generalizing s with
  | zero => exact isTrue trivial
  | succ n ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)

private instance instDecidableTailGood {n : ℕ} (q t b : Seen) (p : Fin 3 × Fin 3)
    (f : Fin n → Col) :
    Decidable (TailGood q t b p f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

private theorem tailGood_cons {n : ℕ} (q t b : Seen) (p : Fin 3 × Fin 3)
    (c : Col) (f : Fin n → Col) :
    TailGood q t b p (Fin.cons c f) ↔
      (compatible p c ∧ allowed t (c 0) ∧ allowed b (c 1)) ∧
        TailGood q (advance t (c 0)) (advance b (c 1)) (pairs c) f := by
  change ((compatible p c ∧ chain (pairs c) f) ∧
    (allowed t (c 0) ∧ good (advance t (c 0)) (fun i => f i 0)) ∧
    (allowed b (c 1) ∧ good (advance b (c 1)) (fun i => f i 1)) ∧
    finish (advance t (c 0)) (fun i => f i 0) = q) ↔ _
  unfold TailGood
  tauto

def step (w : Seen → Seen → Seen → (Fin 3 × Fin 3) → ℤ)
    (q t b : Seen) (p : Fin 3 × Fin 3) : ℤ :=
  ∑ c : Col, if compatible p c ∧ allowed t (c 0) ∧ allowed b (c 1) then
    w q (advance t (c 0)) (advance b (c 1)) (pairs c) else 0

def v : ℕ → Seen → Seen → Seen → (Fin 3 × Fin 3) → ℤ
  | 0, q, t, _, _ => if t = q then 1 else 0
  | k + 1, q, t, b, p => step (v k) q t b p

private def count (n : ℕ) (q t b : Seen) (p : Fin 3 × Fin 3) : ℤ :=
  ∑ f : Fin n → Col, if TailGood q t b p f then 1 else 0

private theorem count_eq_v (n : ℕ) : count n = v n := by
  induction n with
  | zero => funext q t b p; simp [count, TailGood, v, good, finish, chain]
  | succ n ih =>
    funext q t b p
    rw [count, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Col)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ c : Col, ∑ f : Fin n → Col,
      if TailGood q t b p (Fin.cons c f) then (1 : ℤ) else 0) = _
    change _ = step (v n) q t b p
    rw [← ih]
    unfold step count
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible p c ∧ allowed t (c 0) ∧ allowed b (c 1) <;>
      simp [tailGood_cons, h]

def total (w : Seen → Seen → Seen → (Fin 3 × Fin 3) → ℤ) : ℤ :=
  ∑ c : Col, ∑ q : Seen, if c 0 = 0 ∧ allowed q (c 1) then
    w q (false, false) (advance q (c 1)) (pairs c) else 0

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  rw [a, Finset.natCast_card_filter]
  let e : (Fin 2 × Fin (n + 1) → Fin 6) ≃ (Fin (n + 1) → Col) :=
    { toFun := fun A j r => A (r, j)
      invFun := fun f p => f p.2 p.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Col)).sum_comp, Fintype.sum_prod_type]
  unfold total
  apply Finset.sum_congr rfl
  intro c _
  rw [← count_eq_v]
  unfold count
  trans ∑ f : Fin n → Col, ∑ q : Seen,
    if (c 0 = 0 ∧ allowed q (c 1)) ∧
      TailGood q (false, false) (advance q (c 1)) (pairs c) f then (1 : ℤ) else 0
  · apply Finset.sum_congr rfl
    intro f _
    change (if Legal (fun p => (Fin.cons c f : Fin (n + 1) → Col) p.2 p.1) then (1 : ℤ) else 0) = _
    simp only [legal_iff]
    by_cases hc : c 0 = 0
    · have ha : advance (false, false) (c 0) = (false, false) := by rw [hc]; rfl
      simp only [Fin.cons_zero, good, finish, ha]
      change (if c 0 = 0 ∧ (allowed (false, false) (c 0) ∧
        good (false, false) (fun i => f i 0)) ∧
        (allowed (finish (false, false) (fun i => f i 0)) (c 1) ∧
        good (advance (finish (false, false) (fun i => f i 0)) (c 1))
          (fun i => f i 1)) ∧ chain (pairs c) f then (1 : ℤ) else 0) = _
      simp only [TailGood, hc, true_and]
      simp_rw [show ∀ q : Seen,
        (allowed q (c 1) ∧ chain (pairs c) f ∧ good (false, false) (fun i => f i 0) ∧
          good (advance q (c 1)) (fun i => f i 1) ∧
          finish (false, false) (fun i => f i 0) = q) ↔
        (finish (false, false) (fun i => f i 0) = q ∧
          good (false, false) (fun i => f i 0) ∧ allowed q (c 1) ∧
          good (advance q (c 1)) (fun i => f i 1) ∧ chain (pairs c) f) from
        fun q => by tauto]
      simp only [ite_and]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp [allowed]
    · simp [Fin.cons_zero, hc]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : c 0 = 0 ∧ allowed q (c 1) <;> simp [h]
private def tables : Array (Array (Array ℤ)) := #[
  #[
    #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    #[1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1],
    #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    #[1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1],
    #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  ],
  #[
    #[0,0,0,0,4,4,0,4,6,0,0,0,0,6,4,0,4,8,0,0,0,0,4,4],
    #[0,4,6,0,0,0,0,8,4,0,4,8,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[1,0,1,0,0,0,1,0,3,3,0,2,0,0,0,2,0,4,1,0,1,0,0,0],
    #[1,0,3,4,0,2,0,0,0,2,0,4,2,0,2,0,4,4,2,4,12,6,0,4],
    #[0,6,4,4,4,16,2,0,2,0,4,4,2,4,12,8,0,4,0,8,4,4,4,16],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,4,4,0,4,6,0,0,0,0,6,4,0,4,8,0,0,0,0,4,4],
    #[0,4,6,0,0,0,0,8,4,0,4,8,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,2,0,0,0,0,3,1,0],
    #[1,3,0,0,0,0,1,0,0,0,2,0,0,0,0,4,2,0,2,4,0,0,0,0],
    #[1,0,1,0,0,0,1,0,3,3,0,2,0,0,0,2,0,4,1,0,1,0,0,0],
    #[1,0,3,4,0,2,0,0,0,2,0,4,4,0,2,0,8,4,2,4,12,12,2,4],
    #[2,12,4,4,4,16,4,0,2,0,8,4,2,4,12,16,4,4,4,16,4,4,4,16]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[6,0,6,0,4,4,6,4,10,16,0,12,0,16,12,12,12,24,8,0,8,0,4,4],
    #[8,4,12,24,0,16,0,24,16,16,16,32,12,0,12,0,8,8,12,8,20,32,0,24],
    #[0,32,24,24,24,48,16,0,16,0,8,8,16,8,24,48,0,32,0,48,32,32,32,64],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[3,0,3,0,0,0,3,0,3,6,0,6,0,0,0,6,0,8,4,0,4,0,0,0],
    #[4,0,4,8,0,8,0,0,0,8,0,12,10,0,6,0,8,4,6,4,12,36,16,12],
    #[16,36,12,12,12,32,12,0,8,0,8,4,8,4,16,56,32,16,32,56,16,16,16,48],
    #[12,0,12,0,4,4,12,4,16,28,0,24,0,16,12,24,12,40,16,0,16,0,4,4],
    #[16,4,20,40,0,32,0,24,16,32,16,56,32,0,24,0,24,16,24,16,44,104,32,48],
    #[32,104,48,48,48,112,40,0,32,0,24,16,32,16,56,160,64,64,64,160,64,64,64,160]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[32,0,32,0,24,24,32,24,56,96,0,64,0,96,64,64,64,128,48,0,48,0,32,32],
    #[48,32,80,160,0,96,0,160,96,96,96,192,64,0,64,0,48,48,64,48,112,192,0,128],
    #[0,192,128,128,128,256,96,0,96,0,64,64,96,64,160,320,0,192,0,320,192,192,192,384],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[36,0,36,0,12,12,36,12,48,88,0,72,0,40,24,72,24,128,56,0,56,0,16,16],
    #[56,16,72,144,0,112,0,64,32,112,32,208,120,0,72,0,88,40,72,40,144,432,160,144],
    #[160,432,144,144,144,416,176,0,112,0,112,48,112,48,224,736,320,224,320,736,224,224,224,704],
    #[104,0,104,0,48,48,104,48,152,272,0,208,0,176,112,208,112,384,160,0,160,0,64,64],
    #[160,64,224,448,0,320,0,288,160,320,160,608,304,0,208,0,224,128,208,128,400,1056,320,416],
    #[320,1056,416,416,416,1088,448,0,320,0,288,160,320,160,608,1792,640,640,640,1792,640,640,640,
      1792]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[192,0,192,0,128,128,192,128,320,576,0,384,0,576,384,384,384,768,320,0,320,0,192,192],
    #[320,192,512,1024,0,640,0,1024,640,640,640,1280,384,0,384,0,256,256,384,256,640,1152,0,768],
    #[0,1152,768,768,768,1536,640,0,640,0,384,384,640,384,1024,2048,0,1280,0,2048,1280,1280,1280,
      2560],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[432,0,432,0,144,144,432,144,576,1088,0,864,0,576,352,864,352,1536,736,0,736,0,224,224],
    #[736,224,960,1920,0,1472,0,1024,576,1472,576,2688,1280,0,864,0,896,480,864,480,1664,4800,
      1792,1728],
    #[1792,4800,1728,1728,1728,4736,2112,0,1472,0,1344,704,1472,704,2816,8704,3584,2944,3584,8704,
      2944,2944,2944,8448],
    #[1056,0,1056,0,416,416,1056,416,1472,2752,0,2112,0,1728,1088,2112,1088,3840,1792,0,1792,0,
      640,640],
    #[1792,640,2432,4864,0,3584,0,3072,1792,3584,1792,6656,2944,0,2112,0,2048,1216,2112,1216,3968,
      10752,3584,4224],
    #[3584,10752,4224,4224,4224,11008,4864,0,3584,0,3072,1792,3584,1792,6656,19456,7168,7168,7168,
      19456,7168,7168,7168,19456]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[1152,0,1152,0,768,768,1152,768,1920,3584,0,2304,0,3584,2304,2304,2304,4608,2048,0,2048,0,
      1280,1280],
    #[2048,1280,3328,6656,0,4096,0,6656,4096,4096,4096,8192,2304,0,2304,0,1536,1536,2304,1536,
      3840,7168,0,4608],
    #[0,7168,4608,4608,4608,9216,4096,0,4096,0,2560,2560,4096,2560,6656,13312,0,8192,0,13312,8192,
      8192,8192,16384],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[4800,0,4800,0,1728,1728,4800,1728,6528,12544,0,9600,0,7296,4352,9600,4352,17536,8704,0,8704,
      0,2944,2944],
    #[8704,2944,11648,23296,0,17408,0,13568,7680,17408,7680,32256,13824,0,9600,0,9344,5120,9600,
      5120,18304,52992,19456,19200],
    #[19456,52992,19200,19200,19200,52736,24576,0,17408,0,15616,8448,17408,8448,33024,99840,38912,
      34816,38912,99840,34816,34816,34816,98304],
    #[10752,0,10752,0,4224,4224,10752,4224,14976,28672,0,21504,0,18176,11008,21504,11008,39680,
      19456,0,19456,0,7168,7168],
    #[19456,7168,26624,53248,0,38912,0,33792,19456,38912,19456,72704,29952,0,21504,0,20224,11776,
      21504,11776,40448,113152,38912,43008],
    #[38912,113152,43008,43008,43008,114688,53248,0,38912,0,33792,19456,38912,19456,72704,212992,
      77824,77824,77824,212992,77824,77824,77824,212992]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[7168,0,7168,0,4608,4608,7168,4608,11776,22528,0,14336,0,22528,14336,14336,14336,28672,13312,
      0,13312,0,8192,8192],
    #[13312,8192,21504,43008,0,26624,0,43008,26624,26624,26624,53248,14336,0,14336,0,9216,9216,
      14336,9216,23552,45056,0,28672],
    #[0,45056,28672,28672,28672,57344,26624,0,26624,0,16384,16384,26624,16384,43008,86016,0,53248,
      0,86016,53248,53248,53248,106496],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[52992,0,52992,0,19200,19200,52992,19200,72192,140800,0,105984,0,84992,50176,105984,50176,
      195072,99840,0,99840,0,34816,34816],
    #[99840,34816,134656,269312,0,199680,0,162816,93184,199680,93184,370688,148992,0,105984,0,
      98304,55296,105984,55296,200192,580608,212992,211968],
    #[212992,580608,211968,211968,211968,579584,277504,0,199680,0,176128,98304,199680,98304,
      375808,1120256,425984,399360,425984,1120256,399360,399360,399360,1110016],
    #[113152,0,113152,0,43008,43008,113152,43008,156160,304128,0,226304,0,192512,114688,226304,
      114688,418816,212992,0,212992,0,77824,77824],
    #[212992,77824,290816,581632,0,425984,0,368640,212992,425984,212992,794624,312320,0,226304,0,
      205824,119808,226304,119808,423936,1206272,425984,452608],
    #[425984,1206272,452608,452608,452608,1216512,581632,0,425984,0,368640,212992,425984,212992,
      794624,2326528,851968,851968,851968,2326528,851968,851968,851968,2326528]
  ],
  #[
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[45056,0,45056,0,28672,28672,45056,28672,73728,143360,0,90112,0,143360,90112,90112,90112,
      180224,86016,0,86016,0,53248,53248],
    #[86016,53248,139264,278528,0,172032,0,278528,172032,172032,172032,344064,90112,0,90112,0,
      57344,57344,90112,57344,147456,286720,0,180224],
    #[0,286720,180224,180224,180224,360448,172032,0,172032,0,106496,106496,172032,106496,278528,
      557056,0,344064,0,557056,344064,344064,344064,688128],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[580608,0,580608,0,211968,211968,580608,211968,792576,1560576,0,1161216,0,962560,563200,
      1161216,563200,2150400,1120256,0,1120256,0,399360,399360],
    #[1120256,399360,1519616,3039232,0,2240512,0,1875968,1077248,2240512,1077248,4169728,1613824,
      0,1161216,0,1048576,595968,1161216,595968,2183168,6352896,2326528,2322432],
    #[2326528,6352896,2322432,2322432,2322432,6348800,3092480,0,2240512,0,1961984,1110016,2240512,
      1110016,4202496,12435456,4653056,4481024,4653056,12435456,4481024,4481024,4481024,12369920],
    #[1206272,0,1206272,0,452608,452608,1206272,452608,1658880,3264512,0,2412544,0,2068480,
      1216512,2412544,1216512,4481024,2326528,0,2326528,0,851968,851968],
    #[2326528,851968,3178496,6356992,0,4653056,0,4030464,2326528,4653056,2326528,8683520,3317760,
      0,2412544,0,2154496,1249280,2412544,1249280,4513792,12992512,4653056,4825088],
    #[4653056,12992512,4825088,4825088,4825088,13058048,6356992,0,4653056,0,4030464,2326528,
      4653056,2326528,8683520,25427968,9306112,9306112,9306112,25427968,9306112,9306112,9306112,
      25427968]
  ]
]

private def seenCode (s : Seen) : ℕ :=
  (if s.1 then 1 else 0) + (if s.2 then 2 else 0)

private def table (k : ℕ) (q t b : Seen) (p : Fin 3 × Fin 3) : ℤ :=
  let i := 144 * seenCode q + 36 * seenCode t + 9 * seenCode b +
    3 * p.1.val + p.2.val
  ((tables[k]!).getD (i / 24) #[]).getD (i % 24) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem table_base : ∀ q t b p, table 0 q t b p = v 0 q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step0 : ∀ q t b p,
    table 1 q t b p = step (table 0) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step1 : ∀ q t b p,
    table 2 q t b p = step (table 1) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step2 : ∀ q t b p,
    table 3 q t b p = step (table 2) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step3 : ∀ q t b p,
    table 4 q t b p = step (table 3) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step4 : ∀ q t b p,
    table 5 q t b p = step (table 4) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step5 : ∀ q t b p,
    table 6 q t b p = step (table 5) q t b p := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem table_step6 : ∀ q t b p,
    table 7 q t b p = step (table 6) q t b p := by
  decide +kernel

private theorem table_steps : ∀ k : Fin 7, ∀ q t b p,
    table (k.val + 1) q t b p = step (table k.val) q t b p := by
  intro k
  fin_cases k
  · exact table_step0
  · exact table_step1
  · exact table_step2
  · exact table_step3
  · exact table_step4
  · exact table_step5
  · exact table_step6

private theorem v_table (k : ℕ) (hk : k ≤ 7) : v k = table k := by
  induction k with
  | zero => funext q t b p; exact (table_base q t b p).symm
  | succ k ih =>
    funext q t b p
    rw [v, ih (by omega)]
    exact (table_steps ⟨k, by omega⟩ q t b p).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem table_certificate : ∀ q t b p,
    table 7 q t b p = 16 * table 6 q t b p - 32 * table 5 q t b p -
      320 * table 4 q t b p + 512 * table 3 q t b p + 2048 * table 2 q t b p := by
  decide +kernel

/-- The finite continuation identity on every pair of seen-colour records and boundary labels. -/
private theorem vector_certificate : ∀ q t b p,
    v 7 q t b p = 16 * v 6 q t b p - 32 * v 5 q t b p -
      320 * v 4 q t b p + 512 * v 3 q t b p + 2048 * v 2 q t b p := by
  simpa only [v_table 7 (by omega), v_table 6 (by omega), v_table 5 (by omega),
    v_table 4 (by omega), v_table 3 (by omega), v_table 2 (by omega)] using table_certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem initial_table : total (table 0) = 3 ∧ total (table 1) = 8 ∧
    total (table 2) = 80 ∧ total (table 3) = 800 ∧ total (table 4) = 8576 ∧
    total (table 5) = 92672 ∧ total (table 6) = 1009664 := by
  decide +kernel

/-- The finite vector identity and the initial scalar continuation values. -/
theorem finite_certificate :
    (∀ q t b p, v 7 q t b p = 16 * v 6 q t b p - 32 * v 5 q t b p -
      320 * v 4 q t b p + 512 * v 3 q t b p + 2048 * v 2 q t b p) ∧
    total (v 0) = 3 ∧ total (v 1) = 8 ∧ total (v 2) = 80 ∧ total (v 3) = 800 ∧
      total (v 4) = 8576 ∧ total (v 5) = 92672 ∧ total (v 6) = 1009664 := by
  refine ⟨vector_certificate, ?_⟩
  simpa only [v_table 0 (by omega), v_table 1 (by omega), v_table 2 (by omega),
    v_table 3 (by omega), v_table 4 (by omega), v_table 5 (by omega),
    v_table 6 (by omega)] using initial_table

private theorem vector_recurrence (k : ℕ) : ∀ q t b p,
    v (k + 7) q t b p = 16 * v (k + 6) q t b p - 32 * v (k + 5) q t b p -
      320 * v (k + 4) q t b p + 512 * v (k + 3) q t b p + 2048 * v (k + 2) q t b p := by
  induction k with
  | zero => exact finite_certificate.1
  | succ k ih =>
    intro q t b p
    change step (v (k + 7)) q t b p =
      16 * step (v (k + 6)) q t b p - 32 * step (v (k + 5)) q t b p -
      320 * step (v (k + 4)) q t b p + 512 * step (v (k + 3)) q t b p +
      2048 * step (v (k + 2)) q t b p
    unfold step
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible p c ∧ allowed t (c 0) ∧ allowed b (c 1)
    · simpa only [ite_eq_left h] using
        ih q (advance t (c 0)) (advance b (c 1)) (pairs c)
    · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

private theorem total_recurrence (k : ℕ) :
    total (v (k + 7)) = 16 * total (v (k + 6)) - 32 * total (v (k + 5)) -
      320 * total (v (k + 4)) + 512 * total (v (k + 3)) + 2048 * total (v (k + 2)) := by
  unfold total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : c 0 = 0 ∧ allowed q (c 1)
  · simpa only [ite_eq_left h] using
      vector_recurrence k q (false, false) (advance q (c 1)) (pairs c)
  · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

private theorem initial : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 3 ∧ (a 2 : ℤ) = 8 ∧
    (a 3 : ℤ) = 80 ∧ (a 4 : ℤ) = 800 ∧ (a 5 : ℤ) = 8576 ∧
    (a 6 : ℤ) = 92672 ∧ (a 7 : ℤ) = 1009664 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · simpa only [counting_bridge] using finite_certificate.2

private def err (n : ℕ) : ℤ := (a (n + 3) : ℤ) - 12 * (a (n + 2) : ℤ) + 128 * (a n : ℤ)

private theorem error_recurrence (k : ℕ) : err (k + 5) = 4 * err (k + 4) + 16 * err (k + 3) := by
  have h := total_recurrence k
  simp only [← counting_bridge] at h
  simp only [err, Nat.add_assoc]
  linarith

private theorem error_vanish (k : ℕ) : err (k + 2) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 3
    · rcases initial with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
      interval_cases k <;> norm_num only [err, Nat.reduceAdd, h0, h1, h2, h3, h4, h5, h6, h7]
    · have hr := error_recurrence (k - 3)
      have h1 := ih (k - 1) (by omega)
      have h2 := ih (k - 2) (by omega)
      have e1 : k - 3 + 5 = k + 2 := by omega
      have e2 : k - 3 + 4 = k - 1 + 2 := by omega
      have e3 : k - 3 + 3 = k - 2 + 2 := by omega
      rw [e1, e2, e3, h1, h2] at hr
      simpa using hr

private theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 12 * (a (n - 1) : ℤ) - 128 * (a (n - 3) : ℤ) := by
  have h := error_vanish (n - 5)
  simp only [err] at h
  have e1 : n - 5 + 2 + 3 = n := by omega
  have e2 : n - 5 + 2 + 2 = n - 1 := by omega
  have e3 : n - 5 + 2 = n - 3 := by omega
  rw [e1, e2, e3] at h
  linarith

open PowerSeries

/-- Barker's generating-function identity for the literal normalized strip count. -/
theorem result :
    (1 - 4 * X) * (1 - 8 * X - 32 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
        X * (3 - 28 * X - 16 * X ^ 2 + 224 * X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - 4 * X) * (1 - 8 * X - 32 * X ^ 2) * F = _
  have he : (1 - 4 * X) * (1 - 8 * X - 32 * X ^ 2) * F =
      F - 12 * (F * X ^ 1) + 128 * (F * X ^ 3) := by ring
  have hr : (X * (3 - 28 * X - 16 * X ^ 2 + 224 * X ^ 3) : PowerSeries ℤ) =
      3 * X - 28 * X ^ 2 - 16 * X ^ 3 + 224 * X ^ 4 := by ring
  rw [he, hr]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  by_cases hn : 5 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 3 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega)]
    have hh := recurrence n hn
    linarith
  · rcases initial with ⟨h0, h1, h2, h3, h4, _⟩
    interval_cases n <;> norm_num only [h0, h1, h2, h3, h4, ite_true, ite_false]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
