/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.finite_certificate
   digest: Four-column king configurations satisfy the Hardin-Barker formulas. -/

/-
admission_basis: open-problem-resolution (#26982; Proved)
escape_witness: count_eq_v proves count k = v k for arbitrary k by first-row decomposition and induction;
counting_bridge transports this invariant to the literal board count.
Direct frozen dependencies: none; all mathematical imports are pinned Mathlib.
a: proof_shape=bind-only; consumers=counting_bridge, initial, recurrence, generating_function, result
Row: proof_shape=bind-only; consumers=ValidRow, Compatible, Safe, step, v, count, total
ValidRow: proof_shape=bind-only; consumers=validRowDecidable, safe_cons, count_zero, step, v
Compatible: proof_shape=bind-only; consumers=compatibleDecidable, safe_cons, step
validRowDecidable: proof_shape=bind-only; consumers=step, v
compatibleDecidable: proof_shape=bind-only; consumers=step
Safe: proof_shape=bind-only; consumers=safeDecidable, safe_cons, count, board_iff
safeDecidable: proof_shape=bind-only; consumers=count, counting_bridge
safe_cons: proof_shape=bind-only; consumers=count_succ
step: proof_shape=bind-only; consumers=v, count_succ, vector_recurrence
v: proof_shape=bind-only; consumers=count_eq_v, finite_certificate, vector_recurrence, total_recurrence
count: proof_shape=bind-only; consumers=count_zero, count_succ, count_eq_v
count_zero: proof_shape=bind-only; consumers=count_eq_v
count_succ: proof_shape=bind-only; consumers=count_eq_v
count_eq_v: proof_shape=content; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge, total_recurrence, initial
board_iff: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=content; consumers=initial, recurrence
finite_certificate: proof_shape=bind-only; consumers=vector_recurrence
vector_recurrence: proof_shape=bind-only; consumers=total_recurrence
total_recurrence: proof_shape=bind-only; consumers=recurrence
initial: proof_shape=bind-only; consumers=generating_function
recurrence: proof_shape=content; consumers=generating_function, result
generating_function: proof_shape=content; consumers=result
result: proof_shape=content; consumers=terminal result
-/

import Mathlib.Data.Nat.Dist
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! Corner-occupied hard-core configurations on a four-column strip. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings

/-- The literal filtered count, with open king adjacency and an occupied top-left corner. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 4 → Bool =>
    (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = true) ∧
    ∀ p q : Fin n × Fin 4, p ≠ q →
      max (Nat.dist p.1.val q.1.val) (Nat.dist p.2.val q.2.val) = 1 →
      ¬ (A p = true ∧ A q = true))).card

abbrev Row := Fin 4 → Bool

def ValidRow (r : Row) : Prop :=
  ∀ j j' : Fin 4, Nat.dist j.val j'.val = 1 → r j = true → r j' = false

def Compatible (r s : Row) : Prop :=
  ∀ j j' : Fin 4, Nat.dist j.val j'.val ≤ 1 → r j = true → s j' = false

private instance validRowDecidable (r : Row) : Decidable (ValidRow r) :=
  inferInstanceAs (Decidable (∀ j j' : Fin 4,
    Nat.dist j.val j'.val = 1 → r j = true → r j' = false))

private instance compatibleDecidable (r s : Row) : Decidable (Compatible r s) :=
  inferInstanceAs (Decidable (∀ j j' : Fin 4,
    Nat.dist j.val j'.val ≤ 1 → r j = true → s j' = false))

private def Safe {n : ℕ} (f : Fin n → Row) : Prop :=
  ∀ i i' : Fin n, ∀ j j' : Fin 4,
    max (Nat.dist i.val i'.val) (Nat.dist j.val j'.val) = 1 →
      f i j = true → f i' j' = false

private instance safeDecidable {n : ℕ} (f : Fin n → Row) : Decidable (Safe f) :=
  inferInstanceAs (Decidable (∀ i i' : Fin n, ∀ j j' : Fin 4,
    max (Nat.dist i.val i'.val) (Nat.dist j.val j'.val) = 1 →
      f i j = true → f i' j' = false))

private theorem safe_cons (k : ℕ) (r : Row) (f : Fin (k + 1) → Row) :
    Safe (Fin.cons r f) ↔ ValidRow r ∧ Compatible r (f 0) ∧ Safe f := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro j j' hd hr
      exact h 0 0 j j' (by simpa using hd) hr
    · intro j j' hd hr
      exact h 0 (Fin.succ 0) j j' (by
        simpa [Nat.dist_zero_left] using
          (max_eq_left hd : max 1 (Nat.dist j.val j'.val) = 1)) hr
    · intro i i' j j' hd hi
      exact h i.succ i'.succ j j' (by simpa only [Fin.val_succ, Nat.dist_succ_succ] using hd) hi
  · rintro ⟨hr, hc, hf⟩ i i' j j'
    refine Fin.cases ?_ (fun t => ?_) i
    · refine Fin.cases ?_ (fun t => ?_) i'
      · intro hd hi
        exact hr j j' (by simpa using hd) hi
      · intro hd hi
        have ht : t = 0 := Fin.ext (show t.val = 0 from by
          simp only [Fin.val_zero, Fin.val_succ, Nat.dist_zero_left] at hd
          omega)
        subst t
        exact hc j j' (by
          simp only [Fin.val_zero, Fin.val_succ, Nat.dist_zero_left] at hd
          omega) hi
    · refine Fin.cases ?_ (fun t' => ?_) i'
      · intro hd hi
        have ht : t = 0 := Fin.ext (show t.val = 0 from by
          simp only [Fin.val_zero, Fin.val_succ, Nat.dist_zero_right] at hd
          omega)
        subst t
        have hd' : Nat.dist j'.val j.val ≤ 1 := by
          rw [Nat.dist_comm]
          simp only [Fin.val_zero, Fin.val_succ, Nat.dist_zero_right] at hd
          omega
        change r j' = false
        cases he : r j' with
        | false => rfl
        | true => have hh := hc j' j hd' he; simp_all
      · intro hd hi
        exact hf t t' j j' (by
          simpa only [Fin.val_succ, Nat.dist_succ_succ] using hd) hi

def step (w : Row → ℤ) (r : Row) : ℤ :=
  if ValidRow r then ∑ s : Row, if Compatible r s then w s else 0 else 0

def v : ℕ → Row → ℤ
  | 0, r => if ValidRow r then 1 else 0
  | k + 1, r => step (v k) r

private def count (k : ℕ) (r : Row) : ℤ :=
  ∑ f : Fin k → Row, if Safe (Fin.cons r f) then 1 else 0

private theorem count_zero (r : Row) : count 0 r = v 0 r := by
  simp [count, v, Safe, ValidRow, Fin.forall_fin_succ]

private theorem count_succ (k : ℕ) (r : Row) :
    count (k + 1) r = step (count k) r := by
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Row)).sum_comp
    (fun f => if Safe (Fin.cons r f) then (1 : ℤ) else 0), Fintype.sum_prod_type]
  change (∑ s : Row, ∑ f : Fin k → Row,
    if Safe (Fin.cons r (Fin.cons s f)) then (1 : ℤ) else 0) = _
  unfold step
  by_cases hr : ValidRow r
  · simp only [hr, ite_true]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hc : Compatible r s <;> simp [safe_cons, hr, hc]
  · simp [safe_cons, hr]

private theorem count_eq_v (k : ℕ) : count k = v k := by
  induction k with
  | zero => funext r; exact count_zero r
  | succ k ih => funext r; rw [count_succ, ih]; rfl

private def total (w : Row → ℤ) : ℤ :=
  ∑ r : Row, if r 0 = true then w r else 0

private theorem board_iff (k : ℕ) (A : Fin (k + 1) × Fin 4 → Bool) :
    ((∃ i : Fin (k + 1), i.val = 0 ∧ A (i, 0) = true) ∧
      ∀ p q : Fin (k + 1) × Fin 4, p ≠ q →
        max (Nat.dist p.1.val q.1.val) (Nat.dist p.2.val q.2.val) = 1 →
        ¬ (A p = true ∧ A q = true)) ↔
      A (0, 0) = true ∧ Safe (fun i j => A (i, j)) := by
  constructor
  · rintro ⟨⟨i, hi, ha⟩, h⟩
    have hi0 : i = 0 := Fin.ext hi
    refine ⟨by simpa [hi0] using ha, ?_⟩
    intro i i' j j' hd ha
    have hne : (i, j) ≠ (i', j') := by
      intro he
      cases he
      simp at hd
    have hh := h (i, j) (i', j') hne hd
    cases he : A (i', j') <;> simp_all
  · rintro ⟨ha, h⟩
    refine ⟨⟨0, rfl, ha⟩, ?_⟩
    rintro ⟨i, j⟩ ⟨i', j'⟩ _ hd ⟨hi, hi'⟩
    have hh := h i i' j j' hd hi
    simp_all

private theorem counting_bridge (k : ℕ) : (a (k + 1) : ℤ) = total (v k) := by
  let e : (Fin (k + 1) × Fin 4 → Bool) ≃ (Fin (k + 1) → Row) := Equiv.curry _ _ _
  have hc : (a (k + 1) : ℤ) =
      ∑ f : Fin (k + 1) → Row, if f 0 0 = true ∧ Safe f then 1 else 0 := by
    rw [a, Finset.natCast_card_filter]
    rw [← e.sum_comp (fun f => if f 0 0 = true ∧ Safe f then (1 : ℤ) else 0)]
    apply Finset.sum_congr rfl
    intro A _
    simp only [e, Equiv.curry_apply, Function.curry, board_iff]
    rfl
  rw [hc]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Row)).sum_comp
    (fun f => if f 0 0 = true ∧ Safe f then (1 : ℤ) else 0), Fintype.sum_prod_type]
  change (∑ r : Row, ∑ f : Fin k → Row,
    if r 0 = true ∧ Safe (Fin.cons r f) then (1 : ℤ) else 0) = _
  unfold total
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r 0 = true
  · simp only [hr, true_and, ite_true]
    exact congrFun (count_eq_v k) r
  · simp [hr]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction enumerates the sixteen rows and their four-step continuations.
/-- A finite identity on all sixteen binary rows. -/
theorem finite_certificate : ∀ r : Row,
    v 4 r = 2 * v 3 r + 7 * v 2 r - 2 * v 1 r - 3 * v 0 r := by
  decide +kernel

private theorem vector_recurrence (k : ℕ) : ∀ r : Row,
    v (k + 4) r = 2 * v (k + 3) r + 7 * v (k + 2) r -
      2 * v (k + 1) r - 3 * v k r := by
  induction k with
  | zero => exact finite_certificate
  | succ k ih =>
    intro r
    change step (v (k + 4)) r = 2 * step (v (k + 3)) r +
      7 * step (v (k + 2)) r - 2 * step (v (k + 1)) r - 3 * step (v k) r
    unfold step
    by_cases hr : ValidRow r
    · simp only [hr, ite_true, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hc : Compatible r s
      · simpa only [ite_eq_left hc] using ih s
      · simp only [ite_eq_right hc, mul_zero, add_zero, sub_zero]
    · simp [hr]

private theorem total_recurrence (k : ℕ) :
    total (v (k + 4)) = 2 * total (v (k + 3)) + 7 * total (v (k + 2)) -
      2 * total (v (k + 1)) - 3 * total (v k) := by
  unfold total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r 0 = true
  · simpa only [ite_eq_left hr] using vector_recurrence k r
  · simp only [ite_eq_right hr, mul_zero, add_zero, sub_zero]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The small counts reduce through the continuation sum rather than all boards.
private theorem initial : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 3 ∧
    (a 2 : ℤ) = 5 ∧ (a 3 : ℤ) = 29 ∧ (a 4 : ℤ) = 87 := by
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩
  · rw [show 1 = 0 + 1 by omega, counting_bridge]; decide +kernel
  · rw [show 2 = 1 + 1 by omega, counting_bridge]; decide +kernel
  · rw [show 3 = 2 + 1 by omega, counting_bridge]; decide +kernel
  · rw [show 4 = 3 + 1 by omega, counting_bridge]; decide +kernel

private theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) + 7 * (a (n - 2) : ℤ) -
      2 * (a (n - 3) : ℤ) - 3 * (a (n - 4) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simpa only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    ← counting_bridge, Nat.add_assoc, Nat.reduceAdd] using total_recurrence k

open PowerSeries

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Coefficient comparison includes the literal counts at the four small heights.
private theorem generating_function :
    (1 - 2 * X - 7 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) *
      (PowerSeries.mk fun n => (a n : ℤ)) = X * (1 - X) * (3 + 2 * X) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - 2 * X - 7 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) * F = _
  have he : (1 - 2 * X - 7 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) * F =
      F - 2 * (F * X ^ 1) - 7 * (F * X ^ 2) +
        2 * (F * X ^ 3) + 3 * (F * X ^ 4) := by ring
  have hr : (X * (1 - X) * (3 + 2 * X) : PowerSeries ℤ) =
      3 * X - X ^ 2 - 2 * X ^ 3 := by ring
  rw [he, hr]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  by_cases hn : 5 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence n hn
    linarith
  · rcases initial with ⟨h0, h1, h2, h3, h4⟩
    interval_cases n <;> norm_num only [h0, h1, h2, h3, h4, ite_true, ite_false]

/-- The Hardin-Barker recurrence and generating series. -/
theorem result :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) =
      2 * (a (n - 1) : ℤ) + 7 * (a (n - 2) : ℤ) -
        2 * (a (n - 3) : ℤ) - 3 * (a (n - 4) : ℤ)) ∧
    (1 - 2 * X - 7 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) *
      (PowerSeries.mk fun n => (a n : ℤ)) = X * (1 - X) * (3 + 2 * X) := by
  exact ⟨recurrence, generating_function⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
