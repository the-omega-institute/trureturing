/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.finite_certificate
   digest: Six-column binary arrays satisfy Hardin's trace-avoidance recurrence. -/

/-
admission_basis: open-problem-resolution (#22447; Proved)
escape_witness: none (settling result)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22760
Direct frozen dependencies: none; the mathematical imports are Mathlib or this delivery.
The row encoding uses finFunctionFinEquiv directly. The count is the literal Nat.card
of admissible matrices, and claim retains the source's integer recurrence.
The counting invariant identifies finite continuation counts with the recursively
extended row-pair vector; its induction supplies the counting-bridge content.
The certificate calculations and linear residual propagation are bind-only steps.
The following declarations give proof_shape and their mathematical consumers.
raw_step_5: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_5
fast_step_5: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_5
table_step_5: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_6
raw_step_6: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_6
fast_step_6: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_6
table_step_6: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_7
raw_step_7: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_7
fast_step_7: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_7
table_step_7: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_8
raw_step_8: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_8
fast_step_8: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_8
table_step_8: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_9
raw_step_9: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_9
fast_step_9: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_9
table_step_9: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_10
raw_step_10: proof_shape=bind-only; consumers=HardinA185765Recurrence.fast_step_10
fast_step_10: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_step_10
table_step_10: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_11
claim: proof_shape=bind-only; consumers=HardinA185765Recurrence.recurrence_from_certificate
lin: proof_shape=bind-only; consumers=HardinA185765Recurrence.residual_succ
residual: proof_shape=bind-only; consumers=HardinA185765Recurrence.Certificate
Certificate: proof_shape=bind-only; consumers=HardinA185765Recurrence.recurrence_from_certificate
residual_succ: proof_shape=bind-only; consumers=HardinA185765Recurrence.residual_vanish
residual_vanish: proof_shape=bind-only; consumers=HardinA185765Recurrence.recurrence_from_certificate
total_residual: proof_shape=bind-only; consumers=HardinA185765Recurrence.recurrence_from_certificate
recurrence_from_certificate: proof_shape=content; consumers=HardinA185765Recurrence.result
u_table_0: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_1
u_table_1: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_2
u_table_2: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_3
u_table_3: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_4
u_table_4: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_5
u_table_5: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_6
u_table_6: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_7
u_table_7: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_8
u_table_8: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_9
u_table_9: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_10
u_table_10: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_11
u_table_11: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_12
u_table_12: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_13
u_table_13: proof_shape=bind-only; consumers=HardinA185765Recurrence.u_table_14
u_table_14: proof_shape=bind-only; consumers=HardinA185765Recurrence.finite_certificate
raw_annihilator: proof_shape=bind-only; consumers=HardinA185765Recurrence.table_annihilator
table_annihilator: proof_shape=bind-only; consumers=HardinA185765Recurrence.finite_certificate
boundaryThreeRows: proof_shape=bind-only; consumers=HardinA185765Recurrence.raw_boundary_three_rows
raw_boundary_three_rows: proof_shape=bind-only; consumers=HardinA185765Recurrence.raw_boundary_three
raw_boundary_three: proof_shape=bind-only; consumers=HardinA185765Recurrence.boundary_three
boundary_three: proof_shape=bind-only; consumers=HardinA185765Recurrence.finite_certificate
raw_boundary_four: proof_shape=bind-only; consumers=HardinA185765Recurrence.boundary_four
boundary_four: proof_shape=bind-only; consumers=HardinA185765Recurrence.finite_certificate
finite_certificate: proof_shape=bind-only; consumers=HardinA185765Recurrence.result
result: proof_shape=content; consumers=terminal result
-/


import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185765Transfer
import Mathlib.Tactic.Linarith

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185765Recurrence
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185765Transfer
open scoped BigOperators

private theorem raw_step_5 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[5]!)[s.val]!)[t.val]!) = ((tables[6]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_5 : ∀ r s : (Fin 64), fastStep (table 5) r s = table 6 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_5 r s h
  · simp only [table, h, ite_false]

private theorem table_step_5 : ∀ r s : (Fin 64), step (table 5) r s = table 6 r s := by intro r s; rw [step_table_fast]; exact fast_step_5 r s

private theorem raw_step_6 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[6]!)[s.val]!)[t.val]!) = ((tables[7]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_6 : ∀ r s : (Fin 64), fastStep (table 6) r s = table 7 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_6 r s h
  · simp only [table, h, ite_false]

private theorem table_step_6 : ∀ r s : (Fin 64), step (table 6) r s = table 7 r s := by intro r s; rw [step_table_fast]; exact fast_step_6 r s

private theorem raw_step_7 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[7]!)[s.val]!)[t.val]!) = ((tables[8]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_7 : ∀ r s : (Fin 64), fastStep (table 7) r s = table 8 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_7 r s h
  · simp only [table, h, ite_false]

private theorem table_step_7 : ∀ r s : (Fin 64), step (table 7) r s = table 8 r s := by intro r s; rw [step_table_fast]; exact fast_step_7 r s

private theorem raw_step_8 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[8]!)[s.val]!)[t.val]!) = ((tables[9]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_8 : ∀ r s : (Fin 64), fastStep (table 8) r s = table 9 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_8 r s h
  · simp only [table, h, ite_false]

private theorem table_step_8 : ∀ r s : (Fin 64), step (table 8) r s = table 9 r s := by intro r s; rw [step_table_fast]; exact fast_step_8 r s

private theorem raw_step_9 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[9]!)[s.val]!)[t.val]!) = ((tables[10]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_9 : ∀ r s : (Fin 64), fastStep (table 9) r s = table 10 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_9 r s h
  · simp only [table, h, ite_false]

private theorem table_step_9 : ∀ r s : (Fin 64), step (table 9) r s = table 10 r s := by intro r s; rw [step_table_fast]; exact fast_step_9 r s

private theorem raw_step_10 : ∀ r s : Fin 64, H r s →
    (∑ t ∈ (((adjData[r.val]!)[s.val]!)).toFinset,
      ((tables[10]!)[s.val]!)[t.val]!) = ((tables[11]!)[r.val]!)[s.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem fast_step_10 : ∀ r s : (Fin 64), fastStep (table 10) r s = table 11 r s := by
  intro r s
  rw [fastStep_table_data]
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_step_10 r s h
  · simp only [table, h, ite_false]

private theorem table_step_10 : ∀ r s : (Fin 64), step (table 10) r s = table 11 r s := by intro r s; rw [step_table_fast]; exact fast_step_10 r s

/-- OEIS A185765, sole FORMULA assertion, including the printed n>12 threshold.
All signed operations are in the integers. -/
def claim : Prop :=
  ∀ n : ℕ, 13 ≤ n →
    (a n : ℤ) =
      (a (n - 1) : ℤ) + 30 * (a (n - 2) : ℤ) + 24 * (a (n - 3) : ℤ) -
      95 * (a (n - 4) : ℤ) - 15 * (a (n - 5) : ℤ) + 64 * (a (n - 6) : ℤ) -
      116 * (a (n - 7) : ℤ) + 16 * (a (n - 8) : ℤ) + 16 * (a (n - 9) : ℤ)


private def lin : ((Fin 64) → (Fin 64) → ℤ) →ₗ[ℤ] ((Fin 64) → (Fin 64) → ℤ) where
  toFun := step
  map_add' v w := by
    funext r s
    by_cases h : H r s
    · simp only [step, h, if_true, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hv : V r s t <;> simp [hv]
    · simp [step, h]
  map_smul' c v := by
    funext r s
    by_cases h : H r s
    · simp only [step, h, if_true, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hv : V r s t <;> simp [hv]
    · simp [step, h]

def residual (k : ℕ) : (Fin 64) → (Fin 64) → ℤ :=
  u (k + 9) - u (k + 8) - (30 : ℤ) • u (k + 7) - (24 : ℤ) • u (k + 6) +
    (95 : ℤ) • u (k + 5) + (15 : ℤ) • u (k + 4) - (64 : ℤ) • u (k + 3) +
    (116 : ℤ) • u (k + 2) - (16 : ℤ) • u (k + 1) - (16 : ℤ) • u k


def Certificate : Prop := residual 5 = 0 ∧ (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (residual 3) = 0 ∧ (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (residual 4) = 0

private theorem residual_succ (k : ℕ) : residual (k + 1) = lin (residual k) := by
  simp only [residual, map_sub, map_add, map_smul]
  rfl

private theorem residual_vanish (h : residual 5 = 0) (k : ℕ) : residual (k + 5) = 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [show k + 1 + 5 = (k + 5) + 1 by omega, residual_succ, ih, map_zero]

private theorem total_residual (k : ℕ) :
    (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (residual k) =
      (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 9)) - (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 8)) - 30 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 7)) -
      24 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 6)) + 95 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 5)) + 15 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 4)) -
      64 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 3)) + 116 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 2)) -
      16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + 1)) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u k) := by
  simp only [residual, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem recurrence_from_certificate (hc : Certificate) : claim := by
  intro n hn
  let k := n - 10
  have hk : 3 ≤ k := Nat.le_sub_of_add_le hn
  have hz : (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (residual k) = 0 := by
    rcases hc with ⟨h5, h3, h4⟩
    by_cases h : k = 3
    · simpa [h] using h3
    by_cases h' : k = 4
    · simpa [h'] using h4
    have hge : 5 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk (Ne.symm h))) (Ne.symm h'))
    have hv := residual_vanish h5 (k - 5)
    rw [Nat.sub_add_cancel hge] at hv
    rw [hv]
    simp
  have hcount (d : ℕ) (hd : d ≤ 9) :
      (a (n - d) : ℤ) = (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (u (k + (9 - d))) := by
    have hi : n - d = (k + (9 - d)) + 1 := by dsimp [k]; omega
    rw [hi]
    exact counting_bridge _
  have he := total_residual k
  have hcount0 := hcount 0 (by omega)
  simp only [Nat.sub_zero] at hcount0
  rw [hcount0, hcount 1 (by omega),
    hcount 2 (by omega), hcount 3 (by omega), hcount 4 (by omega),
    hcount 5 (by omega), hcount 6 (by omega), hcount 7 (by omega),
    hcount 8 (by omega), hcount 9 (by omega)]
  norm_num only [Nat.add_zero] at *
  linarith


private theorem u_table_0 : u 0 = table 0 := by
  funext r s
  exact table_base r s

private theorem u_table_1 : u 1 = table 1 := by
  change step (u 0) = table 1
  rw [u_table_0]
  funext r s
  exact table_step_0 r s

private theorem u_table_2 : u 2 = table 2 := by
  change step (u 1) = table 2
  rw [u_table_1]
  funext r s
  exact table_step_1 r s

private theorem u_table_3 : u 3 = table 3 := by
  change step (u 2) = table 3
  rw [u_table_2]
  funext r s
  exact table_step_2 r s

private theorem u_table_4 : u 4 = table 4 := by
  change step (u 3) = table 4
  rw [u_table_3]
  funext r s
  exact table_step_3 r s

private theorem u_table_5 : u 5 = table 5 := by
  change step (u 4) = table 5
  rw [u_table_4]
  funext r s
  exact table_step_4 r s

private theorem u_table_6 : u 6 = table 6 := by
  change step (u 5) = table 6
  rw [u_table_5]
  funext r s
  exact table_step_5 r s

private theorem u_table_7 : u 7 = table 7 := by
  change step (u 6) = table 7
  rw [u_table_6]
  funext r s
  exact table_step_6 r s

private theorem u_table_8 : u 8 = table 8 := by
  change step (u 7) = table 8
  rw [u_table_7]
  funext r s
  exact table_step_7 r s

private theorem u_table_9 : u 9 = table 9 := by
  change step (u 8) = table 9
  rw [u_table_8]
  funext r s
  exact table_step_8 r s

private theorem u_table_10 : u 10 = table 10 := by
  change step (u 9) = table 10
  rw [u_table_9]
  funext r s
  exact table_step_9 r s

private theorem u_table_11 : u 11 = table 11 := by
  change step (u 10) = table 11
  rw [u_table_10]
  funext r s
  exact table_step_10 r s

private theorem u_table_12 : u 12 = table 12 := by
  change step (u 11) = table 12
  rw [u_table_11]
  funext r s
  exact table_step_11 r s

private theorem u_table_13 : u 13 = table 13 := by
  change step (u 12) = table 13
  rw [u_table_12]
  funext r s
  exact table_step_12 r s

private theorem u_table_14 : u 14 = table 14 := by
  change step (u 13) = table 14
  rw [u_table_13]
  funext r s
  exact table_step_13 r s

private theorem raw_annihilator : ∀ r s : Fin 64, H r s →
    ((tables[14]!)[r.val]!)[s.val]! - ((tables[13]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[12]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[11]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! = 0 := by
  intro r
  fin_cases r <;> decide +kernel

private theorem table_annihilator : ∀ r s : (Fin 64),
    table 14 r s - table 13 r s - 30 * table 12 r s - 24 * table 11 r s +
    95 * table 10 r s + 15 * table 9 r s - 64 * table 8 r s +
    116 * table 7 r s - 16 * table 6 r s - 16 * table 5 r s = 0   := by
  intro r s
  by_cases h : H r s
  · simpa only [table, h, ite_true] using raw_annihilator r s h
  · simp [table, h]

private def boundaryThreeRows : Array ℤ := #[-104,104,64,-64,-152,152,72,-72,-144,144,304,-304,-104,104,168,-168,-168,168,104,-104,-304,304,144,-144,-72,72,152,-152,-64,64,104,-104,-104,104,64,-64,-152,152,72,-72,-144,144,304,-304,-104,104,168,-168,-168,168,104,-104,-304,304,144,-144,-72,72,152,-152,-64,64,104,-104]

private theorem raw_boundary_three_rows : ∀ r : Fin 64, (∑ s : Fin 64, if H r s then ((tables[12]!)[r.val]!)[s.val]! - ((tables[11]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[4]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[3]!)[r.val]!)[s.val]! else 0) = boundaryThreeRows[r.val]! := by
  intro r
  fin_cases r <;> decide +kernel

private theorem raw_boundary_three : (∑ r : Fin 64, ∑ s : Fin 64, if H r s then ((tables[12]!)[r.val]!)[s.val]! - ((tables[11]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[4]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[3]!)[r.val]!)[s.val]! else 0) = 0  := by
  calc
    _ = ∑ r : Fin 64, boundaryThreeRows[r.val]! := by
      apply Finset.sum_congr rfl
      intro r _
      exact raw_boundary_three_rows r
    _ = 0 := by decide +kernel

private theorem boundary_three :
    (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 12) - (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 11) - 30 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 10) - 24 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 9) +
    95 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 8) + 15 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 7) - 64 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 6) +
    116 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 5) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 4) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 3) = 0  := by
  calc
    (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 12) - (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 11) - 30 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 10) - 24 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 9) +
    95 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 8) + 15 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 7) - 64 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 6) +
    116 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 5) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 4) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 3) = (∑ r : Fin 64, ∑ s : Fin 64, (table 12 r s - table 11 r s - 30 * table 10 r s - 24 * table 9 r s + 95 * table 8 r s + 15 * table 7 r s - 64 * table 6 r s + 116 * table 5 r s - 16 * table 4 r s - 16 * table 3 r s)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (∑ r : Fin 64, ∑ s : Fin 64, if H r s then ((tables[12]!)[r.val]!)[s.val]! - ((tables[11]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[4]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[3]!)[r.val]!)[s.val]! else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : H r s
      · simp only [table, h, ite_true]
      · simp only [table, h, ite_false, mul_zero, sub_zero, add_zero]
    _ = 0 := raw_boundary_three

private theorem raw_boundary_four : (∑ r : Fin 64, ∑ s : Fin 64, if H r s then ((tables[13]!)[r.val]!)[s.val]! - ((tables[12]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[11]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[4]!)[r.val]!)[s.val]! else 0) = 0  := by
  apply Finset.sum_eq_zero
  intro r _
  fin_cases r <;> decide +kernel

private theorem boundary_four :
    (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 13) - (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 12) - 30 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 11) - 24 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 10) +
    95 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 9) + 15 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 8) - 64 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 7) +
    116 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 6) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 5) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 4) = 0  := by
  calc
    (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 13) - (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 12) - 30 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 11) - 24 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 10) +
    95 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 9) + 15 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 8) - 64 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 7) +
    116 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 6) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 5) - 16 * (fun v : Fin 64 → Fin 64 → ℤ => ∑ r : Fin 64, ∑ s : Fin 64, v r s) (table 4) = (∑ r : Fin 64, ∑ s : Fin 64, (table 13 r s - table 12 r s - 30 * table 11 r s - 24 * table 10 r s + 95 * table 9 r s + 15 * table 8 r s - 64 * table 7 r s + 116 * table 6 r s - 16 * table 5 r s - 16 * table 4 r s)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (∑ r : Fin 64, ∑ s : Fin 64, if H r s then ((tables[13]!)[r.val]!)[s.val]! - ((tables[12]!)[r.val]!)[s.val]! - (30 : ℤ) * ((tables[11]!)[r.val]!)[s.val]! - (24 : ℤ) * ((tables[10]!)[r.val]!)[s.val]! + (95 : ℤ) * ((tables[9]!)[r.val]!)[s.val]! + (15 : ℤ) * ((tables[8]!)[r.val]!)[s.val]! - (64 : ℤ) * ((tables[7]!)[r.val]!)[s.val]! + (116 : ℤ) * ((tables[6]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[5]!)[r.val]!)[s.val]! - (16 : ℤ) * ((tables[4]!)[r.val]!)[s.val]! else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : H r s
      · simp only [table, h, ite_true]
      · simp only [table, h, ite_false, mul_zero, sub_zero, add_zero]
    _ = 0 := raw_boundary_four

theorem finite_certificate : Certificate := by
  refine ⟨?_, ?_, ?_⟩
  · funext r s
    simp only [residual, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change u 14 r s - u 13 r s - 30 * u 12 r s - 24 * u 11 r s + 95 * u 10 r s + 15 * u 9 r s - 64 * u 8 r s + 116 * u 7 r s - 16 * u 6 r s - 16 * u 5 r s = 0
    rw [u_table_14, u_table_13, u_table_12, u_table_11, u_table_10,
      u_table_9, u_table_8, u_table_7, u_table_6, u_table_5]
    exact table_annihilator r s
  · rw [total_residual, u_table_12, u_table_11, u_table_10, u_table_9,
      u_table_8, u_table_7, u_table_6, u_table_5, u_table_4, u_table_3]
    exact boundary_three
  · rw [total_residual, u_table_13, u_table_12, u_table_11, u_table_10,
      u_table_9, u_table_8, u_table_7, u_table_6, u_table_5, u_table_4]
    exact boundary_four

theorem result : claim :=
  recurrence_from_certificate finite_certificate

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185765Recurrence
