/- GID: D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact five-column array counts, parity, recurrence and formal generating series. -/
/-
result: proof_shape: content; escape_witness: walks_parity.
admission_basis: open-problem-resolution (#24091; Proved).
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24684
The public statement uses signed integer differences and the literal labelled-array count.
The source domain starts at one; the recurrence is indexed from four.
The all-length induction walks_parity supplies the counting invariant.
square_iff: proof_shape: bind-only; consumer(s): compatible_neighbors;
  Direct frozen dependencies: none; escape_witness: none.
compatible_neighbors: proof_shape: bind-only; consumer(s): walks_step;
  Direct frozen dependencies: none; escape_witness: none.
walks_zero: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
walks_step: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
source_chain: proof_shape: bind-only; consumer(s): sourceWalkEquiv;
  Direct frozen dependencies: none; escape_witness: none.
source_card: proof_shape: bind-only; consumer(s): raw_odd, raw_even;
  Direct frozen dependencies: none; escape_witness: none.
step_basis: proof_shape: bind-only; consumer(s): step_branch, step_degree, step_deterministic, step_one;
  Direct frozen dependencies: none; escape_witness: none.
step_branch: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
step_degree: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
step_deterministic: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
step_one: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
step_linear: proof_shape: bind-only; consumer(s): walks_parity;
  Direct frozen dependencies: none; escape_witness: none.
walks_parity: proof_shape: content; consumer(s): raw_odd, raw_even;
  Direct frozen dependencies: none; escape_witness: walks_parity.
sum_branch: proof_shape: bind-only; consumer(s): sum_degreeBranch, raw_even;
  Direct frozen dependencies: none; escape_witness: none.
sum_center: proof_shape: bind-only; consumer(s): sum_degreeBranch;
  Direct frozen dependencies: none; escape_witness: none.
sum_deterministic: proof_shape: bind-only; consumer(s): raw_odd, raw_even;
  Direct frozen dependencies: none; escape_witness: none.
sum_degreeBranch: proof_shape: bind-only; consumer(s): raw_odd;
  Direct frozen dependencies: none; escape_witness: none.
raw_odd: proof_shape: content; consumer(s): a_odd;
  Direct frozen dependencies: none; escape_witness: walks_parity.
raw_even: proof_shape: content; consumer(s): a_even;
  Direct frozen dependencies: none; escape_witness: walks_parity.
a_odd: proof_shape: content; consumer(s): lag_two, series_identity, result;
  Direct frozen dependencies: none; escape_witness: walks_parity.
a_even: proof_shape: content; consumer(s): lag_two, series_identity, result;
  Direct frozen dependencies: none; escape_witness: walks_parity.
lag_two: proof_shape: content; consumer(s): recurrence;
  Direct frozen dependencies: none; escape_witness: walks_parity.
recurrence: proof_shape: content; consumer(s): series_identity, result;
  Direct frozen dependencies: none; escape_witness: walks_parity.
series_exists: proof_shape: bind-only; consumer(s): result;
  Direct frozen dependencies: none; escape_witness: none.
series_identity: proof_shape: content; consumer(s): result;
  Direct frozen dependencies: none; escape_witness: walks_parity.
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.ChainOfFn

namespace D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open scoped BigOperators

/-- The clockwise signed integer differences of the square [a b; c d]
are pairwise distinct. Entries are coerced to integers before subtraction. -/
def DistinctClockwise (a b c d : Fin 3) : Prop :=
  [((b.val : ℤ) - (a.val : ℤ)),
   ((d.val : ℤ) - (b.val : ℤ)),
   ((c.val : ℤ) - (d.val : ℤ)),
   ((a.val : ℤ) - (c.val : ℤ))].Pairwise (· ≠ ·)

/-- Every consecutive 2 by 2 subblock satisfies the source condition. -/
def IsSourceArray {n : ℕ} (X : (Matrix (Fin (n + 1)) (Fin 5) (Fin 3))) : Prop :=
  ∀ (i : Fin n) (j : Fin 4),
    DistinctClockwise (X i.castSucc j.castSucc) (X i.castSucc j.succ)
      (X i.succ j.castSucc) (X i.succ j.succ)

/-- One quarter of the raw array count in ℚ; the source domain is n ≥ 1. -/
noncomputable def a (n : ℕ) : ℚ :=
  (Nat.card {X : (Matrix (Fin (n + 1)) (Fin 5) (Fin 3)) // IsSourceArray X} : ℚ) / 4

/-- The ordinary generating series starts at index 1 with zero constant term. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
    ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A = a n

/-- The parity formulas, empirical recurrence, and formal generating function
in OEIS A209723 FORMULA. Even indices are 2(m+1), odd indices are 2m+1,
and recurrence indices are m+4. The formal denominator has constant term 1.
Existence of the source series is asserted rather than assumed. -/
def claim : Prop :=
  (∀ m : ℕ, a (2 * (m + 1)) = 3 * (2 : ℚ) ^ m + 4) ∧
  (∀ m : ℕ, a (2 * m + 1) = (2 : ℚ) ^ (m + 1) + 4) ∧
  (∀ m : ℕ, a (m + 4) = a (m + 3) + 2 * a (m + 2) - 2 * a (m + 1)) ∧
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
  (∀ A : PowerSeries ℚ, IsSourceSeries A →
    A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (6 + PowerSeries.X - 11 * PowerSeries.X ^ 2))

private def Compatible (s t : (Fin 5 → Fin 3)) : Prop :=
  ∀ j : Fin 4, DistinctClockwise (s j.castSucc) (s j.succ) (t j.castSucc) (t j.succ)

private theorem square_iff (a b c d : Fin 3) : DistinctClockwise a b c d ↔
    (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 0) ∨
    (a = 0 ∧ b = 2 ∧ c = 1 ∧ d = 0) ∨
    (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 1) ∨
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∨
    (a = 1 ∧ b = 2 ∧ c = 2 ∧ d = 0) ∨
    (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨
    (a = 2 ∧ b = 0 ∧ c = 1 ∧ d = 2) ∨
    (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 2) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num [DistinctClockwise]

private def r0 : (Fin 5 → Fin 3) := ![2, 0, 2, 0, 2]
private def r1 : (Fin 5 → Fin 3) := ![0, 1, 0, 1, 0]
private def r2 : (Fin 5 → Fin 3) := ![1, 2, 1, 2, 1]
private def r3 : (Fin 5 → Fin 3) := ![0, 2, 0, 2, 0]
private def r4 : (Fin 5 → Fin 3) := ![1, 0, 1, 0, 1]
private def r5 : (Fin 5 → Fin 3) := ![2, 1, 2, 1, 2]
private def r6 : (Fin 5 → Fin 3) := ![0, 1, 0, 2, 0]
private def r7 : (Fin 5 → Fin 3) := ![2, 0, 2, 1, 2]
private def r8 : (Fin 5 → Fin 3) := ![0, 2, 0, 1, 0]
private def r9 : (Fin 5 → Fin 3) := ![2, 1, 2, 0, 2]
private def r10 : (Fin 5 → Fin 3) := ![0, 2, 0, 2, 1]
private def r11 : (Fin 5 → Fin 3) := ![1, 0, 1, 0, 2]
private def r12 : (Fin 5 → Fin 3) := ![0, 2, 1, 2, 0]
private def r13 : (Fin 5 → Fin 3) := ![1, 0, 2, 0, 1]
private def r14 : (Fin 5 → Fin 3) := ![0, 2, 1, 2, 1]
private def r15 : (Fin 5 → Fin 3) := ![1, 0, 2, 0, 2]
private def r16 : (Fin 5 → Fin 3) := ![1, 2, 0, 2, 0]
private def r17 : (Fin 5 → Fin 3) := ![2, 0, 1, 0, 1]
private def r18 : (Fin 5 → Fin 3) := ![1, 2, 0, 2, 1]
private def r19 : (Fin 5 → Fin 3) := ![2, 0, 1, 0, 2]
private def r20 : (Fin 5 → Fin 3) := ![1, 2, 1, 2, 0]
private def r21 : (Fin 5 → Fin 3) := ![2, 0, 2, 0, 1]

private def neighbors (s : (Fin 5 → Fin 3)) : Finset (Fin 5 → Fin 3) :=
  if s = r0 then {r1, r2} else
  if s = r1 then {r0} else
  if s = r2 then {r0} else
  if s = r3 then {r4, r5} else
  if s = r4 then {r3} else
  if s = r5 then {r3} else
  if s = r6 then {r7} else
  if s = r7 then {r6} else
  if s = r8 then {r9} else
  if s = r9 then {r8} else
  if s = r10 then {r11} else
  if s = r11 then {r10} else
  if s = r12 then {r13} else
  if s = r13 then {r12} else
  if s = r14 then {r15} else
  if s = r15 then {r14} else
  if s = r16 then {r17} else
  if s = r17 then {r16} else
  if s = r18 then {r19} else
  if s = r19 then {r18} else
  if s = r20 then {r21} else
  if s = r21 then {r20} else
  ∅

private theorem compatible_neighbors (s t : (Fin 5 → Fin 3)) : Compatible s t ↔ t ∈ neighbors s := by
  classical
  constructor
  · intro h
    obtain ⟨a0, a1, a2, a3, a4, hs⟩ : ∃ a0 a1 a2 a3 a4 : Fin 3,
        s = ![a0, a1, a2, a3, a4] := ⟨s 0, s 1, s 2, s 3, s 4, by ext i; fin_cases i <;> rfl⟩
    obtain ⟨b0, b1, b2, b3, b4, ht⟩ : ∃ b0 b1 b2 b3 b4 : Fin 3,
        t = ![b0, b1, b2, b3, b4] := ⟨t 0, t 1, t 2, t 3, t 4, by ext i; fin_cases i <;> rfl⟩
    subst s
    subst t
    have h0 : DistinctClockwise a0 a1 b0 b1 := h 0
    have h1 : DistinctClockwise a1 a2 b1 b2 := h 1
    have h2 : DistinctClockwise a2 a3 b2 b3 := h 2
    have h3 : DistinctClockwise a3 a4 b3 b4 := h 3
    fin_cases a0 <;> fin_cases a1 <;> fin_cases b0 <;> fin_cases b1 <;>
      norm_num [square_iff] at h0
    all_goals fin_cases a2 <;> fin_cases b2 <;> norm_num [square_iff] at h1
    all_goals fin_cases a3 <;> fin_cases b3 <;> norm_num [square_iff] at h2
    all_goals fin_cases a4 <;> fin_cases b4 <;> norm_num [square_iff] at h3
    all_goals simp [neighbors, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, funext_iff, Fin.forall_fin_succ]
  · intro h
    by_cases h0 : s = r0
    · subst s
      have hn : neighbors r0 = {r1, r2} := by exact Finset.val_inj.mp rfl
      rw [hn] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h1 : s = r1
    · subst s
      have hn : neighbors r1 = {r0} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h2 : s = r2
    · subst s
      have hn : neighbors r2 = {r0} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h3 : s = r3
    · subst s
      have hn : neighbors r3 = {r4, r5} := by exact Finset.val_inj.mp rfl
      rw [hn] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h4 : s = r4
    · subst s
      have hn : neighbors r4 = {r3} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h5 : s = r5
    · subst s
      have hn : neighbors r5 = {r3} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h6 : s = r6
    · subst s
      have hn : neighbors r6 = {r7} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h7 : s = r7
    · subst s
      have hn : neighbors r7 = {r6} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h8 : s = r8
    · subst s
      have hn : neighbors r8 = {r9} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h9 : s = r9
    · subst s
      have hn : neighbors r9 = {r8} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h10 : s = r10
    · subst s
      have hn : neighbors r10 = {r11} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h11 : s = r11
    · subst s
      have hn : neighbors r11 = {r10} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h12 : s = r12
    · subst s
      have hn : neighbors r12 = {r13} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h13 : s = r13
    · subst s
      have hn : neighbors r13 = {r12} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h14 : s = r14
    · subst s
      have hn : neighbors r14 = {r15} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h15 : s = r15
    · subst s
      have hn : neighbors r15 = {r14} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h16 : s = r16
    · subst s
      have hn : neighbors r16 = {r17} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h17 : s = r17
    · subst s
      have hn : neighbors r17 = {r16} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h18 : s = r18
    · subst s
      have hn : neighbors r18 = {r19} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h19 : s = r19
    · subst s
      have hn : neighbors r19 = {r18} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h20 : s = r20
    · subst s
      have hn : neighbors r20 = {r21} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    by_cases h21 : s = r21
    · subst s
      have hn : neighbors r21 = {r20} := by exact Finset.val_eq_singleton_iff.mp rfl
      rw [hn] at h
      simp only [Finset.mem_singleton] at h
      subst t
      all_goals norm_num [Compatible, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, Fin.forall_fin_succ, DistinctClockwise]
    have hn : neighbors s = ∅ := by
      simp only [neighbors, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10, ite_eq_right h11, ite_eq_right h12, ite_eq_right h13, ite_eq_right h14, ite_eq_right h15, ite_eq_right h16, ite_eq_right h17, ite_eq_right h18, ite_eq_right h19, ite_eq_right h20, ite_eq_right h21]
    have hf : False := by simp [hn] at h
    exact hf.elim

private noncomputable def tailStep (n : ℕ) (s : Fin 5 → Fin 3) :
    {x : Fin (n + 1) → (Fin 5 → Fin 3) // List.IsChain Compatible (s :: List.ofFn x)} ≃ Σ t : {t : (Fin 5 → Fin 3) // Compatible s t}, {x : Fin n → (Fin 5 → Fin 3) // List.IsChain Compatible (t.val :: List.ofFn x)} := by
  let e := (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 5 → Fin 3)).symm.trans
    (Equiv.sigmaEquivProd (Fin 5 → Fin 3) (Fin n → (Fin 5 → Fin 3))).symm
  refine (e.subtypeEquiv (q := fun c => Compatible s c.1 ∧
    List.IsChain Compatible (c.1 :: List.ofFn c.2)) ?_).trans (Equiv.subtypeSigmaEquivSigma (p := Compatible s)
      (q := fun t x => List.IsChain Compatible (t :: List.ofFn x)))
  intro x
  change List.IsChain Compatible (s :: List.ofFn x) ↔
    Compatible s (x 0) ∧ List.IsChain Compatible (x 0 :: List.ofFn (Fin.tail x))
  rw [List.ofFn_succ, List.isChain_cons_cons]
  rfl

private noncomputable def walks (n : ℕ) (s : (Fin 5 → Fin 3)) : ℕ := Nat.card ({x : Fin n → (Fin 5 → Fin 3) // List.IsChain Compatible (s :: List.ofFn x)})

private noncomputable def step (f : (Fin 5 → Fin 3) → ℕ) (s : (Fin 5 → Fin 3)) : ℕ := ∑ t ∈ neighbors s, f t

private theorem walks_zero (s : (Fin 5 → Fin 3)) : walks 0 s = 1 := by
  let : Unique ({x : Fin 0 → (Fin 5 → Fin 3) // List.IsChain Compatible (s :: List.ofFn x)}) :=
    uniqueOfSubsingleton ⟨Fin.elim0, by simp⟩
  exact Nat.card_unique

private theorem walks_step (n : ℕ) (s : (Fin 5 → Fin 3)) : walks (n + 1) s = step (walks n) s := by
  classical
  rw [walks, Nat.card_congr (tailStep n s), Nat.card_sigma]
  exact (Finset.sum_subtype (neighbors s) (fun t => (compatible_neighbors s t).symm)
    (walks n)).symm

private theorem source_chain {n : ℕ} (x : (Matrix (Fin (n + 1)) (Fin 5) (Fin 3))) :
    IsSourceArray x ↔ List.IsChain Compatible (List.ofFn (fun i : Fin (n + 1) => (x i : (Fin 5 → Fin 3)))) := by
  rw [List.isChain_ofFn]
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩
  · intro h i
    exact h i.val (by omega)

private noncomputable def sourceWalkEquiv (n : ℕ) :
    {x : Matrix (Fin (n + 1)) (Fin 5) (Fin 3) // IsSourceArray x} ≃ Σ s : (Fin 5 → Fin 3), {x : Fin n → (Fin 5 → Fin 3) // List.IsChain Compatible (s :: List.ofFn x)} := by
  refine ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin 5 → Fin 3)).symm.subtypeEquiv
    (q := fun c => List.IsChain Compatible (c.1 :: List.ofFn c.2)) ?_).trans
    (Equiv.subtypeProdEquivSigmaSubtype (fun s x => List.IsChain Compatible (s :: List.ofFn x)))
  intro x
  change IsSourceArray x ↔ List.IsChain Compatible (x 0 :: List.ofFn (Fin.tail x))
  exact (source_chain (n := n) (show Matrix (Fin (n + 1)) (Fin 5) (Fin 3) from x)).trans (by
    rw [List.ofFn_succ]
    rfl)

private theorem source_card (n : ℕ) :
    Nat.card {x : (Matrix (Fin (n + 1)) (Fin 5) (Fin 3)) // IsSourceArray x} = ∑ s : (Fin 5 → Fin 3), walks n s := by
  exact (Nat.card_congr (sourceWalkEquiv n)).trans (Nat.card_sigma)

private def branch (s : (Fin 5 → Fin 3)) : ℕ := if s ∈ ({r0, r1, r2, r3, r4, r5} : Finset (Fin 5 → Fin 3)) then 1 else 0
private def center (s : (Fin 5 → Fin 3)) : ℕ := if s ∈ ({r0, r3} : Finset (Fin 5 → Fin 3)) then 1 else 0
private def deterministic (s : (Fin 5 → Fin 3)) : ℕ := if s ∈ ({r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21} : Finset (Fin 5 → Fin 3)) then 1 else 0

private def degreeBranch (s : (Fin 5 → Fin 3)) : ℕ := branch s + center s

private theorem step_basis (s : (Fin 5 → Fin 3)) :
    step branch s = degreeBranch s ∧
    step degreeBranch s = 2 * branch s ∧
    step deterministic s = deterministic s ∧
    step (fun _ => 1) s = degreeBranch s + deterministic s := by
  by_cases h0 : s = r0
  · subst s
    decide
  by_cases h1 : s = r1
  · subst s
    decide
  by_cases h2 : s = r2
  · subst s
    decide
  by_cases h3 : s = r3
  · subst s
    decide
  by_cases h4 : s = r4
  · subst s
    decide
  by_cases h5 : s = r5
  · subst s
    decide
  by_cases h6 : s = r6
  · subst s
    decide
  by_cases h7 : s = r7
  · subst s
    decide
  by_cases h8 : s = r8
  · subst s
    decide
  by_cases h9 : s = r9
  · subst s
    decide
  by_cases h10 : s = r10
  · subst s
    decide
  by_cases h11 : s = r11
  · subst s
    decide
  by_cases h12 : s = r12
  · subst s
    decide
  by_cases h13 : s = r13
  · subst s
    decide
  by_cases h14 : s = r14
  · subst s
    decide
  by_cases h15 : s = r15
  · subst s
    decide
  by_cases h16 : s = r16
  · subst s
    decide
  by_cases h17 : s = r17
  · subst s
    decide
  by_cases h18 : s = r18
  · subst s
    decide
  by_cases h19 : s = r19
  · subst s
    decide
  by_cases h20 : s = r20
  · subst s
    decide
  by_cases h21 : s = r21
  · subst s
    decide
  have hn : neighbors s = ∅ := by
    simp only [neighbors, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10, ite_eq_right h11, ite_eq_right h12, ite_eq_right h13, ite_eq_right h14, ite_eq_right h15, ite_eq_right h16, ite_eq_right h17, ite_eq_right h18, ite_eq_right h19, ite_eq_right h20, ite_eq_right h21]
  simp [step, hn, degreeBranch, branch, center, deterministic, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

private theorem step_branch (s : (Fin 5 → Fin 3)) : step branch s = degreeBranch s := (step_basis s).1

private theorem step_degree (s : (Fin 5 → Fin 3)) : step degreeBranch s = 2 * branch s := (step_basis s).2.1

private theorem step_deterministic (s : (Fin 5 → Fin 3)) : step deterministic s = deterministic s := (step_basis s).2.2.1

private theorem step_one (s : (Fin 5 → Fin 3)) : step (fun _ => 1) s = degreeBranch s + deterministic s :=
  (step_basis s).2.2.2

private theorem step_linear (f g : (Fin 5 → Fin 3) → ℕ) (a b : ℕ) (s : (Fin 5 → Fin 3)) :
    step (fun t => a * f t + b * g t) s = a * step f s + b * step g s := by
  classical
  simp only [step, Finset.sum_add_distrib, Finset.mul_sum]

private theorem walks_parity (m : ℕ) :
    (∀ s, walks (2 * m + 1) s = 2 ^ m * degreeBranch s + deterministic s) ∧
    (∀ s, walks (2 * m + 2) s = 2 ^ (m + 1) * branch s + deterministic s) := by
  induction m with
  | zero =>
    constructor
    · intro s
      simp only [Nat.mul_zero, Nat.zero_add, pow_zero, one_mul]
      rw [walks_step]
      rw [show walks 0 = (fun _ => 1) from funext walks_zero]
      exact step_one s
    · intro s
      rw [walks_step]
      have hh : walks 1 = fun s => degreeBranch s + deterministic s := by
        funext s
        rw [walks_step]
        rw [show walks 0 = (fun _ => 1) from funext walks_zero]
        exact step_one s
      rw [hh]
      simpa only [pow_one, one_mul] using (step_linear degreeBranch deterministic 1 1 s).trans
        (by rw [step_degree, step_deterministic]; simp)
  | succ m ih =>
    have hod (s : (Fin 5 → Fin 3)) : walks (2 * (m + 1) + 1) s =
        2 ^ (m + 1) * degreeBranch s + deterministic s := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, walks_step]
      have hh : walks (2 * m + 2) = fun s => 2 ^ (m + 1) * branch s + 1 * deterministic s := by
        funext s; simpa using ih.2 s
      rw [hh, step_linear, step_branch, step_deterministic, one_mul]
    refine ⟨hod, ?_⟩
    intro s
    rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega, walks_step]
    have hh : walks (2 * (m + 1) + 1) =
        fun s => 2 ^ (m + 1) * degreeBranch s + 1 * deterministic s := by
      funext s; simpa using hod s
    rw [hh, step_linear, step_degree, step_deterministic, one_mul, pow_succ]
    ring

private theorem sum_branch : ∑ s : (Fin 5 → Fin 3), branch s = 6 := by
  classical
  unfold branch
  rw [← Finset.card_eq_sum_ite (s := ({r0, r1, r2, r3, r4, r5} : Finset (Fin 5 → Fin 3))) (Finset.subset_univ _)]
  decide

private theorem sum_center : ∑ s : (Fin 5 → Fin 3), center s = 2 := by
  classical
  unfold center
  rw [← Finset.card_eq_sum_ite (s := ({r0, r3} : Finset (Fin 5 → Fin 3))) (Finset.subset_univ _)]
  decide

private theorem sum_deterministic : ∑ s : (Fin 5 → Fin 3), deterministic s = 16 := by
  classical
  unfold deterministic
  rw [← Finset.card_eq_sum_ite (s := ({r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21} : Finset (Fin 5 → Fin 3))) (Finset.subset_univ _)]
  decide

private theorem sum_degreeBranch : ∑ s : (Fin 5 → Fin 3), degreeBranch s = 8 := by
  simp only [degreeBranch, Finset.sum_add_distrib, sum_branch, sum_center]

private theorem raw_odd (m : ℕ) :
    Nat.card {x : (Matrix (Fin ((2 * m + 1) + 1)) (Fin 5) (Fin 3)) // IsSourceArray x} = 2 ^ m * 8 + 16 := by
  rw [source_card]
  simp_rw [(walks_parity m).1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_degreeBranch, sum_deterministic]

private theorem raw_even (m : ℕ) :
    Nat.card {x : (Matrix (Fin ((2 * m + 2) + 1)) (Fin 5) (Fin 3)) // IsSourceArray x} = 2 ^ (m + 1) * 6 + 16 := by
  rw [source_card]
  simp_rw [(walks_parity m).2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_branch, sum_deterministic]

private theorem a_odd (m : ℕ) : a (2 * m + 1) = (2 : ℚ) ^ (m + 1) + 4 := by
  rw [a, raw_odd]
  push_cast
  rw [pow_succ]
  ring

private theorem a_even (m : ℕ) : a (2 * (m + 1)) = 3 * (2 : ℚ) ^ m + 4 := by
  rw [show 2 * (m + 1) = 2 * m + 2 by omega, a, raw_even]
  push_cast
  rw [pow_succ]
  ring

private theorem lag_two (n : ℕ) : a (n + 3) = 2 * a (n + 1) - 4 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · rw [hm, show 2 * m + 3 = 2 * (m + 1) + 1 by omega, a_odd, a_odd, pow_succ]
    ring
  · rw [hm, show 2 * m + 1 + 3 = 2 * ((m + 1) + 1) by omega,
      show 2 * m + 1 + 1 = 2 * (m + 1) by omega, a_even, a_even, pow_succ]
    ring

private theorem recurrence (m : ℕ) :
    a (m + 4) = a (m + 3) + 2 * a (m + 2) - 2 * a (m + 1) := by
  have h0 := lag_two m
  have h1 := lag_two (m + 1)
  rw [show m + 1 + 3 = m + 4 by omega, show m + 1 + 1 = m + 2 by omega] at h1
  linarith

private theorem series_exists : ∃ A : PowerSeries ℚ, IsSourceSeries A := by
  refine ⟨PowerSeries.mk (fun n => if n = 0 then 0 else a n), ?_, ?_⟩
  · simp [PowerSeries.coeff_mk]
  · intro n hn
    simp only [PowerSeries.coeff_mk, ite_eq_right (by omega : n ≠ 0)]

private theorem series_identity (A : PowerSeries ℚ) (hA : IsSourceSeries A) :
    A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (6 + PowerSeries.X - 11 * PowerSeries.X ^ 2) := by
  have hL : A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      A - A * PowerSeries.X ^ 1 - 2 * (A * PowerSeries.X ^ 2) +
        2 * (A * PowerSeries.X ^ 3) := by ring
  have hR : (PowerSeries.X : PowerSeries ℚ) * (6 + PowerSeries.X - 11 * PowerSeries.X ^ 2) =
      6 * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 - 11 * PowerSeries.X ^ 3 := by ring
  rw [hL, hR]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow]
  have ha1 : a 1 = 6 := by
    have h := a_odd 0
    norm_num at h
    exact h
  have ha2 : a 2 = 7 := by
    have h := a_even 0
    norm_num at h
    exact h
  have ha3 : a 3 = 8 := by
    have h := a_odd 1
    norm_num at h
    exact h
  rcases n with _ | _ | _ | _ | n
  · simp [hA.1]
  · norm_num [hA.1, hA.2 1 (by omega), ha1]
  · norm_num [hA.1, hA.2 1 (by omega), hA.2 2 (by omega), ha1, ha2]
  · norm_num [hA.1, hA.2 1 (by omega), hA.2 2 (by omega), hA.2 3 (by omega), ha1, ha2, ha3]
  · have he := recurrence n
    have h1 : n + 1 + 1 + 1 + 1 - 1 = n + 3 := by omega
    have h2 : n + 1 + 1 + 1 + 1 - 2 = n + 2 := by omega
    have h3 : n + 1 + 1 + 1 + 1 - 3 = n + 1 := by omega
    simp only [show 1 ≤ n + 1 + 1 + 1 + 1 by omega,
      show 2 ≤ n + 1 + 1 + 1 + 1 by omega,
      show 3 ≤ n + 1 + 1 + 1 + 1 by omega, ite_true,
      h1, h2, h3, hA.2 (n + 4) (by omega), hA.2 (n + 3) (by omega),
      hA.2 (n + 2) (by omega), hA.2 (n + 1) (by omega),
      show ¬ n + 1 + 1 + 1 + 1 = 1 by omega,
      show ¬ n + 1 + 1 + 1 + 1 = 2 by omega,
      show ¬ n + 1 + 1 + 1 + 1 = 3 by omega, ite_false]
    convert (by linarith : a (n + 4) - a (n + 3) - 2 * a (n + 2) + 2 * a (n + 1) = (0 : ℚ)) using 1; ring

theorem result : claim := by
  exact ⟨a_even, a_odd, recurrence, series_exists, series_identity⟩

end D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209723EdgeDifferences
