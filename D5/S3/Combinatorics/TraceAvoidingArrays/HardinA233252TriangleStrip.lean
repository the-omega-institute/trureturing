/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.finite_certificate
   digest: Barker identities for the literal four-column strip. -/

/-
admission_basis: open-problem-resolution (#27709; Proved)
escape_witness: none (open-problem-resolution; all declarations instantiate frozen owners and finite kernel decisions)
Valid, instDecidableValid and boundaryClass are reused directly from HardinA233124SquareStrip.
The four-label sum reindexing in row_counts uses HardinA233125SquareStrip.label_sum.
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233124SquareStrip (Valid boundaryClass)
open HardinA233125SquareStrip (Row rowLegal)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableNormal
attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableLegal
attribute [local instance 2000] HardinA233125SquareStrip.decidableRowLegal
attribute [local instance 2000] HardinA233124SquareStrip.instDecidableValid
attribute [local instance 2000] Pi.instFintype

abbrev Boundary := Fin 3 → Fin 3

private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3, c j.succ ≠ d j.castSucc ∧
    (c j.succ).val + (d j.castSucc).val ≠ 5

private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 4 → Fin 6 =>
    widthLegal rowLegal bonds A)).card

def pairs (c : Row) : Boundary := fun j => beta (c j.succ)

def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 3, p j ≠ beta (c j.castSucc)

private instance instDecidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) :=
  inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) :
    bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private abbrev v := widthV rowLegal pairs compatible
private abbrev total := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) :
    (a (n + 1) : ℤ) = total (v n) := by
  simpa [a, widthLegal] using
    (width_counting_bridge rowLegal pairs compatible bonds bonds_iff n)

def transfer (i k : Fin 3) : ℤ :=
  ![![16, 32, 40], ![0, 80, 80], ![0, 64, 64]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c →
      Valid (finish s c) (pairs c) := by
  decide +kernel

def classCount (s : Seen) (p : Boundary) (k : Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (pairs c) = k then 1 else 0

def firstCount (k : Fin 3) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
      boundaryClass (finish (false, false) c) (pairs c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Boundary) (k : Fin 3) :
    classCount s p k = ∑ q : Fin 4 → Fin 3,
      rowWeight s q * if (∀ j : Fin 3, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j.castSucc) ∧
          boundaryClass (rowFinish s q) (Fin.tail q) = k then 1 else 0 := by
  let H : Seen → (Fin 4 → Fin 3) → ℤ := fun t q =>
    if (∀ j : Fin 3, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j.castSucc) ∧
          boundaryClass t (Fin.tail q) = k then 1 else 0
  change classCount s p k = ∑ q : Fin 4 → Fin 3,
    rowWeight s q * H (rowFinish s q) q
  rw [← scanner_fibres 4 s]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  have hp : pairs c = Fin.tail (fun j => beta (c j)) := by
    rfl
  rw [hp]
  by_cases hg : good s c <;>
    simp [H, hg, rowLegal, compatible, pairs, ← colour_bond_iff,
      and_comm, and_left_comm]

private theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [class_fibres, HardinA233125SquareStrip.label_sum]
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

private theorem initial_counts : ∀ k, firstCount k = ![4, 2, 4] k := by
  decide +kernel

theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k,
      classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![4, 2, 4] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 3 → ℤ
  | 0, _ => 1
  | n + 1, k =>
      if k = 0 then 16 * w n 0 + 32 * w n 1 + 40 * w n 2
      else if k = 1 then 80 * w n 1 + 80 * w n 2
      else 64 * w n 1 + 64 * w n 2

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        ∑ k : Fin 3, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = k then (1 : ℤ) else 0) * w n k := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k : Fin 3, classCount s p k * w n k) = _
    simp_rw [finite_certificate.1 s p h]
    generalize boundaryClass s p = k
    fin_cases k <;> simp [transfer, w, Fin.sum_univ_succ] <;> ring

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = 4 * w n 0 + 2 * w n 1 + 4 * w n 2 := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      ∑ k : Fin 3, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = k then (1 : ℤ) else 0) * w n k := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ k : Fin 3, firstCount k * w n k) = _
  simp_rw [finite_certificate.2]
  simp [Fin.sum_univ_succ]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 3) : ℤ) = 160 * a (n + 2) - 2304 * a (n + 1) := by
  rw [show n + 3 = (n + 1) + 1 + 1 by omega,
    show n + 2 = (n + 1) + 1 by omega, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  norm_num
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, widthLegal]

private theorem one_count : (a 1 : ℤ) = 10 := by
  have h := a_eq_w 0
  change (a 1 : ℤ) = 4 * 1 + 2 * 1 + 4 * 1 at h
  calc
    (a 1 : ℤ) = 4 * 1 + 2 * 1 + 4 * 1 := h
    _ = 10 := by norm_num

private theorem two_count : (a 2 : ℤ) = 1184 := by
  have h := a_eq_w 1
  change (a 2 : ℤ) = 4 * 88 + 2 * 160 + 4 * 128 at h
  calc
    (a 2 : ℤ) = 4 * 88 + 2 * 160 + 4 * 128 := h
    _ = 1184 := by norm_num

private theorem closed_step (n : ℕ) :
    (2 : ℤ) ^ (4 * (n + 2) + 1) * (4 * (9 : ℤ) ^ (n + 3) + 9) =
      160 * ((2 : ℤ) ^ (4 * (n + 1) + 1) * (4 * (9 : ℤ) ^ (n + 2) + 9)) -
        2304 * ((2 : ℤ) ^ (4 * n + 1) * (4 * (9 : ℤ) ^ (n + 1) + 9)) := by
  have e2 : 4 * (n + 2) + 1 = (4 * n + 1) + 8 := by omega
  have e1 : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by omega
  have q2 : n + 3 = (n + 1) + 2 := by omega
  have q1 : n + 2 = (n + 1) + 1 := by omega
  rw [e2, e1, q2, q1]
  simp only [pow_add]
  norm_num
  ring

private theorem closed_form : ∀ n : ℕ,
    9 * (a (n + 1) : ℤ) =
      2 ^ (4 * n + 1) * (4 * 9 ^ (n + 1) + 9) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        change 9 * (a 1 : ℤ) = _
        rw [one_count]
        norm_num
      by_cases hn1 : n = 1
      · subst n
        change 9 * (a 2 : ℤ) = _
        rw [two_count]
        norm_num
      have hn2 : 2 ≤ n := by omega
      have hrec := recurrence (n - 2)
      have hindex : n - 2 + 3 = n + 1 := by omega
      have hprev : n - 2 + 2 = n := by omega
      have hprev2 : n - 2 + 1 = n - 1 := by omega
      rw [hindex, hprev, hprev2] at hrec
      have hi1 := ih (n - 1) (by omega)
      have hi2 := ih (n - 2) (by omega)
      rw [show n - 1 + 1 = n by omega] at hi1
      rw [show n - 2 + 1 = n - 1 by omega] at hi2
      have hs := closed_step (n - 2)
      have hs' :
          (2 : ℤ) ^ (4 * n + 1) * (4 * (9 : ℤ) ^ (n + 1) + 9) =
            160 * ((2 : ℤ) ^ (4 * (n - 1) + 1) * (4 * (9 : ℤ) ^ n + 9)) -
              2304 * ((2 : ℤ) ^ (4 * (n - 2) + 1) * (4 * (9 : ℤ) ^ (n - 1) + 9)) := by
        rw [show 4 * (n - 2 + 2) + 1 = 4 * n + 1 by omega,
          show n - 2 + 3 = n + 1 by omega,
          show 4 * (n - 2 + 1) + 1 = 4 * (n - 1) + 1 by omega,
          show n - 2 + 2 = n by omega,
          show n - 2 + 1 = n - 1 by omega] at hs
        exact hs
      linarith [hrec, hi1, hi2, hs']

attribute [local irreducible] a
open PowerSeries in
theorem result :
    (∀ n : ℕ, 1 ≤ n →
      (a (n + 2) : ℤ) = 160 * a (n + 1) - 2304 * a n) ∧
    ((1 - 16 * X) * (1 - 144 * X) *
      (PowerSeries.mk fun n => (a n : ℤ)) = 2 * X * (5 - 208 * X)) ∧
    (∀ n : ℕ, 9 * (a (n + 1) : ℤ) =
      2 ^ (4 * n + 1) * (4 * 9 ^ (n + 1) + 9)) := by
  have hrec : ∀ n : ℕ, 1 ≤ n →
      (a (n + 2) : ℤ) = 160 * a (n + 1) - 2304 * a n := by
    intro n hn
    have h := recurrence (n - 1)
    rw [show n - 1 + 3 = n + 2 by omega,
      show n - 1 + 2 = n + 1 by omega,
      show n - 1 + 1 = n by omega] at h
    exact h
  have hgf :
      (1 - 16 * X) * (1 - 144 * X) *
          (PowerSeries.mk fun n => (a n : ℤ)) = 2 * X * (5 - 208 * X) := by
    let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
    have hp : (1 - 16 * X) * (1 - 144 * X) * F =
        F - 160 * (F * X ^ 1) + 2304 * (F * X ^ 2) := by ring
    have hr : (2 * X * (5 - 208 * X) : PowerSeries ℤ) =
        10 * X - 416 * X ^ 2 := by ring
    change (1 - 16 * X) * (1 - 144 * X) * F = _
    rw [hp, hr]
    ext n
    simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
      coeff_X, coeff_X_pow, F, coeff_mk]
    by_cases hn : 3 ≤ n
    · simp only [ite_eq_left (show 1 ≤ n by omega),
        ite_eq_left (show 2 ≤ n by omega),
        ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega)]
      have hh := recurrence (n - 3)
      have h3 : n - 3 + 3 = n := by omega
      have h2 : n - 3 + 2 = n - 1 := by omega
      have h1 : n - 3 + 1 = n - 2 := by omega
      rw [h3, h2, h1] at hh
      linarith
    · have h1 := one_count
      have h2 := two_count
      interval_cases n <;> norm_num only [zero_count, h1, h2,
        Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, if_true,
        if_false, Nat.cast_zero, mul_zero, sub_self, add_zero, zero_add]
  exact ⟨hrec, hgf, closed_form⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
