/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.finite_certificate
   digest: Barker's generating function for the literal normalized six-colour five-column strip. -/

/-
admission_basis: open-problem-resolution (#28234; Proved)
escape_witness: none
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-! Literal five-column arrays and a three-dimensional symbolic continuation transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip

open HardinA233175PairStrip (Seen allowed advance good finish)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip

abbrev Row := Fin 5 → Fin 6
abbrev Boundary := Fin 4 → Fin 3

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 4, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 4, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5

private def Legal {n : ℕ} (A : Fin n × Fin 5 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), bonds (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    Transfer.normal (false, false) (fun i j => A (i, j))

private instance instDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → Row) :
    Decidable (Transfer.normal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))
private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 5 → Fin 6) :
    Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The literal filtered count. The first-cell existential sets `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 5 → Fin 6 => Legal A)).card

def pairs (c : Row) : Boundary := fun j => beta (c j.succ)

def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 4, p j ≠ beta (c j.castSucc)

private instance instDecidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))
private instance instDecidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, HardinA233251TriangleStrip.colour_bond_iff, compatible, pairs]

private abbrev v := Transfer.v rowLegal pairs compatible
private abbrev total := Transfer.total rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  exact Transfer.counting_bridge rowLegal pairs compatible bonds bonds_iff n

/-- The boundary labels alternate, and absent colour two excludes its whole pair. -/
def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 3, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)

private instance instDecidableValid (s : Seen) (p : Boundary) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))

/-- On the four boundary shapes ABAB, ABAC, ABCA, ABCB the ranks are 3,2,0,2. -/
def rank (p : Boundary) : ℤ :=
  if p 0 = p 2 then (if p 1 = p 3 then 3 else 2) else
    (if p 1 = p 3 then 2 else 0)

set_option maxRecDepth 100000 in
private theorem valid_next : ∀ s, s.1 = true → ∀ c : Row,
    rowLegal c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

/-- Count continuations by the second final flag. -/
def classCount (s : Seen) (p : Boundary) (b : Bool) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = b then 1 else 0

/-- Sum the boundary ranks of fully seen continuations. -/
def rankCount (s : Seen) (p : Boundary) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = true then rank (pairs c) else 0

/-- Count first rows by the second final flag. -/
def firstCount (b : Bool) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = b then 1 else 0

/-- Sum the ranks of fully seen first rows. -/
def firstRank : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = true then rank (pairs c) else 0

set_option maxRecDepth 100000 in
private theorem row_counts : ∀ s p, Valid s p →
    classCount s p true = (if s.2 then 320 + 64 * rank p else 240) ∧
    classCount s p false = (if s.2 then 0 else 32) ∧
    rankCount s p = (if s.2 then 512 + 160 * rank p else 448) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem initial_counts : firstCount true = 28 ∧ firstCount false = 8 ∧
    firstRank = 44 := by
  decide +kernel

/-- The weighted one-row transfer and initial-row counts. -/
theorem finite_certificate :
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 320 + 64 * rank p else 240) ∧
      classCount s p false = (if s.2 then 0 else 32) ∧
      rankCount s p = (if s.2 then 512 + 160 * rank p else 448)) ∧
    firstCount true = 28 ∧ firstCount false = 8 ∧ firstRank = 44 :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 3 → ℤ
  | 0, i => if i = 2 then 0 else 1
  | n + 1, i => if i = 0 then 32 * w n 0 + 240 * w n 1 + 448 * w n 2 else
      if i = 1 then 320 * w n 1 + 512 * w n 2 else 64 * w n 1 + 160 * w n 2

private def eval (n : ℕ) (s : Seen) (p : Boundary) : ℤ :=
  if s.2 then w n 1 + rank p * w n 2 else w n 0

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = eval n s p := by
  induction n generalizing s p with
  | zero => simp [Transfer.v, eval, w]
  | succ n ih =>
    rw [v, Transfer.v, Transfer.step]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      v n (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then (1 : ℤ) else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then rank (pairs c) else 0) * w n 2 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = false
          then (1 : ℤ) else 0) * w n 0 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s h.1 c ⟨hc.1, hc.2.2⟩)]
        cases hb : (finish s c).2 <;> simp [eval, hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    change classCount s p true * w n 1 + rankCount s p * w n 2 +
      classCount s p false * w n 0 = eval (n + 1) s p
    rw [(finite_certificate.1 s p h).1, (finite_certificate.1 s p h).2.1,
      (finite_certificate.1 s p h).2.2]
    cases hb : s.2 <;> simp [hb, eval, w] <;> ring

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = 8 * w n 0 + 28 * w n 1 + 44 * w n 2 := by
  rw [counting_bridge, total, Transfer.total]
  change (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
    v n (finish (false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) * w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then rank (pairs c) else 0) * w n 2 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) * w n 0 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w _ _ _ (initial_valid c hc)]
      cases hb : (finish (false, false) c).2 <;> simp [eval, hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change firstCount true * w n 1 + firstRank * w n 2 + firstCount false * w n 0 = _
  rw [finite_certificate.2.1, finite_certificate.2.2.1, finite_certificate.2.2.2]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 512 * a (n + 3) - 33792 * a (n + 2) +
      589824 * a (n + 1) := by
  rw [show n + 4 = ((n + 1) + 1) + 1 + 1 by omega,
    a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  norm_num
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, Legal]

open PowerSeries in
/-- Barker's identity for the literal count, with `a 0 = 0`. -/
theorem result :
    (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) = 4 * X * (9 - 1120 * X + 30720 * X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) * F =
      F - 512 * (F * X ^ 1) + 33792 * (F * X ^ 2) -
        589824 * (F * X ^ 3) := by ring
  have hr : (4 * X * (9 - 1120 * X + 30720 * X ^ 2) : PowerSeries ℤ) =
      36 * X - 4480 * X ^ 2 + 122880 * X ^ 3 := by ring
  change (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence (n - 4)
    have h4 : n - 4 + 4 = n := by omega
    have h3 : n - 4 + 3 = n - 1 := by omega
    have h2 : n - 4 + 2 = n - 2 := by omega
    have h1 : n - 4 + 1 = n - 3 := by omega
    rw [h4, h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    norm_num [w] at h1 h2 h3
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, if_true, if_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero, zero_add] <;> ring

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
