/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.finite_certificate
   digest: Barker's generating function for normalized six-colour square strips. -/

/-
admission_basis: open-problem-resolution (#28306; Proved)
escape_witness: none
Single-row numerical premises are consumed by the unbounded class induction.
bonds: proof_shape=bind-only; consumers=Legal, bonds_iff, counting_bridge
Legal: proof_shape=bind-only; consumers=a, counting_bridge, zero_count
instDecidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, a_eq_w, zero_count, result
pairs: proof_shape=bind-only; consumers=bonds_iff, v, total, classCount
compatible: proof_shape=bind-only; consumers=bonds_iff, v, classCount
instDecidableCompatible: proof_shape=bind-only; consumers=v, classCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge, v_eq_w
total: proof_shape=bind-only; consumers=counting_bridge, a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next, initial_valid, row_counts
instDecidableValid: proof_shape=bind-only; consumers=valid_next, initial_valid, row_counts
boundaryClass: proof_shape=bind-only; consumers=classCount, firstCount, v_eq_w
transfer: proof_shape=bind-only; consumers=row_counts, finite_certificate, v_eq_w
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=finite_certificate, v_eq_w
firstCount: proof_shape=bind-only; consumers=finite_certificate, a_eq_w
row_sum: proof_shape=bind-only; consumers=row_counts_zero, row_counts_one, row_counts_two
row_counts_zero: proof_shape=bind-only; consumers=row_counts
row_counts_one: proof_shape=bind-only; consumers=row_counts
row_counts_two: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, recurrence, result
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28306)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-! Literal square-strip counts and a three-class row transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip

open HardinA233175PairStrip
  (Seen good finish)
open HardinA233251TriangleStrip
  (Row rowLegal widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)

attribute [local reducible] rowLegal
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

def Legal {n : ℕ} (A : Fin n × Fin 3 → Fin 6) : Prop :=
  widthLegal rowLegal bonds A

private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
attribute [local reducible] Legal

/-- The literal filtered finite count; the first-cell condition gives the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Fin 6 => Legal A)).card

def pairs (c : Row) : Fin 3 → Fin 3 := fun j => beta (c j)

def compatible (p : Fin 3 → Fin 3) (c : Row) : Prop :=
  ∀ j, p j ≠ beta (c j)

private instance instDecidableCompatible (p : Fin 3 → Fin 3) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private abbrev v := widthV rowLegal pairs compatible

private abbrev total := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 3 → Fin 3) : Prop :=
  s.1 = true ∧ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧ (s.2 = false → ∀ j, p j ≠ 2)

private instance instDecidableValid (s : Seen) (p : Fin 3 → Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Fin 3 → Fin 3) : Fin 3 :=
  if s.2 then if p 0 = p 2 then 1 else 2 else 0

def transfer (i k : Fin 3) : ℤ :=
  ![![8, 8, 8], ![0, 24, 16], ![0, 16, 16]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  have hv : ∀ (s : Seen) (c : Row), s.1 = true → rowLegal c → good s c →
      Valid (finish s c) (pairs c) := by decide +kernel
  intro s p hp c hc
  exact hv s c hp.1 hc.1 hc.2.2

def classCount (s : Seen) (p : Fin 3 → Fin 3) (k : Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (pairs c) = k then 1 else 0

def firstCount (k : Fin 3) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (pairs c) = k then 1 else 0

private theorem row_sum (g : Row → ℤ) :
    (∑ c : Row, g c) =
      ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, g ![x, y, z] := by
  let e : Row ≃ Fin 6 × Fin 6 × Fin 6 :=
    { toFun := fun c => (c 0, c 1, c 2)
      invFun := fun t => ![t.1, t.2.1, t.2.2]
      left_inv := by intro c; ext j; fin_cases j <;> rfl
      right_inv := by rintro ⟨x, y, z⟩; rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem row_counts_zero : ∀ s p, Valid s p →
    classCount s p 0 = transfer (boundaryClass s p) 0 := by
  simp only [classCount, row_sum]
  decide +kernel

private theorem row_counts_one : ∀ s p, Valid s p →
    classCount s p 1 = transfer (boundaryClass s p) 1 := by
  simp only [classCount, row_sum]
  decide +kernel

private theorem row_counts_two : ∀ s p, Valid s p →
    classCount s p 2 = transfer (boundaryClass s p) 2 := by
  simp only [classCount, row_sum]
  decide +kernel

private theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  intro s p h k
  fin_cases k
  · exact row_counts_zero s p h
  · exact row_counts_one s p h
  · exact row_counts_two s p h

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

private theorem initial_counts : ∀ k, firstCount k = ![2, 0, 1] k := by
  decide +kernel

/-- The single-row transition matrix and the first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![2, 0, 1] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 3 → ℤ
  | 0, _ => 1
  | n + 1, k => if k = 0 then 8 * w n 0 + 8 * w n 1 + 8 * w n 2
      else if k = 1 then 24 * w n 1 + 16 * w n 2
      else 16 * w n 1 + 16 * w n 2

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 3 → Fin 3) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 0 then (1 : ℤ) else 0) * w n 0 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 1 then (1 : ℤ) else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 2 then (1 : ℤ) else 0) * w n 2 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        generalize boundaryClass (finish s c) (pairs c) = k
        fin_cases k <;> simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    change classCount s p 0 * w n 0 + classCount s p 1 * w n 1 +
      classCount s p 2 * w n 2 = _
    rw [finite_certificate.1 s p h 0, finite_certificate.1 s p h 1,
      finite_certificate.1 s p h 2]
    generalize boundaryClass s p = k
    fin_cases k <;> simp [transfer, w]

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 2 * w n 0 + w n 2 := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 0 then (1 : ℤ) else 0) *
          w n 0 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 1 then (1 : ℤ) else 0) *
          w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 2 then (1 : ℤ) else 0) *
          w n 2 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      generalize boundaryClass (finish (false, false) c) (pairs c) = k
      fin_cases k <;> simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change firstCount 0 * w n 0 + firstCount 1 * w n 1 + firstCount 2 * w n 2 = _
  rw [finite_certificate.2 0, finite_certificate.2 1, finite_certificate.2 2]
  simp

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 48 * a (n + 3) - 448 * a (n + 2) + 1024 * a (n + 1) := by
  rw [show n + 4 = (n + 1 + 1 + 1) + 1 by omega,
    show n + 3 = (n + 1 + 1) + 1 by omega, a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp [w]
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, Legal, widthLegal]

open PowerSeries in
/-- Barker's generating-function identity, with the empty coefficient set to zero. -/
theorem result :
    (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) = X * (3 - 64 * X + 192 * X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * F =
      F - 48 * (F * X ^ 1) + 448 * (F * X ^ 2) - 1024 * (F * X ^ 3) := by ring
  have hr : (X * (3 - 64 * X + 192 * X ^ 2) : PowerSeries ℤ) =
      3 * X - 64 * X ^ 2 + 192 * X ^ 3 := by ring
  change (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * F = _
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
    change (a 1 : ℤ) = 3 at h1
    change (a 2 : ℤ) = 80 at h2
    change (a 3 : ℤ) = 2688 at h3
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
