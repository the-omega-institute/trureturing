/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.finite_certificate
   digest: Barker's generating function for literal normalized two-column square strips. -/

/-
admission_basis: open-problem-resolution (#28348; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right at the boundary-class map after the
finite one-step premises are normalized.
Direct frozen dependencies (declaration statement_ids):
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Col
statement_id: sha256:b505330c2fba0907d9e841291266aa10f18f893fefa47fb6fc9ffa0aadb9d677
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.pairs
statement_id: sha256:fd8e139e79cc87792af23c7f3cc02fca4178e9d6a1835610fc0d3741c72c1530
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthNormal
statement_id: sha256:544f7677e789967b28078e2cb7f71e075b79492f79f4741e37f835329362022b
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableLegal
statement_id: sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthStep
statement_id: sha256:bd12c5c5928f8822063ec100e0e6e92c5300f5907da4aa64e85595a1ee4c7cb5
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
statement_id: sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthTotal
statement_id: sha256:c4c082551693765b0f6c344f5f6ff825120f019a96ec4d79015c10c10bf774d0
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.width_counting_bridge
statement_id: sha256:a6ad861eda2ca48bc91989542e4b7cc27d81aec8df9a91b8db40c9398c577c72
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.Valid
statement_id: sha256:214fcd95916dbdaa9b9ace506c545eeb309580e42df33d25224d324be358ccb9
D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
rowLegal: proof_shape=bind-only; consumers=a, a_eq_w, classCount, counting_bridge, firstCount, initial_counts, initial_valid, instDecidableRowLegal, row_counts, total2, v2, v_eq_w, valid_next, zero_count
bonds: proof_shape=bind-only; consumers=instDecidableBonds, a, bonds_iff, counting_bridge, zero_count
instDecidableRowLegal: proof_shape=bind-only; consumers=a, a_eq_w, classCount, counting_bridge, firstCount, initial_counts, initial_valid, row_counts, total2, v2, v_eq_w, valid_next, zero_count
instDecidableBonds: proof_shape=bind-only; consumers=a, counting_bridge, zero_count
a: proof_shape=bind-only; consumers=a_eq_w, counting_bridge, recurrence, result, zero_count
compatible: proof_shape=bind-only; consumers=bonds_iff, classCount, counting_bridge, instDecidableCompatible, row_counts, v2, v_eq_w, valid_next
instDecidableCompatible: proof_shape=bind-only; consumers=classCount, counting_bridge, row_counts, v2, v_eq_w, valid_next
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v2: proof_shape=bind-only; consumers=a_eq_w, counting_bridge, v_eq_w
total2: proof_shape=bind-only; consumers=counting_bridge, a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, v_eq_w
firstCount: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, v_eq_w
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w; direct_frozen_dependencies=PairStrip.Col, PairStrip.Seen, PairStrip.finish, PairStrip.good, TriangleStrip.Valid, TriangleStrip.widthInstDecidableGood, BooleanRankThreeK4.beta
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, recurrence, result
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28348); direct_frozen_dependencies=PairStrip.Col, PairStrip.Seen, PairStrip.finish, PairStrip.good, PairStrip.pairs, TriangleStrip.Valid, TriangleStrip.widthInstDecidableGood, TriangleStrip.widthInstDecidableLegal, TriangleStrip.widthLegal, TriangleStrip.widthNormal, TriangleStrip.widthStep, TriangleStrip.widthTotal, TriangleStrip.widthV, TriangleStrip.width_counting_bridge, TriangleStrip.colour_bond_iff, BooleanRankThreeK4.beta
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Basic

/-! Literal array counting and a two-class continuation transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip

open HardinA233175PairStrip (Seen Col good finish pairs)
open HardinA233251TriangleStrip
  (widthNormal widthLegal widthStep widthV widthTotal width_counting_bridge colour_bond_iff Valid)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def rowLegal (c : Col) : Prop :=
  c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5

def bonds (c d : Col) : Prop :=
  ∀ j : Fin 2, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

instance instDecidableRowLegal (c : Col) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (_ ∧ _))
private instance instDecidableBonds (c d : Col) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- The literal filtered finite count; the first-cell condition gives the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 2 → Fin 6 => widthLegal rowLegal bonds A)).card

def compatible (p : Fin 3 × Fin 3) (c : Col) : Prop :=
  p.1 ≠ beta (c 0) ∧ p.2 ≠ beta (c 1)

private instance instDecidableCompatible (p : Fin 3 × Fin 3) (c : Col) :
    Decidable (compatible p c) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem bonds_iff (c d : Col) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs, Fin.forall_fin_two]

private abbrev v2 := widthV rowLegal pairs compatible
private abbrev total2 := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total2 (v2 n) := by
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Col,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

/-- One-row continuations ending in the specified second seen flag. -/
def classCount (s : Seen) (p : Fin 3 × Fin 3) (b : Bool) : ℤ :=
  ∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = b then 1 else 0

/-- First rows ending in the specified second seen flag. -/
def firstCount (b : Bool) : ℤ :=
  ∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = b then 1 else 0

private theorem row_counts : ∀ s p, Valid s p →
    (∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = true then (1 : ℤ) else 0) = (if s.2 then 12 else 4) ∧
    (∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = false then (1 : ℤ) else 0) = (if s.2 then 0 else 4) := by
  decide +kernel

private theorem initial_valid : ∀ c : Col,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

private theorem initial_counts :
    (∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) = 0 ∧
    (∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) = 1 := by
  decide +kernel

/-- The single-row class counts and the two first-row class counts. -/
theorem finite_certificate :
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 12 else 4) ∧
      classCount s p false = (if s.2 then 0 else 4)) ∧
    firstCount true = 0 ∧ firstCount false = 1 :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Bool → ℤ
  | 0, _ => 1
  | n + 1, true => 12 * w n true
  | n + 1, false => 4 * w n false + 4 * w n true

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 3 × Fin 3) (h : Valid s p) :
    v2 n s p = w n s.2 := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v2, widthV, widthStep]
    change (∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c then
      v2 n (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Col, (if rowLegal c ∧ compatible p c ∧ good s c then
        v2 n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then (1 : ℤ) else 0) * w n true +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = false
          then (1 : ℤ) else 0) * w n false := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        cases (finish s c).2 <;> simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      show (∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = true then (1 : ℤ) else 0) = (if s.2 then 12 else 4) from
        (finite_certificate.1 s p h).1,
      show (∑ c : Col, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = false then (1 : ℤ) else 0) = (if s.2 then 0 else 4) from
        (finite_certificate.1 s p h).2]
    cases s.2 <;> simp [w]
    ring

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = w n false := by
  rw [counting_bridge, total2, widthTotal]
  change (∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
    v2 n (finish (false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Col, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v2 n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) * w n true +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) * w n false := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      cases (finish (false, false) c).2 <;> simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    show (∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) = 0 from
      finite_certificate.2.1,
    show (∑ c : Col, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) = 1 from
      finite_certificate.2.2]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 3) : ℤ) = 16 * a (n + 2) - 48 * a (n + 1) := by
  rw [show n + 3 = (n + 1) + 1 + 1 by omega, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, widthLegal]

open PowerSeries in
/-- Barker's generating-function identity, with the empty coefficient set to zero. -/
theorem result :
    (1 - 4 * X) * (1 - 12 * X) * (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (1 - 8 * X) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 4 * X) * (1 - 12 * X) * F =
      F - 16 * (F * X ^ 1) + 48 * (F * X ^ 2) := by ring
  have hr : (X * (1 - 8 * X) : PowerSeries ℤ) = X - 8 * X ^ 2 := by ring
  change (1 - 4 * X) * (1 - 12 * X) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 3 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega)]
    have hh := recurrence (n - 3)
    have h3 : n - 3 + 3 = n := by omega
    have h2 : n - 3 + 2 = n - 1 := by omega
    have h1 : n - 3 + 1 = n - 2 := by omega
    rw [h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    change (a 1 : ℤ) = 1 at h1
    change (a 2 : ℤ) = 4 * 1 + 4 * 1 at h2
    norm_num only at h1 h2
    interval_cases n <;> norm_num only [zero_count, h1, h2,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
