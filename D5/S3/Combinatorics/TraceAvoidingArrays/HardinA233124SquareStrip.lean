/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.finite_certificate
   digest: Barker's generating function for normalized six-colour square strips. -/

/-
admission_basis: open-problem-resolution (#28306; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right at the boundary-class map after the
finite one-step premises (scanner fibres, row_counts, valid_next) are normalized.
instDecidableValid is the public decidability instance for Valid.
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
(statement_id sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish
(statement_id sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good
(statement_id sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.Row
(statement_id sha256:b7c502e020b34fb16b6f45eb8f4662622d3137215aa86d5133861c790e91cd34).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.pairs
(statement_id sha256:1082b02d9e62b47407e60e2c9bfbe8f9e6eef2db0b64d1d41f79f2f2492840ff).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff
(statement_id sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.rowLegal
(statement_id sha256:be28ba8e38a531250b809a95236ffb2f5f4e876106346cd44ea2ed1046ba3cc5).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
(statement_id sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableLegal
(statement_id sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthLegal
(statement_id sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthNormal
(statement_id sha256:544f7677e789967b28078e2cb7f71e075b79492f79f4741e37f835329362022b).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthStep
(statement_id sha256:bd12c5c5928f8822063ec100e0e6e92c5300f5907da4aa64e85595a1ee4c7cb5).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthTotal
(statement_id sha256:c4c082551693765b0f6c344f5f6ff825120f019a96ec4d79015c10c10bf774d0).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthV
(statement_id sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.width_counting_bridge
(statement_id sha256:a6ad861eda2ca48bc91989542e4b7cc27d81aec8df9a91b8db40c9398c577c72).
Direct frozen dependency:
D5/S3/Observer/Separation/BooleanRankThreeK4.beta
(statement_id sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.WidthRow
(statement_id sha256:63d18919d9321000a9a3541c82cd4a7aa88a0da2c26ce61e51d7cede756ff789).
Direct frozen dependency:
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.instDecidableRowLegal
(statement_id sha256:8b3f54e6d8ac00ffc4bce4bacb2fa6e6c06ace120e7d2011fb7a8bb54ef78207).

bonds: proof_shape=bind-only; consumers=Legal, bonds_iff, counting_bridge
Legal: proof_shape=bind-only; consumers=a, counting_bridge, zero_count
instDecidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, a_eq_w, zero_count, result
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
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
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

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

-- The column pair labels of the frozen ladder owner.
local notation "labelsOf" => HardinA233176Ladder.pairs

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

abbrev Legal {n : ℕ} (A : Fin n × Fin 3 → Fin 6) : Prop :=
  widthLegal rowLegal bonds A

private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- The literal filtered finite count; the first-cell condition gives the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Fin 6 => Legal A)).card

def compatible (p : Fin 3 → Fin 3) (c : Row) : Prop :=
  ∀ j, p j ≠ beta (c j)

private instance instDecidableCompatible (p : Fin 3 → Fin 3) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labelsOf c) d := by
  simp only [bonds, colour_bond_iff, compatible, HardinA233176Ladder.pairs]

private abbrev v := widthV rowLegal labelsOf compatible

private abbrev total := widthTotal rowLegal labelsOf

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labelsOf compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 3 → Fin 3) : Prop :=
  s.1 = true ∧ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧ (s.2 = false → ∀ j, p j ≠ 2)

instance instDecidableValid (s : Seen) (p : Fin 3 → Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Fin 3 → Fin 3) : Fin 3 :=
  if s.2 then if p 0 = p 2 then 1 else 2 else 0

def transfer (i k : Fin 3) : ℤ :=
  ![![8, 8, 8], ![0, 24, 16], ![0, 16, 16]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (labelsOf c) := by
  have hv : ∀ (s : Seen) (c : Row), s.1 = true → rowLegal c → good s c →
      Valid (finish s c) (labelsOf c) := by decide +kernel
  intro s p hp c hc
  exact hv s c hp.1 hc.1 hc.2.2

def classCount (s : Seen) (p : Fin 3 → Fin 3) (k : Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labelsOf c) = k then 1 else 0

def firstCount (k : Fin 3) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labelsOf c) = k then 1 else 0

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
      Valid (finish (false, false) c) (labelsOf c) := by
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
        v n (finish s c) (labelsOf c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labelsOf c) = 0 then (1 : ℤ) else 0) * w n 0 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labelsOf c) = 1 then (1 : ℤ) else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labelsOf c) = 2 then (1 : ℤ) else 0) * w n 2 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        generalize boundaryClass (finish s c) (labelsOf c) = k
        fin_cases k <;> simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    suffices hstep : classCount s p 0 * w n 0 + classCount s p 1 * w n 1 +
        classCount s p 2 * w n 2 = w (n + 1) (boundaryClass s p) by
      simpa only [classCount] using hstep
    rw [finite_certificate.1 s p h 0, finite_certificate.1 s p h 1,
      finite_certificate.1 s p h 2]
    generalize boundaryClass s p = k
    fin_cases k <;> simp [transfer, w]

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 2 * w n 0 + w n 2 := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labelsOf c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labelsOf c) = 0 then (1 : ℤ) else 0) *
          w n 0 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labelsOf c) = 1 then (1 : ℤ) else 0) *
          w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labelsOf c) = 2 then (1 : ℤ) else 0) *
          w n 2 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      generalize boundaryClass (finish (false, false) c) (labelsOf c) = k
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
