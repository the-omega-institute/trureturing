/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.finite_certificate,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.distribution_step,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.distribution_relation
   digest: Hardin's seven-term recurrence for literal normalized five-column diagonal strips. -/

/-
admission_basis: open-problem-resolution (#29002; Proved)
escape_witness: finite_certificate proves this graph's seven-class transfer,
consumed by the all-height reduction and result and not supplied by frozen owners.
distribution_step and distribution_relation are consumed bind-only helpers
(finite computations on the transfer and the reused first-row distribution).
bonds: proof_shape=bind-only; consumers=decidableBonds, a, bonds_iff, counting_bridge
decidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, result
compatible: proof_shape=bind-only; consumers=decidableCompatible, bonds_iff, v, valid_next, classCount
decidableCompatible: proof_shape=bind-only; consumers=v, classCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge, v_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
transfer: proof_shape=bind-only; consumers=finite_certificate, w, distribution_step
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=class_fibres, finite_certificate, v_eq_w
class_fibres: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=v_eq_w; escape_witness=finite_certificate
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, shifted_count
v_eq_w: proof_shape=content; consumers=a_eq_w; escape_witness=finite_certificate
a_eq_w: proof_shape=content; consumers=shifted_count; escape_witness=finite_certificate
distribution: proof_shape=bind-only; consumers=distribution_step, shifted_count, distribution_relation
distribution_step: proof_shape=bind-only; consumers=shifted_count
shifted_count: proof_shape=content; consumers=result; escape_witness=finite_certificate
distribution_relation: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=terminal result; escape_witness=finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Lean.Elab.Tactic.Omega

/-! Horizontal and both diagonal bonds constrain the literal row-major normalized arrays. -/
set_option maxRecDepth 100000
set_option Elab.async false
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233253TriangleStrip (Row rowLegal)
open HardinA233254TriangleStrip (Boundary Valid)
open HardinA233126SquareStrip (labels boundaryClass firstCount initial_valid label_sum)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 4,
    (c j.castSucc ≠ d j.succ ∧ (c j.castSucc).val + (d j.succ).val ≠ 5) ∧
    (c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5)

private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, (_ ∧ _) ∧ (_ ∧ _)))

/-- The literal filtered finite count, with the owner scanner and first-cell condition. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 5 → Fin 6 => widthLegal rowLegal bonds A)).card

def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 4, p j.castSucc ≠ beta (c j.succ) ∧ p j.succ ≠ beta (c j.castSucc)

private instance decidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = widthTotal rowLegal labels (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

def transfer (i k : Fin 7) : ℤ :=
  ![![32, 32, 64, 32, 32, 0, 32],
    ![0, 96, 128, 64, 64, 0, 64],
    ![0, 64, 128, 32, 32, 0, 64],
    ![0, 64, 64, 64, 64, 32, 0],
    ![0, 32, 32, 32, 64, 32, 0],
    ![0, 0, 0, 32, 64, 32, 0],
    ![0, 64, 128, 0, 0, 0, 64]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (labels c) := by
  intro s p hp c hc
  exact HardinA233126SquareStrip.row_valid s c hp.1 hc.1 hc.2.2

def classCount (s : Seen) (p : Boundary) (k : Fin 7) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Boundary) (k : Fin 7) :
    classCount s p k = ∑ q : Boundary,
      rowWeight s q * if (∀ j : Fin 4, q j.castSucc ≠ q j.succ) ∧
        (∀ j : Fin 4, p j.castSucc ≠ q j.succ ∧ p j.succ ≠ q j.castSucc) ∧
        boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 5 s (fun t q =>
    if (∀ j : Fin 4, q j.castSucc ≠ q j.succ) ∧
      (∀ j : Fin 4, p j.castSucc ≠ q j.succ ∧ p j.succ ≠ q j.castSucc) ∧
      boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

set_option maxHeartbeats 0 in
private theorem finite_certificate : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  suffices h : ∀ k : Fin 7, ∀ s p, Valid s p →
      classCount s p k = transfer (boundaryClass s p) k by
    intro s p hp k
    exact h k s p hp
  intro k
  fin_cases k <;> simp only [class_fibres, label_sum, Valid] <;> decide +kernel

private def w : ℕ → Fin 7 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 7, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 7, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) * w n k := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k : Fin 7, classCount s p k * w n k) = _
    simp_rw [finite_certificate s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 7, ![8, 0, 8, 4, 8, 4, 4] k * w n k := by
  rw [counting_bridge, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 7, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labels c) = k then (1 : ℤ) else 0) *
          w n k := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ k : Fin 7, firstCount k * w n k) = _
  simp_rw [HardinA233126SquareStrip.finite_certificate.2]

private def distribution (r : Fin 8) (k : Fin 7) : ℤ :=
  ![![8, 0, 8, 4, 8, 4, 4],
    ![256, 1536, 2560, 1152, 1536, 512, 1024],
    ![8192, 507904, 794624, 327680, 393216, 102400, 335872],
    ![262144, 154927104, 243793920, 95027200, 110886912, 26345472, 105119744],
    ![8388608, 46841987072, 74138517504, 28198305792, 32589742080, 7432306688, 32254197760],
    ![268435456, 14153796288512, 22462142087168,
      8455985299456, 9736690860032, 2183051345920, 9807289384960],
    ![8589934592, 4276773814534144, 6794947499917312,
      2547254908944384, 2928686659534848, 652023280173056, 2971095166615552],
    ![274877906944, 1292339579008843776, 2054223346609946624,
      768759151248539648, 883341869319192576, 196094875156873216, 898740529666195456]] r k

private theorem distribution_step : ∀ (r : Fin 7) (k : Fin 7),
    distribution r.succ k = ∑ i : Fin 7, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 8) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 7, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

private theorem distribution_relation : ∀ k : Fin 7,
    distribution 7 k = 480 * distribution 6 k - 60416 * distribution 5 k +
      1966080 * distribution 4 k + 22020096 * distribution 3 k -
      1845493760 * distribution 2 k + 22548578304 * distribution 1 k -
      68719476736 * distribution 0 k := by
  decide +kernel

/-- Hardin's recurrence for every height at least eight, with the index shift explicit. -/
theorem result (n : ℕ) :
    (a (n + 8) : ℤ) = 480 * a (n + 7) - 60416 * a (n + 6) +
      1966080 * a (n + 5) + 22020096 * a (n + 4) -
      1845493760 * a (n + 3) + 22548578304 * a (n + 2) -
      68719476736 * a (n + 1) := by
  have h0 := shifted_count (0 : Fin 8) n
  have h1 := shifted_count (1 : Fin 8) n
  have h2 := shifted_count (2 : Fin 8) n
  have h3 := shifted_count (3 : Fin 8) n
  have h4 := shifted_count (4 : Fin 8) n
  have h5 := shifted_count (5 : Fin 8) n
  have h6 := shifted_count (6 : Fin 8) n
  have h7 := shifted_count (7 : Fin 8) n
  change (a (n + 1) : ℤ) = _ at h0
  change (a (n + 2) : ℤ) = _ at h1
  change (a (n + 3) : ℤ) = _ at h2
  change (a (n + 4) : ℤ) = _ at h3
  change (a (n + 5) : ℤ) = _ at h4
  change (a (n + 6) : ℤ) = _ at h5
  change (a (n + 7) : ℤ) = _ at h6
  change (a (n + 8) : ℤ) = _ at h7
  rw [h7, h6, h5, h4, h3, h2, h1, h0]
  simp_rw [distribution_relation, sub_mul, add_mul]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, Finset.mul_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
