/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.finite_certificate
   digest: Barker's generating function for the literal eight-colour three-column strip. -/

/-
admission_basis: open-problem-resolution (#28599; Proved)
escape_witness: none
Direct frozen dependencies (GID and declaration statement_id):
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Seen
statement_id: sha256:81b88997a2c3d2f53ff882dacf64140ab25fdfa46060ae927c1c63ee630736fd
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.WidthRow
statement_id: sha256:ae15c3e642a6c1515543b2ddf359b409d2043f62636f436a563813f6dfe69872
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.beta
statement_id: sha256:f2505b223dba09056766886dde8961967e3030e856c18d65de2734fae3a38dee
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.colour_bond_iff
statement_id: sha256:d7a7cd2df86ff06e776596be1ef85f1977a9d437358db2daf55cf0bd676c9eb0
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish
statement_id: sha256:7054a413386be5cdcacaeaf88ae7ecec7159bfda28cda49e2145b07fbdfb1312
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good
statement_id: sha256:417a6ea98050fbf77c7289c3ffbdebbaee51eb553d11bf873bb6b2a76938f6f6
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableGood
statement_id: sha256:ba6f67f310ba830404c486a59fabfe407663a527a36a27ef60d2fb48d44e43b7
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableLegal
statement_id: sha256:7a2f2772a17ec13ac856e41a4d2303e53c23af078293aa52bef20c84fc42c315
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthLegal
statement_id: sha256:2b02b5cd250ec66f51ecff4b5862dde43d02334522762d1502ef1672f512bc41
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthNormal
statement_id: sha256:e95e90b3d2e434d2f3689955d5c1a43f761b459878d8d005ae29d69cdb6dde66
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthStep
statement_id: sha256:b7e892dff9721f779553cc5b9c84fc752961a64b6ee12de6deca09a57acd7e3d
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthTotal
statement_id: sha256:8d08772c073cb671fe0c90dc55e2ac53a82d23e2d9db0450d416622b7b3fa7fa
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthV
statement_id: sha256:36f617fb195a7cafd2772fde4192f8f89537893f5a88b725d0cf6c632d0acb86
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.width_counting_bridge
statement_id: sha256:cdf4ecd31fa9f5461d1e5406bc32cd51c7e4ad71dd7c890ccdc676bea7c5943e
Compiler-generated direct constants of the frozen owner (not inventory members):
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.allowed._proof_1
statement_id: sha256:2e96afc6083f3f5ff2c0d41bd86fbc5db45d2b998a685826e63d55ca74060906
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthStep.eq_1
statement_id: sha256:d2dcfe5907345ebab6e712d8977529311389ec5e41ad5bb926ac4d10f5ce5206
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthTotal.eq_1
statement_id: sha256:1a7da251e7485965ff9889cb993634650f45a9393e7b09edabe3f0e292e86622
D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthV.eq_2
statement_id: sha256:01b4e052e81856c7b5fe6d8595e667de6a59176a1e943a332d62fdd7a124e302
Closed, unfrozen dependency: TransferMatrix.scalarRelationShift.
Every declaration has proof_shape=bind-only. The all-height class reduction is
Function.Semiconj.iterate_right after normalization of the finite one-step premises.
Consumers list named local users, contracting generated type/value intermediates;
the terminal result also names its compiled Reg audit consumer.
Row: proof_shape=bind-only; consumers=a_eq_w, bonds, bonds_iff, classCount, compatible, firstCount, initial_valid, instDecidableBonds, instDecidableCompatible, instDecidableRowLegal, pairs, rowLegal, v_eq_w, valid_next
rowLegal: proof_shape=bind-only; consumers=a, a_eq_w, classCount, counting_bridge, firstCount, initial_valid, instDecidableRowLegal, total3, v3, v_eq_w, valid_next, zero_count
bonds: proof_shape=bind-only; consumers=a, bonds_iff, counting_bridge, instDecidableBonds, zero_count
instDecidableRowLegal: proof_shape=bind-only; consumers=a, a_eq_w, classCount, counting_bridge, firstCount, initial_valid, total3, v3, v_eq_w, valid_next, zero_count
instDecidableBonds: proof_shape=bind-only; consumers=a, counting_bridge, zero_count
a: proof_shape=bind-only; consumers=a_eq_w, counting_bridge, recurrence, result, zero_count
pairs: proof_shape=bind-only; consumers=a_eq_w, bonds_iff, classCount, counting_bridge, firstCount, initial_valid, total3, v3, v_eq_w, valid_next
compatible: proof_shape=bind-only; consumers=bonds_iff, classCount, counting_bridge, instDecidableCompatible, v3, v_eq_w, valid_next
instDecidableCompatible: proof_shape=bind-only; consumers=classCount, counting_bridge, v3, v_eq_w, valid_next
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v3: proof_shape=bind-only; consumers=a_eq_w, counting_bridge, v_eq_w
total3: proof_shape=bind-only; consumers=a_eq_w, counting_bridge
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, initial_valid, instDecidableValid, recurrence, row_counts, v_eq_w, valid_next
instDecidableValid: proof_shape=bind-only; consumers=initial_valid, row_counts, valid_next
seenClass: proof_shape=bind-only; consumers=a_eq_w, classCount, finite_certificate, firstCount, recurrence, row_counts, v_eq_w
T: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, recurrence, row_counts, v_eq_w, vector_relation, w
classCount: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, recurrence, row_counts, v_eq_w
firstCount: proof_shape=bind-only; consumers=a_eq_w, finite_certificate, initial_counts, recurrence, v_eq_w
valid_next: proof_shape=bind-only; consumers=v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_counts: proof_shape=bind-only; consumers=finite_certificate
vector_relation: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=a_eq_w, recurrence, v_eq_w
w: proof_shape=bind-only; consumers=a_eq_w, recurrence, result, v_eq_w
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233197Strip.audit
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Basic

/-! The existing eight-colour scanner is specialized to three-column boundaries. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233197Strip

open HardinA233196Strip (Seen WidthRow beta good finish widthLegal widthV widthStep
  widthTotal width_counting_bridge colour_bond_iff)

abbrev Row := WidthRow 3

def rowLegal (c : Row) : Prop :=
  (c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 7) ∧
    (c 1 ≠ c 2 ∧ (c 1).val + (c 2).val ≠ 7)

def bonds (c d : Row) : Prop :=
  (∀ j : Fin 3, c j ≠ d j ∧ (c j).val + (d j).val ≠ 7) ∧
    (c 1 ≠ d 0 ∧ (c 1).val + (d 0).val ≠ 7) ∧
    (c 2 ≠ d 1 ∧ (c 2).val + (d 1).val ≠ 7)

private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∧ (_ ∧ _)))

private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((∀ _, _ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _)))

/-- The literal filtered count. The first-cell existential fixes `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Fin 8 =>
    widthLegal rowLegal bonds A)).card

def pairs (c : Row) : Fin 3 → Fin 4 := fun j => beta (c j)

def compatible (p : Fin 3 → Fin 4) (c : Row) : Prop :=
  (∀ j : Fin 3, p j ≠ beta (c j)) ∧ p 1 ≠ beta (c 0) ∧ p 2 ≠ beta (c 1)

private instance instDecidableCompatible (p : Fin 3 → Fin 4) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable ((∀ _, _) ∧ _ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private abbrev v3 := widthV rowLegal pairs compatible
private abbrev total3 := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total3 (v3 n) := by
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 3 → Fin 4) : Prop :=
  s.1 = true ∧ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧
    (s.2.1 = false → ∀ j, (p j).val < 2) ∧
    (s.2.2 = false → ∀ j, (p j).val < 3) ∧ (s.2.2 = true → s.2.1 = true)

private instance instDecidableValid (s : Seen) (p : Fin 3 → Fin 4) :
    Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → ∀ _, _) ∧ (_ → ∀ _, _) ∧ (_ → _)))

def seenClass (s : Seen) (p : Fin 3 → Fin 4) : Fin 5 :=
  if s.2.1 then
    if s.2.2 then (if p 0 = p 2 then 3 else 4) else (if p 0 = p 2 then 1 else 2)
  else 0

def T : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![0, 0, 0, 2, 2], ![0, 0, 0, 8, 8], ![0, 0, 8, 4, 16],
    ![0, 0, 0, 16, 16], ![0, 0, 0, 8, 40]]

def classCount (s : Seen) (p : Fin 3 → Fin 4) (b : Fin 5) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    seenClass (finish s c) (pairs c) = b then 1 else 0

def firstCount (b : Fin 5) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c ∧
    seenClass (finish (false, false, false) c) (pairs c) = b then 1 else 0

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c →
      Valid (finish (false, false, false) c) (pairs c) := by
  decide +kernel

private theorem row_counts : ∀ s p, Valid s p → ∀ b,
    classCount s p b = T (seenClass s p) b := by
  decide +kernel

private theorem initial_counts : ∀ b, firstCount b = (![2, 0, 1, 0, 0] : Fin 5 → ℤ) b := by
  decide +kernel

private theorem vector_relation :
    (T ^ (1 + 3)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 3, (![4096, -960, 64] : Fin 3 → ℤ) j •
        (T ^ (1 + j.val)).mulVec (1 : Fin 5 → ℤ) := by
  decide +kernel

/-- Finite single-row counts and the eventual cubic relation for continuation vectors. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ b, classCount s p b = T (seenClass s p) b) ∧
    (∀ b, firstCount b = (![2, 0, 1, 0, 0] : Fin 5 → ℤ) b) ∧
    (T ^ (1 + 3)).mulVec (1 : Fin 5 → ℤ) =
      ∑ j : Fin 3, (![4096, -960, 64] : Fin 3 → ℤ) j •
        (T ^ (1 + j.val)).mulVec (1 : Fin 5 → ℤ) :=
  ⟨row_counts, initial_counts, vector_relation⟩

private def w (n : ℕ) : Fin 5 → ℤ := (T ^ n).mulVec 1

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 3 → Fin 4) (h : Valid s p) :
    v3 n s p = w n (seenClass s p) := by
  induction n generalizing s p with
  | zero => simp [v3, widthV, w, Matrix.one_mulVec]
  | succ n ih =>
    rw [v3, widthV, widthStep]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      v3 n (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v3 n (finish s c) (pairs c) else 0) =
        ∑ b : Fin 5, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          seenClass (finish s c) (pairs c) = b then (1 : ℤ) else 0) * w n b := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ b : Fin 5, classCount s p b * w n b) = _
    simp_rw [finite_certificate.1 s p h]
    change _ = (T ^ (n + 1)).mulVec (1 : Fin 5 → ℤ) (seenClass s p)
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 2 * w n 0 + w n 2 := by
  rw [counting_bridge, total3, widthTotal]
  change (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
    v3 n (finish (false, false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
      v3 n (finish (false, false, false) c) (pairs c) else 0) =
      ∑ b : Fin 5, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c ∧
        seenClass (finish (false, false, false) c) (pairs c) = b then (1 : ℤ) else 0) * w n b := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ b : Fin 5, firstCount b * w n b) = _
  simp [finite_certificate.2.1, Fin.sum_univ_succ]

private theorem recurrence (n : ℕ) :
    (a (n + 5) : ℤ) = 64 * a (n + 4) - 960 * a (n + 3) + 4096 * a (n + 2) := by
  have hh := TransferMatrix.scalarRelationShift T ![2, 0, 1, 0, 0] 3 1
    ![4096, -960, 64] finite_certificate.2.2 n
  norm_num [dotProduct, Fin.sum_univ_succ, Nat.add_assoc] at hh
  rw [show n + 5 = (n + 1 + 3) + 1 by omega,
    show n + 4 = (n + 1 + 2) + 1 by omega,
    show n + 3 = (n + 1 + 1) + 1 by omega,
    show n + 2 = (n + 1 + 0) + 1 by omega, a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  dsimp [w]
  linarith

private theorem zero_count : a 0 = 0 := by simp [a, widthLegal]

open PowerSeries in
/-- Barker's identity for the literal count, with the convention `a 0 = 0`. -/
theorem result :
    (1 - 8 * X) * (1 - 56 * X + 512 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
        X * (3 - 156 * X + 2016 * X ^ 2 - 7168 * X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 8 * X) * (1 - 56 * X + 512 * X ^ 2) * F =
      F - 64 * (F * X ^ 1) + 960 * (F * X ^ 2) - 4096 * (F * X ^ 3) := by ring
  have hr : (X * (3 - 156 * X + 2016 * X ^ 2 - 7168 * X ^ 3) : PowerSeries ℤ) =
      3 * X ^ 1 - 156 * X ^ 2 + 2016 * X ^ 3 - 7168 * X ^ 4 := by ring
  change (1 - 8 * X) * (1 - 56 * X + 512 * X ^ 2) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X_pow, F, coeff_mk]
  by_cases hn : 5 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega),
      ite_eq_right (show n ≠ 4 by omega), mul_zero, sub_zero]
    have hh := recurrence (n - 5)
    have h5 : n - 5 + 5 = n := by omega
    have h4 : n - 5 + 4 = n - 1 := by omega
    have h3 : n - 5 + 3 = n - 2 := by omega
    have h2 : n - 5 + 2 = n - 3 := by omega
    rw [h5, h4, h3, h2] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    have h4 := a_eq_w 3
    have hw0 : 2 * w 0 0 + w 0 2 = 3 := by decide +kernel
    have hw1 : 2 * w 1 0 + w 1 2 = 36 := by decide +kernel
    have hw2 : 2 * w 2 0 + w 2 2 = 1440 := by decide +kernel
    have hw3 : 2 * w 3 0 + w 3 2 = 62720 := by decide +kernel
    rw [hw0] at h1
    rw [hw1] at h2
    rw [hw2] at h3
    rw [hw3] at h4
    norm_num only at h1 h2 h3 h4
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3, h4,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233197Strip
