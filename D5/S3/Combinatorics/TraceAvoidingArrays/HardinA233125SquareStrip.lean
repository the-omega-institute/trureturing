/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.finite_certificate
   digest: The generating function for literal normalized four-column square strips. -/

/-
admission_basis: open-problem-resolution (#28505; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right at the boundary-class map after the
finite one-step premises (scanner fibres, row_counts, valid_next) are normalized.
label_sum is the public reindexing identity for sums over four-column label rows.
Direct frozen dependencies (declaration statement_ids):
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthTotal
statement_id: sha256:c4c082551693765b0f6c344f5f6ff825120f019a96ec4d79015c10c10bf774d0
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.width_counting_bridge
statement_id: sha256:a6ad861eda2ca48bc91989542e4b7cc27d81aec8df9a91b8db40c9398c577c72
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableLegal
statement_id: sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
statement_id: sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthStep
statement_id: sha256:bd12c5c5928f8822063ec100e0e6e92c5300f5907da4aa64e85595a1ee4c7cb5
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthNormal
statement_id: sha256:544f7677e789967b28078e2cb7f71e075b79492f79f4741e37f835329362022b
D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
Row: proof_shape=bind-only; consumers=rowLegal, bonds, a
rowLegal: proof_shape=bind-only; consumers=a, counting_bridge, row_counts
bonds: proof_shape=bind-only; consumers=a, bonds_iff
decidableRowLegal: proof_shape=bind-only; consumers=a, counting_bridge
decidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=a_eq_w, result
labels: proof_shape=bind-only; consumers=v, classCount
compatible: proof_shape=bind-only; consumers=v, classCount
decidableCompatible: proof_shape=bind-only; consumers=v, classCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge, v_eq_w
total: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next, row_counts, initial_valid
decidableValid: proof_shape=bind-only; consumers=valid_next, row_counts, initial_valid
boundaryClass: proof_shape=bind-only; consumers=row_counts, v_eq_w
transfer: proof_shape=bind-only; consumers=row_counts, v_eq_w
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=row_counts, v_eq_w
firstCount: proof_shape=bind-only; consumers=initial_counts, a_eq_w
class_fibres: proof_shape=bind-only; consumers=row_counts
label_sum: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, recurrence, result
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28505)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Literal four-column square-strip counts and their all-height class reduction. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

abbrev Row := Fin 4 → Fin 6

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 3, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 4, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

instance decidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- Literal filtered array count. The first-cell condition sets the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 4 → Fin 6 => widthLegal rowLegal bonds A)).card

def labels (c : Row) : Fin 4 → Fin 3 := fun j => beta (c j)
def compatible (p : Fin 4 → Fin 3) (c : Row) : Prop := ∀ j, p j ≠ beta (c j)
private instance decidableCompatible (p : Fin 4 → Fin 3) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible
private abbrev total := widthTotal rowLegal labels

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 4 → Fin 3) : Prop :=
  s.1 = true ∧ (∀ j : Fin 3, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)
private instance decidableValid (s : Seen) (p : Fin 4 → Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Fin 4 → Fin 3) : Fin 4 :=
  if s.2 then if p 0 = p 2 ∧ p 1 = p 3 then 1 else if p 0 = p 3 then 3 else 2 else 0

def transfer (i k : Fin 4) : ℤ :=
  ![![16, 16, 32, 8], ![0, 48, 64, 16], ![0, 32, 64, 16], ![0, 16, 32, 32]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (labels c) := by
  have hv : ∀ (s : Seen) (c : Row), s.1 = true → rowLegal c → good s c →
      Valid (finish s c) (labels c) := by decide +kernel
  intro s p hp c hc
  exact hv s c hp.1 hc.1 hc.2.2

def classCount (s : Seen) (p : Fin 4 → Fin 3) (k : Fin 4) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

def firstCount (k : Fin 4) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Fin 4 → Fin 3) (k : Fin 4) :
    classCount s p k = ∑ q : Fin 4 → Fin 3,
      rowWeight s q * if (∀ j : Fin 3, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 4 s (fun t q =>
    if (∀ j : Fin 3, q j.castSucc ≠ q j.succ) ∧
      (∀ j, p j ≠ q j) ∧ boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

theorem label_sum (g : (Fin 4 → Fin 3) → ℤ) :
    (∑ q, g q) = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      g ![a, b, c, d] := by
  let e : (Fin 4 → Fin 3) ≃ Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
    { toFun := fun q => (q 0, q 1, q 2, q 3)
      invFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2]
      left_inv := by intro q; ext j; fin_cases j <;> rfl
      right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [class_fibres, label_sum]
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (labels c) := by
  decide +kernel

private theorem initial_counts : ∀ k, firstCount k = ![4, 0, 4, 2] k := by
  decide +kernel

/-- The exact single-row transitions and first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![4, 0, 4, 2] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 4 → ℤ
  | 0, _ => 1
  | n + 1, k => if k = 0 then 16 * w n 0 + 16 * w n 1 + 32 * w n 2 + 8 * w n 3
      else if k = 1 then 48 * w n 1 + 64 * w n 2 + 16 * w n 3
      else if k = 2 then 32 * w n 1 + 64 * w n 2 + 16 * w n 3
      else 16 * w n 1 + 32 * w n 2 + 32 * w n 3

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 4 → Fin 3) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 4, (if rowLegal c ∧ compatible p c ∧ good s c ∧
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
    change (∑ k : Fin 4, classCount s p k * w n k) = _
    simp_rw [finite_certificate.1 s p h]
    generalize boundaryClass s p = k
    fin_cases k <;> simp [transfer, w, Fin.sum_univ_succ, add_assoc]

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 4 * w n 0 + 4 * w n 2 + 2 * w n 3 := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 4, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
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
  change (∑ k : Fin 4, firstCount k * w n k) = _
  simp_rw [finite_certificate.2]
  simp [Fin.sum_univ_succ, add_assoc]

private theorem recurrence (n : ℕ) :
    (a (n + 5) : ℤ) = 160 * a (n + 4) - 6144 * a (n + 3) +
      86016 * a (n + 2) - 393216 * a (n + 1) := by
  rw [show n + 5 = (n + 1 + 1 + 1 + 1) + 1 by omega,
    show n + 4 = (n + 1 + 1 + 1) + 1 by omega,
    show n + 3 = (n + 1 + 1) + 1 by omega,
    show n + 2 = (n + 1) + 1 by omega,
    a_eq_w, a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  norm_num only [Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, widthLegal]

open PowerSeries in
/-- The exact generating-function identity, with coefficient zero at height zero. -/
theorem result :
    (1 - 16 * X) * (1 - 144 * X + 3840 * X ^ 2 - 24576 * X ^ 3) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
        X * (10 - 704 * X + 14336 * X ^ 2 - 81920 * X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 16 * X) * (1 - 144 * X + 3840 * X ^ 2 - 24576 * X ^ 3) * F =
      F - 160 * (F * X ^ 1) + 6144 * (F * X ^ 2) - 86016 * (F * X ^ 3) +
        393216 * (F * X ^ 4) := by ring
  have hr : (X * (10 - 704 * X + 14336 * X ^ 2 - 81920 * X ^ 3) : PowerSeries ℤ) =
      10 * X - 704 * X ^ 2 + 14336 * X ^ 3 - 81920 * X ^ 4 := by ring
  change (1 - 16 * X) * (1 - 144 * X + 3840 * X ^ 2 - 24576 * X ^ 3) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 5 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega)]
    have hh := recurrence (n - 5)
    have h5 : n - 5 + 5 = n := by omega
    have h4 : n - 5 + 4 = n - 1 := by omega
    have h3 : n - 5 + 3 = n - 2 := by omega
    have h2 : n - 5 + 2 = n - 3 := by omega
    have h1 : n - 5 + 1 = n - 4 := by omega
    rw [h5, h4, h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    have h4 := a_eq_w 3
    change (a 1 : ℤ) = 10 at h1
    change (a 2 : ℤ) = 896 at h2
    change (a 3 : ℤ) = 96256 at h3
    change (a 4 : ℤ) = 10674176 at h4
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3, h4,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
