/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.finite_certificate
   digest: The recurrence for literal normalized five-column square strips. -/

/-
admission_basis: open-problem-resolution (#28572; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right at the boundary-class map after the
finite one-step premises (scanner fibres, row_counts, valid_next) are normalized.
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
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Literal five-column square-strip counts and their all-height class reduction. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

abbrev Row := Fin 5 → Fin 6

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 5, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 5, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

private instance decidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- Literal filtered array count. The first-cell condition sets the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 5 → Fin 6 => widthLegal rowLegal bonds A)).card

def labels (c : Row) : Fin 5 → Fin 3 := fun j => beta (c j)
def compatible (p : Fin 5 → Fin 3) (c : Row) : Prop := ∀ j, p j ≠ beta (c j)
private instance decidableCompatible (p : Fin 5 → Fin 3) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible
private abbrev total := widthTotal rowLegal labels

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 5 → Fin 3) : Prop :=
  s.1 = true ∧ (∀ j : Fin 4, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)
private instance decidableValid (s : Seen) (p : Fin 5 → Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Fin 5 → Fin 3) : Fin 7 :=
  if s.2 then
    if p 0 = p 2 ∧ p 2 = p 4 then (if p 1 = p 3 then 1 else 3)
    else if p 1 = p 3 then (if p 0 = p 4 then 6 else 2)
    else if p 0 = p 3 ∧ p 1 = p 4 then 5 else 4
  else 0

def transfer (i k : Fin 7) : ℤ :=
  ![![32, 32, 64, 32, 32, 0, 32], ![0, 96, 128, 64, 64, 0, 64],
    ![0, 64, 96, 64, 64, 32, 32], ![0, 64, 128, 64, 64, 0, 64],
    ![0, 32, 64, 32, 96, 32, 32], ![0, 0, 64, 0, 64, 64, 0],
    ![0, 64, 64, 64, 64, 0, 64]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (labels c) := by
  have hv : ∀ (s : Seen) (c : Row), s.1 = true → rowLegal c → good s c →
      Valid (finish s c) (labels c) := by decide +kernel
  intro s p hp c hc
  exact hv s c hp.1 hc.1 hc.2.2

def classCount (s : Seen) (p : Fin 5 → Fin 3) (k : Fin 7) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

def firstCount (k : Fin 7) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Fin 5 → Fin 3) (k : Fin 7) :
    classCount s p k = ∑ q : Fin 5 → Fin 3,
      rowWeight s q * if (∀ j : Fin 4, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 5 s (fun t q =>
    if (∀ j : Fin 4, q j.castSucc ≠ q j.succ) ∧
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

private theorem label_sum (g : (Fin 5 → Fin 3) → ℤ) :
    (∑ q, g q) = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ∑ e : Fin 3,
      g ![a, b, c, d, e] := by
  let e : (Fin 5 → Fin 3) ≃ Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
    { toFun := fun q => (q 0, q 1, q 2, q 3, q 4)
      invFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]
      left_inv := by intro q; ext j; fin_cases j <;> rfl
      right_inv := by rintro ⟨a, b, c, d, e⟩; rfl }
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

private theorem initial_counts : ∀ k, firstCount k = ![8, 0, 8, 4, 8, 4, 4] k := by
  decide +kernel

/-- The exact single-row transitions and first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![8, 0, 8, 4, 8, 4, 4] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 7 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 7, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 5 → Fin 3) (h : Valid s p) :
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
    simp_rw [finite_certificate.1 s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 7, ![8, 0, 8, 4, 8, 4, 4] k * w n k := by
  rw [counting_bridge, total, widthTotal]
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
  simp_rw [finite_certificate.2]

private def distribution (r k : Fin 7) : ℤ :=
  ![![8, 0, 8, 4, 8, 4, 4],
    ![256, 1536, 2816, 1536, 2304, 768, 1280],
    ![8192, 589824, 958464, 540672, 737280, 212992, 450560],
    ![262144, 205258752, 326893568, 186384384, 247201792, 67895296, 155713536],
    ![8388608, 70439141376, 111660761088, 63870861312,
      84037074944, 22716350464, 53410267136],
    ![268435456, 24103893336064, 38162126602240, 21849840812032,
      28682060038144, 7716177182720, 18276696457216],
    ![8589934592, 8242282759192576, 13044855060037632, 7470958172438528,
      9800445354573824, 2632849312186368, 6249770121166848]] r k

private theorem distribution_step : ∀ (r : Fin 6) (k : Fin 7),
    distribution r.succ k = ∑ i : Fin 7, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 7) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 7, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

/-- Hardin's recurrence for every height at least seven, with the index shift explicit. -/
theorem result (n : ℕ) :
    (a (n + 7) : ℤ) = 544 * a (n + 6) - 82944 * a (n + 5) +
      5144576 * a (n + 4) - 146800640 * a (n + 3) +
      1879048192 * a (n + 2) - 8589934592 * a (n + 1) := by
  rw [shifted_count (6 : Fin 7) n, shifted_count (5 : Fin 7) n,
    shifted_count (4 : Fin 7) n, shifted_count (3 : Fin 7) n,
    shifted_count (2 : Fin 7) n, shifted_count (1 : Fin 7) n,
    shifted_count (0 : Fin 7) n]
  simp only [distribution, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue]
  ring

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
