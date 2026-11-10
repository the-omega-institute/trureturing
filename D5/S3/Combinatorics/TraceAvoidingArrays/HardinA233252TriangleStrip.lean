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
Row: proof_shape=bind-only; consumers=rowLegal, pairs, compatible, Valid, classCount, firstCount
Boundary: proof_shape=bind-only; consumers=pairs, compatible, Valid
rowLegal: proof_shape=bind-only; consumers=instDecidableRowLegal, classCount, a
bonds: proof_shape=bind-only; consumers=instDecidableBonds, bonds_iff, a
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableRowLegal: proof_shape=bind-only; consumers=instDecidableLegal, classCount
instDecidableBonds: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
instDecidableCompatible: proof_shape=bind-only; consumers=classCount
a: proof_shape=bind-only; consumers=counting_bridge, zero_count, result
pairs: proof_shape=bind-only; consumers=bonds_iff, compatible, classCount, a_eq_w
compatible: proof_shape=bind-only; consumers=bonds_iff, counting_bridge, classCount
colour_bond_iff: proof_shape=bind-only; consumers=bonds_iff, class_fibres
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=v_eq_w
total: proof_shape=bind-only; consumers=a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next, row_counts, initial_valid, v_eq_w
instDecidableValid: proof_shape=bind-only; consumers=row_counts, initial_valid
boundaryClass: proof_shape=bind-only; consumers=classCount, firstCount, row_counts, initial_counts, v_eq_w, a_eq_w
transfer: proof_shape=bind-only; consumers=row_counts, v_eq_w
classCount: proof_shape=bind-only; consumers=row_counts, finite_certificate, v_eq_w
firstCount: proof_shape=bind-only; consumers=initial_counts, finite_certificate, a_eq_w
class_fibres: proof_shape=bind-only; consumers=row_counts
label_sum: proof_shape=bind-only; consumers=row_counts
valid_next: proof_shape=bind-only; consumers=v_eq_w
row_counts: proof_shape=bind-only; consumers=finite_certificate, v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_counts: proof_shape=bind-only; consumers=finite_certificate, a_eq_w
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, result
w: proof_shape=bind-only; consumers=v_eq_w, recurrence
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, closed_form
recurrence: proof_shape=bind-only; consumers=result, closed_form
zero_count: proof_shape=bind-only; consumers=result
one_count: proof_shape=bind-only; consumers=closed_form
two_count: proof_shape=bind-only; consumers=closed_form
closed_step: proof_shape=bind-only; consumers=closed_form
closed_form: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
Direct frozen dependencies (declaration statement_ids):
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthNormal
statement_id: sha256:544f7677e789967b28078e2cb7f71e075b79492f79f4741e37f835329362022b
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
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
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53fbbe70a660fd21867d6be8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
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

set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthNormal widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

abbrev Row := Fin 4 → Fin 6
abbrev Boundary := Fin 3 → Fin 3

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 3, c j.castSucc ≠ c j.succ ∧
    (c j.castSucc).val + (c j.succ).val ≠ 5

private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3, c j.succ ≠ d j.castSucc ∧
    (c j.succ).val + (d j.castSucc).val ≠ 5

private instance instDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → Row) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))

private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 4 → Fin 6) :
    Decidable (widthLegal rowLegal bonds A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

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

def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 2, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)

private instance instDecidableValid (s : Seen) (p : Boundary) :
    Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Boundary) : Fin 3 :=
  if s.2 then if p 0 = p 2 then 1 else 2 else 0

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

private theorem label_sum (g : (Fin 4 → Fin 3) → ℤ) :
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
    simp_rw [row_counts s p h]
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
  simp_rw [initial_counts]
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
