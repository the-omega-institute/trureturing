/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's generating function for the literal six-colour complementary strip. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.RingTheory.PowerSeries.Inverse
import OmegaBuild.Commands

compile_only_with_mathlib

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen good finish)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
  (widthNormal widthLegal widthStep widthV widthTotal width_counting_bridge)
open D5.S3.Combinatorics.TraceAvoidingArrays

private abbrev Row := Fin 2 → Fin 6
private abbrev RowPair := Fin 6 × Fin 6
private abbrev State := Seen × RowPair

private def bond (a b : Fin 6) : Prop := a.val + b.val ≠ 5
private instance (a b : Fin 6) : Decidable (bond a b) :=
  inferInstanceAs (Decidable (_ ≠ (5 : ℕ)))

private def horizontal (c : Row) : Prop := bond (c 0) (c 1)

private def between (c d : Row) : Prop :=
  bond (c 0) (d 0) ∧ bond (c 1) (d 1) ∧ bond (c 1) (d 0)

private instance (c : Row) : Decidable (horizontal c) := inferInstanceAs (Decidable (bond _ _))
private instance (c d : Row) : Decidable (between c d) :=
  inferInstanceAs (Decidable (bond _ _ ∧ bond _ _ ∧ bond _ _))

private def Normal {n : ℕ} (A : Fin n × Fin 2 → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, 2 * q.1.val + q.2.val < 2 * p.1.val + p.2.val ∧ A q = 1) ∧
    (A p = 3 → ∃ q, 2 * q.1.val + q.2.val < 2 * p.1.val + p.2.val ∧ A q = 2)

/-- The literal bond, anchor and first-use predicate on the array. -/
def Legal {n : ℕ} (A : Fin n × Fin 2 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
  (∀ i, bond (A (i, 0)) (A (i, 1))) ∧
  (∀ (i : Fin n) (h : i.val + 1 < n),
    let j : Fin n := ⟨i.val + 1, h⟩
    bond (A (i, 0)) (A (j, 0)) ∧ bond (A (i, 1)) (A (j, 1)) ∧
      bond (A (i, 1)) (A (j, 0))) ∧
  Normal A

private instance {n : ℕ} (A : Fin n × Fin 2 → Fin 6) : Decidable (Normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _)))
instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 2 → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The cardinality of the literal arrays, with zero constant coefficient. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun A : Fin n × Fin 2 → Fin 6 => Legal A)).card

private theorem normal_iff {n : ℕ} (A : Fin n × Fin 2 → Fin 6) :
    widthNormal (false, false) (fun i j => A (i, j)) ↔ Normal A := by
  have earlier (i : Fin n) (j : Fin 2) (d : Fin 6) :
      (∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r, k) = d) ↔
      ∃ q, 2 * q.1.val + q.2.val < 2 * i.val + j.val ∧ A q = d := by
    constructor
    · rintro ⟨r, k, h, hc⟩
      refine ⟨(r, k), ?_, hc⟩
      change 2 * r.val + k.val < 2 * i.val + j.val
      rcases h with h | ⟨rfl, h⟩ <;> simp only [Fin.lt_def] at h <;> omega
    · rintro ⟨⟨r, k⟩, h, hc⟩
      change 2 * r.val + k.val < 2 * i.val + j.val at h
      refine ⟨r, k, ?_, hc⟩
      by_cases hr : r < i
      · exact Or.inl hr
      · simp only [Fin.lt_def] at hr
        exact Or.inr ⟨Fin.ext (by omega), by simp only [Fin.lt_def]; omega⟩
  change (∀ i j, (((A (i, j) = 2 ∨ A (i, j) = 3 ∨ A (i, j) = 4) →
    (false : Bool) = true ∨ ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r, k) = 1) ∧
    (A (i, j) = 3 → (false : Bool) = true ∨
      ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ A (r, k) = 2))) ↔ _
  simp only [Bool.false_eq_true, false_or, earlier, Normal, Prod.forall]

private abbrev v := widthV horizontal id between
private abbrev total := widthTotal horizontal (id : Row → Row)

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  have h : Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 6 => Legal A) =
      Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 6 =>
        widthLegal horizontal between A) := by
    ext A
    simp [widthLegal, Legal, horizontal, between, normal_iff]
  rw [a, h]
  exact width_counting_bridge horizontal id between between (fun _ _ => Iff.rfl) n

private abbrev rowEquiv := finTwoArrowEquiv (Fin 6)
private abbrev toRow : RowPair → Row := rowEquiv.symm

private def allowedNext (s : State) (r : RowPair) : Prop :=
  horizontal (toRow r) ∧ between (toRow s.2) (toRow r) ∧ good s.1 (toRow r)

private def allowedFirst (r : RowPair) : Prop :=
  toRow r 0 = 0 ∧ horizontal (toRow r) ∧ good (false, false) (toRow r)

private instance (s : State) (r : RowPair) : Decidable (allowedNext s r) :=
  inferInstanceAs (Decidable (horizontal _ ∧ between _ _ ∧ good _ _))
private instance (r : RowPair) : Decidable (allowedFirst r) :=
  inferInstanceAs (Decidable (_ ∧ horizontal _ ∧ good _ _))

private def T : Matrix State State ℤ := fun s t =>
  if allowedNext s t.2 ∧ finish s.1 (toRow t.2) = t.1 then 1 else 0

private def initial : State → ℤ := fun t =>
  if allowedFirst t.2 ∧ finish (false, false) (toRow t.2) = t.1 then 1 else 0

private theorem sum_flags (P : Prop) [Decidable P] (s : Seen) (f : Seen → ℤ) :
    (∑ t, (if P ∧ s = t then 1 else 0) * f t) = if P then f s else 0 := by
  by_cases h : P
  · simp [h, ite_mul]
  · simp [h]

private def rowStep (w : State → ℤ) (s : State) : ℤ :=
  ∑ r : RowPair, if allowedNext s r then w (finish s.1 (toRow r), r) else 0

private def rowTotal (w : State → ℤ) : ℤ :=
  ∑ r : RowPair, if allowedFirst r then w (finish (false, false) (toRow r), r) else 0

private theorem mulVec_eq_rowStep (w : State → ℤ) (s : State) :
    T.mulVec w s = rowStep w s := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [T, rowStep, sum_flags]

private theorem dot_eq_rowTotal (w : State → ℤ) : dotProduct initial w = rowTotal w := by
  rw [dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [initial, rowTotal, sum_flags]

private theorem continuation (n : ℕ) (s : State) :
    v n s.1 (toRow s.2) = (T ^ n).mulVec (1 : State → ℤ) s := by
  induction n generalizing s with
  | zero => simp [widthV, Matrix.one_mulVec]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, mulVec_eq_rowStep]
    let f (c : Row) : ℤ :=
      if horizontal c ∧ between (toRow s.2) c ∧ good s.1 c
        then v n (finish s.1 c) c else 0
    change (∑ c : Row, f c) = _
    rw [← rowEquiv.symm.sum_comp f]
    simp only [f, rowStep, allowedNext]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih (finish s.1 (toRow r), r)]
    rfl

private theorem matrix_count (n : ℕ) :
    (a (n + 1) : ℤ) = dotProduct initial ((T ^ n).mulVec (1 : State → ℤ)) := by
  rw [counting_bridge, dot_eq_rowTotal]
  let f (c : Row) : ℤ :=
    if c 0 = 0 ∧ horizontal c ∧ good (false, false) c
      then v n (finish (false, false) c) c else 0
  change (∑ c : Row, f c) = _
  rw [← rowEquiv.symm.sum_comp f]
  simp only [f, rowTotal, allowedFirst]
  apply Finset.sum_congr rfl
  intro r _
  rw [continuation n (finish (false, false) (toRow r), r)]
  rfl
-- Rows of this table are the continuation vectors for lengths 1 through 6.
-- Each vector is indexed by the two flags followed by the two row colours.
private def entries : Array (Array ℤ) := #[
  #[
    5, 6, 6, 5, 1, 3, 5, 8, 8, 7, 2, 5, 5, 8, 8, 7, 2, 5,
    5, 8, 8, 7, 2, 5, 2, 4, 4, 4, 2, 2, 3, 6, 6, 5, 1, 5,
    6, 7, 6, 6, 1, 4, 6, 9, 8, 8, 2, 6, 6, 9, 8, 8, 2, 6,
    6, 9, 8, 8, 2, 6, 2, 4, 4, 4, 2, 2, 4, 7, 6, 6, 1, 6,
    14, 11, 17, 9, 11, 10, 11, 14, 17, 9, 10, 11, 14, 14, 21, 12, 14, 14,
    10, 10, 16, 12, 10, 10, 11, 10, 17, 9, 14, 11, 10, 11, 17, 9, 11, 14,
    21, 17, 17, 17, 17, 16, 17, 21, 17, 17, 16, 17, 17, 17, 21, 16, 17, 17,
    17, 17, 16, 21, 17, 17, 17, 16, 17, 17, 21, 17, 16, 17, 17, 17, 17, 21],
  #[
    58, 69, 69, 52, 5, 42, 58, 85, 85, 68, 10, 58, 58, 85, 85, 68, 10, 58,
    58, 85, 85, 68, 10, 58, 16, 32, 32, 32, 10, 16, 42, 69, 69, 52, 5, 58,
    95, 112, 95, 95, 6, 72, 95, 135, 118, 118, 12, 95, 95, 135, 118, 118, 12, 95,
    95, 135, 118, 118, 12, 95, 23, 46, 46, 46, 12, 23, 72, 112, 95, 95, 6, 95,
    209, 167, 248, 108, 167, 156, 167, 209, 248, 108, 156, 167, 209, 209, 301, 144, 209, 209,
    137, 137, 212, 144, 137, 137, 167, 156, 248, 108, 209, 167, 156, 167, 248, 108, 167, 209,
    377, 305, 305, 305, 305, 288, 305, 377, 305, 305, 288, 305, 305, 305, 377, 288, 305, 305,
    305, 305, 288, 377, 305, 305, 305, 288, 305, 305, 377, 305, 288, 305, 305, 305, 305, 377],
  #[
    906, 1073, 1073, 768, 58, 681, 906, 1298, 1298, 993, 116, 906, 906, 1298, 1298, 993, 116, 906,
    906, 1298, 1298, 993, 116, 906, 225, 450, 450, 450, 116, 225, 681, 1073, 1073, 768, 58, 906,
    1692, 1997, 1692, 1692, 95, 1292, 1692, 2397, 2092, 2092, 190, 1692, 1692, 2397, 2092, 2092, 190, 1692,
    1692, 2397, 2092, 2092, 190, 1692, 400, 800, 800, 800, 190, 400, 1292, 1997, 1692, 1692, 95, 1692,
    3502, 2821, 4141, 1629, 2821, 2654, 2821, 3502, 4141, 1629, 2654, 2821, 3502, 3502, 4989, 2172, 3502, 3502,
    2210, 2210, 3392, 2172, 2210, 2210, 2821, 2654, 4141, 1629, 3502, 2821, 2654, 2821, 4141, 1629, 2821, 3502,
    6765, 5473, 5473, 5473, 5473, 5168, 5473, 6765, 5473, 5473, 5168, 5473, 5473, 5473, 6765, 5168, 5473, 5473,
    5473, 5473, 5168, 6765, 5473, 5473, 5473, 5168, 5473, 5473, 6765, 5473, 5168, 5473, 5473, 5473, 5473, 6765],
  #[
    15523, 18344, 18344, 12871, 906, 11796, 15523, 22071, 22071, 16598, 1812, 15523, 15523, 22071, 22071, 16598, 1812, 15523,
    15523, 22071, 22071, 16598, 1812, 15523, 3727, 7454, 7454, 7454, 1812, 3727, 11796, 18344, 18344, 12871, 906, 15523,
    30349, 35822, 30349, 30349, 1692, 23184, 30349, 42987, 37514, 37514, 3384, 30349, 30349, 42987, 37514, 37514, 3384, 30349,
    30349, 42987, 37514, 37514, 3384, 30349, 7165, 14330, 14330, 14330, 3384, 7165, 23184, 35822, 30349, 30349, 1692, 30349,
    61393, 49597, 72508, 27432, 49597, 46776, 49597, 61393, 72508, 27432, 46776, 49597, 61393, 61393, 87125, 36576, 61393, 61393,
    38209, 38209, 58468, 36576, 38209, 38209, 49597, 46776, 72508, 27432, 61393, 49597, 46776, 49597, 72508, 27432, 49597, 61393,
    121393, 98209, 98209, 98209, 98209, 92736, 98209, 121393, 98209, 98209, 92736, 98209, 98209, 98209, 121393, 92736, 98209, 98209,
    98209, 98209, 92736, 121393, 98209, 98209, 98209, 92736, 98209, 98209, 121393, 98209, 92736, 98209, 98209, 98209, 98209, 121393],
  #[
    274319, 323916, 323916, 225707, 15523, 209199, 274319, 389036, 389036, 290827, 31046, 274319, 274319, 389036, 389036, 290827, 31046, 274319,
    274319, 389036, 389036, 290827, 31046, 274319, 65120, 130240, 130240, 130240, 31046, 65120, 209199, 323916, 323916, 225707, 15523, 274319,
    544578, 642787, 544578, 544578, 30349, 416020, 544578, 771345, 673136, 673136, 60698, 544578, 544578, 771345, 673136, 673136, 60698, 544578,
    544578, 771345, 673136, 673136, 60698, 544578, 128558, 257116, 257116, 257116, 60698, 128558, 416020, 642787, 544578, 544578, 30349, 544578,
    1093214, 884015, 1290617, 481761, 884015, 834418, 884015, 1093214, 1290617, 481761, 834418, 884015, 1093214, 1093214, 1549413, 642348, 1093214, 1093214,
    677194, 677194, 1035184, 642348, 677194, 677194, 884015, 834418, 1290617, 481761, 1093214, 884015, 834418, 884015, 1290617, 481761, 884015, 1093214,
    2178309, 1762289, 1762289, 1762289, 1762289, 1664080, 1762289, 2178309, 1762289, 1762289, 1664080, 1762289, 1762289, 1762289, 2178309, 1664080, 1762289, 1762289,
    1762289, 1762289, 1664080, 2178309, 1762289, 1762289, 1762289, 1664080, 1762289, 1762289, 2178309, 1762289, 1664080, 1762289, 1762289, 1762289, 1762289, 2178309],
  #[
    4897852, 5781867, 5781867, 4019578, 274319, 3739518, 4897852, 6940201, 6940201, 5177912, 548638, 4897852, 4897852, 6940201, 6940201, 5177912, 548638, 4897852,
    4897852, 6940201, 6940201, 5177912, 548638, 4897852, 1158334, 2316668, 2316668, 2316668, 548638, 1158334, 3739518, 5781867, 5781867, 4019578, 274319, 4897852,
    9772043, 11534332, 9772043, 9772043, 544578, 7465176, 9772043, 13841199, 12078910, 12078910, 1089156, 9772043, 9772043, 13841199, 12078910, 12078910, 1089156, 9772043,
    9772043, 13841199, 12078910, 12078910, 1089156, 9772043, 2306867, 4613734, 4613734, 4613734, 1089156, 2306867, 7465176, 11534332, 9772043, 9772043, 544578, 9772043,
    19567745, 15828227, 23098064, 8583732, 15828227, 14944212, 15828227, 19567745, 23098064, 8583732, 14944212, 15828227, 19567745, 19567745, 27721597, 11444976, 19567745, 19567745,
    12102569, 12102569, 18494132, 11444976, 12102569, 12102569, 15828227, 14944212, 23098064, 8583732, 19567745, 15828227, 14944212, 15828227, 23098064, 8583732, 15828227, 19567745,
    39088169, 31622993, 31622993, 31622993, 31622993, 29860704, 31622993, 39088169, 31622993, 31622993, 29860704, 31622993, 31622993, 31622993, 39088169, 29860704, 31622993, 31622993,
    31622993, 31622993, 29860704, 39088169, 31622993, 31622993, 31622993, 29860704, 31622993, 31622993, 39088169, 31622993, 29860704, 31622993, 31622993, 31622993, 31622993, 39088169],
]

private def stateIndex (s : State) : ℕ :=
  36 * (2 * s.1.1.toNat + s.1.2.toNat) + 6 * s.2.1.val + s.2.2.val

private def W (k : Fin 7) (s : State) : ℤ :=
  if k.val = 0 then 1 else (entries.getD (k.val - 1) #[]).getD (stateIndex s) 0

private theorem table_zero : W 0 = (1 : State → ℤ) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem table_steps : ∀ k : Fin 6, W k.succ = T.mulVec (W k.castSucc) := by
  have step : ∀ (k : Fin 6) (s : State),
      W k.succ s = rowStep (W k.castSucc) s := by
    intro k
    fin_cases k <;> decide +kernel
  intro k
  funext s
  rw [mulVec_eq_rowStep]
  exact step k s

private theorem powers (k : Fin 7) : (T ^ k.val).mulVec (1 : State → ℤ) = W k :=
  TransferMatrix.tabulatedPowers T 6 W table_zero table_steps k

private def coefficients : Fin 5 → ℤ := ![1, -25, 134, -134, 25]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem table_relation : ∀ s : State,
    W 6 s = ∑ j : Fin 5, coefficients j * W ⟨1 + j.val, by omega⟩ s := by
  decide +kernel

-- The degree-five relation holds after one continuation step on the full state space.
private theorem power_relation :
    (T ^ (1 + 5)).mulVec (1 : State → ℤ) =
      ∑ j : Fin 5, coefficients j • (T ^ (1 + j.val)).mulVec (1 : State → ℤ) := by
  have h (j : Fin 5) : (T ^ (1 + j.val)).mulVec (1 : State → ℤ) =
      W ⟨1 + j.val, by omega⟩ := powers ⟨1 + j.val, by omega⟩
  rw [show (1 + 5 : ℕ) = (6 : Fin 7).val from rfl, powers]
  simp_rw [h]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact table_relation s

private def firstValues : Fin 6 → ℤ := ![2, 16, 225, 3727, 65120, 1158334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem table_initials : ∀ k : Fin 6, rowTotal (W k.castSucc) = firstValues k := by
  decide +kernel

private theorem initial_count (k : Fin 6) : (a (k.val + 1) : ℤ) = firstValues k := by
  rw [matrix_count, dot_eq_rowTotal]
  change rowTotal ((T ^ k.castSucc.val).mulVec (1 : State → ℤ)) = _
  rw [powers]
  exact table_initials k

private theorem zero_count : a 0 = 0 := by simp [a, Legal]

private theorem initial_counts :
    a 1 = 2 ∧ a 2 = 16 ∧ a 3 = 225 ∧ a 4 = 3727 ∧ a 5 = 65120 ∧ a 6 = 1158334 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (a 1 : ℤ) = 2 := initial_count 0
    exact_mod_cast h
  · have h : (a 2 : ℤ) = 16 := initial_count 1
    exact_mod_cast h
  · have h : (a 3 : ℤ) = 225 := initial_count 2
    exact_mod_cast h
  · have h : (a 4 : ℤ) = 3727 := initial_count 3
    exact_mod_cast h
  · have h : (a 5 : ℤ) = 65120 := initial_count 4
    exact_mod_cast h
  · have h : (a 6 : ℤ) = 1158334 := initial_count 5
    exact_mod_cast h

private theorem sum_coefficients (f : Fin 5 → ℤ) :
    (∑ j : Fin 5, coefficients j * f j) =
      f 0 - 25 * f 1 + 134 * f 2 - 134 * f 3 + 25 * f 4 := by
  norm_num [coefficients, Fin.sum_univ_succ]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 6) : ℤ) =
      25 * a (n + 5) - 134 * a (n + 4) + 134 * a (n + 3) - 25 * a (n + 2) + a (n + 1) := by
  cases n with
  | zero =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := initial_counts
    norm_num [h1, h2, h3, h4, h5, h6]
  | succ n =>
    let f (k : ℕ) := dotProduct initial ((T ^ k).mulVec (1 : State → ℤ))
    have hf (k : ℕ) : f k = (a (k + 1) : ℤ) := (matrix_count k).symm
    have h := TransferMatrix.scalarRelationShift T initial 5 1 coefficients power_relation n
    change f (n + 6) = ∑ j : Fin 5, coefficients j * f (n + 1 + j.val) at h
    rw [sum_coefficients] at h
    change f (n + 6) =
      f (n + 1) - 25 * f (n + 2) + 134 * f (n + 3) - 134 * f (n + 4) + 25 * f (n + 5) at h
    norm_num only [hf, Nat.add_assoc, Nat.reduceAdd] at h ⊢
    omega

open PowerSeries in
private theorem product_identity :
    (1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℚ)) =
    X * (2 - 34 * X + 93 * X ^ 2 - 22 * X ^ 3 + X ^ 4) := by
  let F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have denominator :
      (1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2) * F =
      F - 25 * (F * X ^ 1) + 134 * (F * X ^ 2) - 134 * (F * X ^ 3) +
        25 * (F * X ^ 4) - F * X ^ 5 := by ring
  have numerator : (X * (2 - 34 * X + 93 * X ^ 2 - 22 * X ^ 3 + X ^ 4) : PowerSeries ℚ) =
      2 * X - 34 * X ^ 2 + 93 * X ^ 3 - 22 * X ^ 4 + X ^ 5 := by ring
  change (1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2) * F = _
  rw [denominator, numerator]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow, F,
    coeff_mk]
  by_cases hn : 6 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_left (show 5 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega),
      ite_eq_right (show n ≠ 4 by omega), ite_eq_right (show n ≠ 5 by omega)]
    have h : (a (n - 6 + 6) : ℚ) =
        25 * a (n - 6 + 5) - 134 * a (n - 6 + 4) + 134 * a (n - 6 + 3) -
          25 * a (n - 6 + 2) + a (n - 6 + 1) := by
      exact_mod_cast recurrence (n - 6)
    rw [show n - 6 + 6 = n by omega, show n - 6 + 5 = n - 1 by omega,
      show n - 6 + 4 = n - 2 by omega, show n - 6 + 3 = n - 3 by omega,
      show n - 6 + 2 = n - 4 by omega, show n - 6 + 1 = n - 5 by omega] at h
    linarith
  · obtain ⟨h1, h2, h3, h4, h5, _⟩ := initial_counts
    interval_cases n <;> norm_num [zero_count, h1, h2, h3, h4, h5]

open PowerSeries in
/-- Colin Barker's generating function for OEIS A233141, revision 8. -/
theorem result :
    (PowerSeries.mk fun n =>
      ((Finset.univ.filter (fun A : Fin n × Fin 2 → Fin 6 => Legal A)).card : ℚ)) =
      X * (2 - 34 * X + 93 * X ^ 2 - 22 * X ^ 3 + X ^ 4) *
        ((1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2))⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff ((1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2) :
      PowerSeries ℚ) ≠ 0)).2
  rw [mul_comm]
  exact product_identity

end D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141
