/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.finite_certificate
   digest: Hardin's order-ten recurrence for literal six-column diagonal strips. -/

/-
admission_basis: open-problem-resolution (#29162; Proved)
escape_witness: finite_certificate establishes the eleven-class diagonal transfer.
The all-height reduction consumes this witness. Distribution calculations only
instantiate the transfer and are consumed bind-only helpers.
labels: proof_shape=bind-only; consumers=bonds_iff, counting_bridge, row_valid, initial_valid, classCount, firstCount
Valid: proof_shape=bind-only; consumers=row_valid, initial_valid, valid_next, finite_certificate, v_eq_w
boundaryClass: proof_shape=bind-only; consumers=firstCount, classCount, finite_certificate, v_eq_w, a_eq_w
bonds: proof_shape=bind-only; consumers=decidableBonds, a, bonds_iff, counting_bridge
decidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, a_eq_w, shifted_count, result
compatible: proof_shape=bind-only; consumers=decidableCompatible, bonds_iff, v, valid_next, classCount
decidableCompatible: proof_shape=bind-only; consumers=v, classCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge, v_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
transfer: proof_shape=bind-only; consumers=finite_certificate, w, distribution_step
row_valid: proof_shape=bind-only; consumers=valid_next
valid_next: proof_shape=bind-only; consumers=v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
firstCount: proof_shape=bind-only; consumers=initial_fibres, initial_counts, a_eq_w
initial_fibres: proof_shape=bind-only; consumers=initial_counts
classCount: proof_shape=bind-only; consumers=class_fibres, finite_certificate, v_eq_w
class_fibres: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=content; consumers=v_eq_w
initial_counts: proof_shape=bind-only; consumers=a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, shifted_count
v_eq_w: proof_shape=content; consumers=a_eq_w
a_eq_w: proof_shape=content; consumers=shifted_count
distribution: proof_shape=bind-only; consumers=distribution_step, shifted_count, distribution_relation
distribution_step: proof_shape=bind-only; consumers=shifted_count
shifted_count: proof_shape=content; consumers=result
distribution_relation: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=terminal result (#29162)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Lean.Elab.Tactic.Omega

/-! Horizontal and both diagonal bonds constrain the literal row-major normalized arrays. -/
set_option maxRecDepth 100000
set_option Elab.async false
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip

open HardinA233175PairStrip (Seen good finish allowed advance finish_fst finish_snd good_iff)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233254TriangleStrip (Row rowLegal sum_rows)
open HardinA233255PairTransfer (Boundary)
open HardinA233255ShapeSymmetry (proper full_row)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

private def labels (c : Row) : Boundary := fun j => beta (c j)

private def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ proper p ∧ (s.2 = false → ∀ j, p j ≠ 2)

private def boundaryClass (s : Seen) (p : Boundary) : Fin 11 :=
  if s.2 then
    ![1, 2, 3, 4, 3, 5, 6, 7, 2, 8, 5, 9, 4, 9, 7, 10]
      ((if p 0 = p 2 then 8 else 0) + (if p 1 = p 3 then 4 else 0) +
      (if p 2 = p 4 then 2 else 0) + (if p 3 = p 5 then 1 else 0) : Fin 16)
  else 0

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 5,
    (c j.castSucc ≠ d j.succ ∧ (c j.castSucc).val + (d j.succ).val ≠ 5) ∧
    (c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5)

private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, (_ ∧ _) ∧ (_ ∧ _)))

/-- The literal filtered finite count, with the owner scanner and first-cell condition. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 6 → Fin 6 => widthLegal rowLegal bonds A)).card

private def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 5, p j.castSucc ≠ beta (c j.succ) ∧ p j.succ ≠ beta (c j.castSucc)

private instance decidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = widthTotal rowLegal labels (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

private def transfer (i k : Fin 11) : ℤ :=
  ![![64, 0, 0, 64, 64, 128, 32, 128, 32, 128, 64],
    ![0, 64, 128, 0, 0, 0, 0, 0, 64, 0, 0],
    ![0, 64, 128, 0, 64, 0, 0, 0, 64, 64, 0],
    ![0, 0, 0, 64, 64, 64, 64, 128, 0, 64, 64],
    ![0, 0, 64, 64, 64, 64, 64, 128, 64, 64, 64],
    ![0, 0, 0, 64, 64, 128, 64, 192, 0, 128, 128],
    ![0, 0, 0, 128, 128, 128, 64, 128, 0, 128, 64],
    ![0, 0, 0, 128, 128, 192, 64, 192, 0, 192, 128],
    ![0, 64, 128, 0, 128, 0, 0, 0, 64, 128, 64],
    ![0, 0, 64, 64, 64, 128, 64, 192, 64, 192, 128],
    ![0, 0, 0, 128, 128, 256, 64, 256, 64, 256, 192]] i k

private theorem row_valid (s : Seen) (c : Row) (hs : s.1 = true ∨ ∃ i, c i = 1)
    (hc : rowLegal c ∧ good s c) : Valid (finish s c) (labels c) := by
  refine ⟨(finish_fst s c).mpr hs, ?_, ?_⟩
  · intro j
    exact (colour_bond_iff _ _).mp (hc.1 j)
  · intro ht j hp
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((good_iff s c).mp hc.2 i).2 hi with hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    rcases (hb _).mp hp with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (labels c) := by
  intro s p hp c hc
  exact row_valid s c (Or.inl hp.1) ⟨hc.1, hc.2.2⟩

private theorem initial_valid (c : Row)
    (hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) :
    Valid (finish (false, false) c) (labels c) := by
  have ht : ∀ y : Fin 6, ((0 : Fin 6) ≠ y ∧ y.val ≠ 5) →
      allowed (advance (false, false) 0) y → y = 1 := by decide +kernel
  have hb : (0 : Fin 6) ≠ c 1 ∧ (c 1).val ≠ 5 := by
    have hh := hc.2.1 0
    change c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5 at hh
    simpa only [hc.1, Fin.val_zero, zero_add] using hh
  have hg : allowed (advance (false, false) 0) (c 1) := by
    have hh : allowed (advance (false, false) (c 0)) (c 1) := hc.2.2.2.1
    simpa only [hc.1] using hh
  exact row_valid (false, false) c (Or.inr ⟨1, ht _ hb hg⟩) hc.2

private def firstCount (k : Fin 11) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0

private def classCount (s : Seen) (p : Boundary) (k : Fin 11) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Boundary) (k : Fin 11) :
    classCount s p k = ∑ q : Boundary,
      rowWeight s q * if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
        (∀ j : Fin 5, p j.castSucc ≠ q j.succ ∧ p j.succ ≠ q j.castSucc) ∧
        boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 6 s (fun t q =>
    if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
      (∀ j : Fin 5, p j.castSucc ≠ q j.succ ∧ p j.succ ≠ q j.castSucc) ∧
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
-- The certificate enumerates the finite scanner states and all labelled rows.
private theorem finite_certificate : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  suffices h : ∀ k : Fin 11, ∀ s p, Valid s p →
      classCount s p k = transfer (boundaryClass s p) k by
    intro s p hp k
    exact h k s p hp
  intro k
  fin_cases k <;> rintro ⟨u, t⟩ <;> cases u <;> cases t <;>
    simp only [Valid, Bool.false_eq_true, Bool.true_eq_false, eq_self,
      false_and, true_and, and_true, false_implies, true_implies] <;>
    simp (config := { failIfUnchanged := false }) only
      [class_fibres, (full_row 6 _).1, (full_row 6 _).2,
      sum_rows, mul_ite, mul_one, mul_zero] <;>
    simp (config := { failIfUnchanged := false }) only
      [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi] <;>
    decide +kernel

private theorem initial_fibres (k : Fin 11) :
    firstCount k = ∑ q : Fin 5 → Fin 3, rowWeight (false, false) q *
      if proper (Fin.cons 0 q) ∧ boundaryClass (rowFinish (false, false) q) (Fin.cons 0 q) = k
      then 1 else 0 := by
  unfold firstCount
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 6)).sum_comp, Fintype.sum_prod_type]
  change (∑ x : Fin 6, ∑ c : Fin 5 → Fin 6,
    if x = 0 ∧ rowLegal (Fin.cons x c) ∧ good (false, false) (Fin.cons x c) ∧
      boundaryClass (finish (false, false) (Fin.cons x c)) (labels (Fin.cons x c)) = k
    then (1 : ℤ) else 0) = _
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · have h := scanner_fibres 5 (false, false) (fun t q =>
      if proper (Fin.cons 0 q) ∧ boundaryClass t (Fin.cons 0 q) = k then (1 : ℤ) else 0)
    rw [← h]
    apply Finset.sum_congr rfl
    intro c _
    have ha : allowed (false, false) (0 : Fin 6) := by decide +kernel
    have hd : advance (false, false) (0 : Fin 6) = (false, false) := by decide +kernel
    have hg : good (false, false) (Fin.cons (0 : Fin 6) c) ↔ good (false, false) c := by
      change (allowed (false, false) 0 ∧ good (advance (false, false) 0) c) ↔ _
      simp only [ha, hd, true_and]
    have hf : finish (false, false) (Fin.cons (0 : Fin 6) c) = finish (false, false) c := by
      change finish (advance (false, false) 0) c = _
      rw [hd]
    have hb : labels (Fin.cons (0 : Fin 6) c) = Fin.cons 0 (fun j => beta (c j)) :=
      Fin.comp_cons beta 0 c
    have hr : proper (labels (Fin.cons (0 : Fin 6) c)) ↔ rowLegal (Fin.cons 0 c) := by
      simp only [proper, labels, rowLegal, colour_bond_iff]
    simp only [← hb, hr, hg, hf, eq_self, true_and]
    by_cases hc : good (false, false) c <;> simp [hc]
  · intro x _ hx
    simp [hx]
  · simp

set_option maxHeartbeats 0 in
-- This exact finite sum retains the scanner multiplicities of every first row.
private theorem initial_counts : ∀ k,
    firstCount k = ![16, 8, 16, 16, 16, 16, 8, 16, 8, 16, 0] k := by
  simp only [initial_fibres, HardinA233126SquareStrip.label_sum]
  decide +kernel

private def w : ℕ → Fin 11 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 11, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 11, (if rowLegal c ∧ compatible p c ∧ good s c ∧
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
    change (∑ k : Fin 11, classCount s p k * w n k) = _
    simp_rw [finite_certificate s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 11, ![16, 8, 16, 16, 16, 16, 8, 16, 8, 16, 0] k * w n k := by
  rw [counting_bridge, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 11, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
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
  change (∑ k : Fin 11, firstCount k * w n k) = _
  simp_rw [initial_counts]

private def distribution (r : Fin 11) (k : Fin 11) : ℤ :=
  ![![16, 8, 16, 16, 16, 16, 8, 16, 8, 16, 0],
    ![1024, 2048, 6144, 8192, 10240, 12288, 6144, 16384, 4608, 15360, 10240],
    ![65536, 819200, 3276800, 7208960, 8192000, 11403264, 5079040, 14352384, 3145728, 13369344,
      9535488],
    ![4194304, 463470592, 2306867200, 6283067392, 6895435776, 10011803648, 4427087872,
      12582912000, 2455764992, 11479810048, 8355053568],
    ![268435456, 334470578176, 1844956889088, 5465882755072, 5927860174848, 8716367691776,
      3842385117184, 10935255171072, 2045343956992, 9913052954624, 7249904795648],
    ![17179869184, 270385371152384, 1554589182590976, 4741025419493376, 5120906686889984,
      7561169665523712, 3331253944188928, 9482652134408192, 1748206308294656, 8575486322016256,
      6282291613532160],
    ![1099511627776, 228683575170433024, 1333936302910865408, 4108224042115268608,
      4431488157262807040, 6551994187963695104, 2886066840063180800, 8215903825974788096,
      1507319940762304512, 7424089427720273920, 5441721639886651392],
    ![70368744177664, 196476148405990588416, 1151709262250898358272, 3558603617691066433536,
      3836912493494936797184, 5675431254231462445056, 2499807274927518646272,
      7116442186395433304064, 1303503333982025547776, 6428881853409430339584,
      4713103352492330057728],
    ![4503599627370496, 169708079656890527645696, 996426997515660552044544,
      3082146234676877069385728, 3322704054210633834430464, 4915551807117819813822464,
      2165067652340899207184384, 6163540877122741158805504, 1128357534670078961778688,
      5567558065269780120600576, 4081897435904891772993536],
    ![288230376151711744, 146847527157928322654011392, 862671829962603138430009344,
      2669374214177009583588900864, 2877575306455781966027423744, 4257242734229727936650412032,
      1875101832249308338618105856, 5338072184551335030297722880, 977065738846703077323440128,
      4821767542685766246807371776, 3535185234376796557157597184],
    ![18446744073709551616, 127141446141903010458077495296, 747040834628865106537581903872,
      2311851411212249341527851008000, 2492126822902233936284771942400,
      3687048398764803114598085427200, 1623956419127669814222296973312,
      4623109825807893401514828365824, 846151243496300447774445404160,
      4175916933186676749150678155264, 3061685613957189212204376784896]] r k

private theorem distribution_step : ∀ (r : Fin 10) (k : Fin 11),
    distribution r.succ k = ∑ i : Fin 11, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 11) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 11, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

private theorem distribution_relation : ∀ k : Fin 11,
    distribution 10 k = 1216 * distribution 9 k - 303104 * distribution 8 k - 6553600 *
      distribution 7 k + 6056574976 * distribution 6 k - 287762808832 * distribution 5 k -
      18622978195456 * distribution 4 k + 1482141674242048 * distribution 3 k - 15199648742375424
      * distribution 2 k - 522417556774977536 * distribution 1 k + 5764607523034234880 *
      distribution 0 k := by
  decide +kernel

/-- Hardin's recurrence at every height at least eleven. -/
theorem result (n : ℕ) :
    (a (n + 11) : ℤ) = 1216 * a (n + 10) - 303104 * a (n + 9) - 6553600 * a (n + 8) + 6056574976 *
      a (n + 7) - 287762808832 * a (n + 6) - 18622978195456 * a (n + 5) + 1482141674242048 * a (n
      + 4) - 15199648742375424 * a (n + 3) - 522417556774977536 * a (n + 2) + 5764607523034234880
      * a (n + 1) := by
  have h0 := shifted_count (0 : Fin 11) n
  have h1 := shifted_count (1 : Fin 11) n
  have h2 := shifted_count (2 : Fin 11) n
  have h3 := shifted_count (3 : Fin 11) n
  have h4 := shifted_count (4 : Fin 11) n
  have h5 := shifted_count (5 : Fin 11) n
  have h6 := shifted_count (6 : Fin 11) n
  have h7 := shifted_count (7 : Fin 11) n
  have h8 := shifted_count (8 : Fin 11) n
  have h9 := shifted_count (9 : Fin 11) n
  have h10 := shifted_count (10 : Fin 11) n
  change (a (n + 1) : ℤ) = _ at h0
  change (a (n + 2) : ℤ) = _ at h1
  change (a (n + 3) : ℤ) = _ at h2
  change (a (n + 4) : ℤ) = _ at h3
  change (a (n + 5) : ℤ) = _ at h4
  change (a (n + 6) : ℤ) = _ at h5
  change (a (n + 7) : ℤ) = _ at h6
  change (a (n + 8) : ℤ) = _ at h7
  change (a (n + 9) : ℤ) = _ at h8
  change (a (n + 10) : ℤ) = _ at h9
  change (a (n + 11) : ℤ) = _ at h10
  rw [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  simp only [distribution_relation, sub_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip
