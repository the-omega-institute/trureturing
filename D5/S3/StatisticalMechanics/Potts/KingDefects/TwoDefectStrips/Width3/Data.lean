/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data
   mirror-E: none(waiver:exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data.structural_certificate
   digest: Width-3 exact-budget transfer data and its zero-budget certificate. -/


/-
admission_basis: escape-witness
escape_witness: Forward.structural_certificate computes the initial weights from all width-three boundary rows and verifies the table step and annihilation relation used in the two recurrences.
ZeroTemperature.legal_iff: proof_shape=bind-only; consumers=transition_counts
ZeroTemperature.class_correspondence: proof_shape=bind-only; consumers=transition_counts
ZeroTemperature.transition_counts: proof_shape=bind-only; consumers=Certificate.transition_counts
Forward.structural_certificate: proof_shape=content; consumers=HardinA229750.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
set_option maxRecDepth 100000
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip (Boundary)
abbrev horizontal : Finset (Fin 3 × Fin 3) :=
  D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip.horizontal
def between : Finset (Fin 3 × Fin 3) :=
  D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip.between
def Valid (p : Boundary) (d : ℕ) : Prop := d ≤ 2 ∧ bondDefects horizontal p p ≤ 2-d
instance (p : Boundary) (d : ℕ) : Decidable (Valid p d) := inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 9 :=
  if p 1 = p 0 then (if p 2 = p 0 then ((![6, 0, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![8, 4, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)) else (if p 2 = p 0 then ((![7, 3, 2] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 2 = p 1 then ((![8, 4, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![5, 0, 1] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))
def T : Matrix (Fin 9) (Fin 9) ℤ :=
  ![![1, 0, 0, 0, 0, 7, 0, 5, 2], ![7, 1, 0, 5, 2, 13, 1, 5, 8], ![10, 0, 2, 2, 4, 10, 2, 6, 8], ![0, 0, 0, 2, 0, 10, 0, 2, 4], ![2, 0, 0, 2, 0, 8, 0, 4, 6], (fun s => if s = 5 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip.rate false / 8 else 0), ![0, 0, 0, 0, 0, 6, 0, 6, 0], (fun s => if s = 7 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip.rate true / 8 else 0), ![0, 0, 0, 0, 0, 2, 0, 2, 0]]
def initial : Fin 9 → ℤ := ![0, 24, 12, 0, 24, 0, 4, 0, 0]
def terminal : Fin 9 → ℤ :=
  D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip.terminal
def W : Fin 9 → Fin 9 → ℤ :=
  ![![0, 24, 12, 0, 24, 0, 4, 0, 0], ![336, 24, 24, 192, 96, 648, 48, 312, 432], ![936, 24, 48, 744, 144, 7392, 72, 4488, 2400], ![1872, 24, 96, 1992, 240, 28560, 120, 21360, 6288], ![3480, 24, 192, 4776, 432, 78072, 216, 71016, 14112], ![6432, 24, 384, 10920, 816, 185400, 408, 201504, 30384], ![12072, 24, 768, 24360, 1584, 413520, 792, 525912, 64704], ![23088, 24, 1536, 53544, 3120, 896448, 1560, 1306128, 137424], ![44856, 24, 3072, 116520, 6192, 1918344, 3096, 3140808, 291552]]
def classList : Fin 9 → List (Fin 9) :=
  ![[0, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 8, 8], [0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8], [3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 8, 8, 8, 8], [0, 0, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8], [], [5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7], [], [5, 5, 7, 7]]
def successors (p : Boundary) (d : ℕ) : List (Fin 9) :=
  ((List.ofFn (fun i : Fin (4^3) => finFunctionFinEquiv.symm i)).filterMap
    (fun r => let a := bondDefects between p r + bondDefects horizontal r r
      if a ≤ d then some (cl r (d-a)) else none)).insertionSort (· ≤ ·)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data

/- The proper zero-defect block is the signed saturated block divided by 8. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
  (Boundary rowLegal pairs compatible saturated proper kind rate step saturated_certificate)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (good allowed advance widthStep colour_bond_iff)

private theorem legal_iff (p : Boundary) (c : Fin 3 → Fin 8) :
    (rowLegal c ∧ compatible p c ∧ good saturated c) ↔
      bondDefects between p (pairs c) + bondDefects horizontal (pairs c) (pairs c) = 0 := by
  simp only [bondDefects, Nat.add_eq_zero_iff, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, between,
    D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip.between, horizontal,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Prod.fst, Prod.snd]
  simp [rowLegal, compatible, colour_bond_iff, good, saturated, allowed, advance,
    pairs, Fin.forall_fin_succ, and_assoc, ne_comm]
  <;> tauto

set_option maxRecDepth 100000 in
private theorem class_correspondence : ∀ p : Boundary, proper p →
    cl p 0 = (if kind p then 7 else 5 : Fin 9) := by
  decide +kernel

theorem transition_counts (p : Boundary) (hp : proper p) (s : Fin 9) :
    (∑ r : Boundary, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  classical
  let w : Boundary → ℤ := fun r =>
    if bondDefects between p r + bondDefects horizontal r r = 0 ∧ cl r 0 = s
    then 1 else 0
  have hf := SignedFibres.sum_beta w
  have hs := saturated_certificate p hp
  have he : (∑ c : Fin 3 → Fin 8, w (pairs c)) =
      if cl p 0 = s then rate (kind p) else 0 := by
    calc
      _ = ∑ c : Fin 3 → Fin 8,
          if cl p 0 = s then
            (if rowLegal c ∧ compatible p c ∧ good saturated c then (1 : ℤ) else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : rowLegal c ∧ compatible p c ∧ good saturated c
        · have hclass : cl (pairs c) 0 = cl p 0 := by
            rw [class_correspondence _ (hs.1 c hc).2.1,
              class_correspondence _ hp, (hs.1 c hc).2.2]
          simp only [w, (legal_iff p c).mp hc, hclass, hc, ite_true, true_and]
        · have hn := mt (legal_iff p c).mpr hc
          simp only [w, hn, hc, ite_false, false_and, ite_self]
      _ = _ := by
        split_ifs with h
        · simpa only [ite_true, step, widthStep] using hs.2
        · simp only [ite_false, Finset.sum_const_zero]
  have heq : (8 : ℤ) * (∑ r : Boundary, w r) =
      if cl p 0 = s then rate (kind p) else 0 := by
    simpa only [show (2 : ℤ)^3 = 8 from rfl] using hf.symm.trans he
  have hT : (8 : ℤ) * T (cl p 0) s =
      if cl p 0 = s then rate (kind p) else 0 := by
    rw [class_correspondence _ hp]
    cases hk : kind p <;> simp [T, rate, hk, eq_comm]
  have hsum : (∑ r : Boundary, w r) = T (cl p 0) s := by linarith
  simpa only [w, Nat.le_zero, Nat.zero_sub] using hsum

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.ZeroTemperature

/- Acceptance, initial weights and the forward polynomial relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Forward
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip (Boundary)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ s : Fin 9, (∑ r : Boundary, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 8, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 8 = ∑ j : Fin 6, (![-8, 36, -66, 63, -33, 9] j : ℤ) • W ⟨2+j.val, by omega⟩ := by
  decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Forward
