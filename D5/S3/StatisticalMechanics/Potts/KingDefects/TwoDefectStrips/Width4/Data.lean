/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data
   mirror-E: none(waiver:exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data.transition_counts
   digest: Width-4 exact-budget transfer data and its zero-budget certificate. -/


/-
admission_basis: escape-witness
escape_witness: ZeroTemperature.transition_counts constructs the proper comparison row for the improper class-14 case and proves exact agreement of the zero-defect successor predicates.
between: proof_shape=bind-only; consumers=successors
ZeroTemperature.legal_iff: proof_shape=bind-only; consumers=proper_transition_counts
ZeroTemperature.class_correspondence: proof_shape=bind-only; consumers=transition_counts
ZeroTemperature.proper_transition_counts: proof_shape=bind-only; consumers=transition_counts
ZeroTemperature.transition_counts: proof_shape=content; consumers=Certificate.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
set_option maxRecDepth 100000
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip (Boundary)
abbrev horizontal : Finset (Fin 4 × Fin 4) :=
  D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip.horizontal
def between : Finset (Fin 4 × Fin 4) :=
  D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData.between
def Valid (p : Boundary) (d : ℕ) : Prop := d ≤ 2 ∧ bondDefects horizontal p p ≤ 2-d
instance (p : Boundary) (d : ℕ) : Decidable (Valid p d) := inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 19 :=
  if p 1 = p 0 then (if p 2 = p 0 then (if p 3 = p 0 then ((![0, 0, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![17, 0, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)) else (if p 3 = p 0 then ((![16, 10, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 3 = p 2 then ((![18, 0, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![13, 7, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))) else (if p 2 = p 0 then (if p 3 = p 0 then ((![16, 10, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 3 = p 1 then ((![14, 6, 8] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![12, 1, 5] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 2 = p 1 then (if p 3 = p 0 then ((![14, 6, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 3 = p 1 then ((![17, 0, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 9, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 3 = p 0 then ((![2, 11, 3] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 3 = p 1 then ((![12, 1, 5] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 3 = p 2 then ((![13, 7, 0] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![12, 0, 4] : Fin 3 → Fin 19) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))))))
def T : Matrix (Fin 19) (Fin 19) ℤ :=
  ![![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 2, 0, 0, 0, 0, 0], ![0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 3, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 6, 14, 0, 0, 0, 2, 0, 0, 1, 0, 0, 26, 6, 7, 2, 6, 2, 0], ![2, 6, 8, 0, 1, 0, 0, 2, 0, 0, 0, 2, 28, 10, 7, 4, 2, 0, 1], ![3, 5, 9, 0, 0, 1, 3, 1, 0, 1, 1, 3, 30, 11, 6, 3, 5, 2, 1], ![0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 12, 0, 2, 0, 4, 0, 0], ![1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 2, 3, 2, 1, 0, 0], ![0, 12, 10, 0, 0, 0, 2, 0, 2, 0, 4, 4, 26, 12, 4, 8, 4, 4, 2], ![0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 4, 4, 1, 2, 0, 0], ![0, 2, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 12, 2, 4, 2, 4, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 2, 1, 0, 0, 0], (fun s => if s = 12 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip.rate false / 16 else 0), ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], (fun s => if s = 14 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip.rate true / 16 else 0), ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 0, 0, 0, 0]]
def initial : Fin 19 → ℤ := ![0, 0, 0, 24, 24, 48, 12, 48, 12, 24, 24, 0, 0, 0, 0, 0, 0, 24, 12]
def terminal : Fin 19 → ℤ := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 12 → Fin 19 → ℤ :=
  ![![0, 0, 0, 24, 24, 48, 12, 48, 12, 24, 24, 0, 0, 0, 0, 0, 0, 24, 12], ![288, 816, 1512, 0, 24, 48, 288, 96, 24, 72, 96, 264, 4656, 1296, 1104, 552, 720, 192, 96], ![576, 1920, 6984, 0, 24, 48, 960, 96, 48, 48, 144, 360, 31680, 3120, 9288, 1968, 2976, 192, 120], ![864, 3360, 15456, 0, 24, 48, 2448, 96, 96, 48, 240, 432, 90768, 5088, 35256, 3432, 7008, 288, 168], ![1152, 5568, 29016, 0, 24, 48, 5712, 96, 192, 48, 432, 624, 200112, 7872, 103560, 5520, 14976, 480, 264], ![1440, 9312, 53856, 0, 24, 48, 12816, 96, 384, 48, 816, 1008, 401952, 12192, 271368, 9072, 31392, 864, 456], ![1728, 16128, 102624, 0, 24, 48, 28176, 96, 768, 48, 1584, 1776, 785232, 19584, 669480, 15504, 65856, 1632, 840], ![2016, 29088, 201504, 0, 24, 48, 61200, 96, 1536, 48, 3120, 3312, 1536960, 33120, 1594248, 27696, 138720, 3168, 1608], ![2304, 54336, 405216, 0, 24, 48, 131856, 96, 3072, 48, 6192, 6384, 3049584, 58944, 3711336, 51408, 292992, 6240, 3144], ![2592, 104160, 827808, 0, 24, 48, 282384, 96, 6144, 48, 12336, 12528, 6144864, 109344, 8504904, 98160, 619296, 12384, 6216], ![2880, 203136, 1706592, 0, 24, 48, 601872, 96, 12288, 48, 24624, 24816, 12540048, 208896, 19262760, 190992, 1308096, 24672, 12360], ![3168, 400416, 3534624, 0, 24, 48, 1277712, 96, 24576, 48, 49200, 49392, 25817088, 406752, 43227144, 375984, 2758752, 49248, 24648]]
def classList : Fin 19 → List (Fin 19) :=
  ![[0, 2, 2, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13], [1, 2, 2, 2, 12, 12, 12, 12, 12, 12, 12, 12, 13, 14, 14, 14, 15, 16], [], [0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 6, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 15, 15, 16, 16, 16, 16, 16, 16, 17, 17], [0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 7, 7, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 18], [0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 6, 6, 6, 7, 9, 10, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 16, 16, 16, 16, 16, 17, 17, 18], [2, 2, 2, 2, 6, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 14, 14, 16, 16, 16, 16], [0, 1, 2, 2, 2, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 14, 14, 14, 15, 15, 16], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 6, 8, 8, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18], [1, 1, 2, 2, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 16, 16], [1, 1, 2, 2, 2, 2, 2, 2, 6, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 14, 14, 14, 14, 15, 15, 16, 16, 16, 16], [12, 12, 12, 12, 12, 12, 12, 12, 14, 14, 15], [], [12, 12], [], [2, 12, 12], [12, 12, 14, 14], [2, 2, 12, 12, 12, 12, 14, 14], [12, 12, 12, 12, 12, 12, 14, 14]]
def successors (p : Boundary) (d : ℕ) : List (Fin 19) :=
  ((List.ofFn (fun i : Fin (4^4) => finFunctionFinEquiv.symm i)).filterMap
    (fun r => let a := bondDefects between p r + bondDefects horizontal r r
      if a ≤ d then some (cl r (d-a)) else none)).insertionSort (· ≤ ·)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data

/- The proper zero-defect block is the signed saturated block divided by 16. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
  (Boundary rowLegal pairs compatible saturated proper kind rate step saturated_certificate)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (good allowed advance widthStep colour_bond_iff)

private theorem legal_iff (p : Boundary) (c : Fin 4 → Fin 8) :
    (rowLegal c ∧ compatible p c ∧ good saturated c) ↔
      bondDefects between p (pairs c) + bondDefects horizontal (pairs c) (pairs c) = 0 := by
  simp only [bondDefects, Nat.add_eq_zero_iff, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, between, horizontal,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Prod.fst, Prod.snd]
  simp [D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData.between,
    rowLegal, compatible, colour_bond_iff, good, saturated, allowed, advance,
    pairs, D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip.horizontal,
    Fin.forall_fin_succ, and_assoc, ne_comm]
  <;> tauto

set_option maxRecDepth 100000 in
private theorem class_correspondence : ∀ p : Boundary, proper p →
    cl p 0 = (if kind p then 14 else 12 : Fin 19) := by
  decide +kernel

private theorem proper_transition_counts (p : Boundary) (hp : proper p) (s : Fin 19) :
    (∑ r : Boundary, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  classical
  let w : Boundary → ℤ := fun r =>
    if bondDefects between p r + bondDefects horizontal r r = 0 ∧ cl r 0 = s
    then 1 else 0
  have hf := SignedFibres.sum_beta w
  have hs := saturated_certificate p hp
  have he : (∑ c : Fin 4 → Fin 8, w (pairs c)) =
      if cl p 0 = s then rate (kind p) else 0 := by
    calc
      _ = ∑ c : Fin 4 → Fin 8,
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
  have heq : (16 : ℤ) * (∑ r : Boundary, w r) =
      if cl p 0 = s then rate (kind p) else 0 := by
    simpa only [show (2 : ℤ)^4 = 16 from rfl] using hf.symm.trans he
  have hT : (16 : ℤ) * T (cl p 0) s =
      if cl p 0 = s then rate (kind p) else 0 := by
    rw [class_correspondence _ hp]
    cases hk : kind p <;> simp [T, rate, hk, eq_comm]
  have hsum : (∑ r : Boundary, w r) = T (cl p 0) s := by linarith
  simpa only [w, Nat.le_zero, Nat.zero_sub] using hsum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem transition_counts (p : Boundary) (hp : proper p ∨ cl p 0 = 14) (s : Fin 19) :
    (∑ r : Boundary, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  classical
  by_cases hpr : proper p
  · exact proper_transition_counts p hpr s
  have h14 : cl p 0 = 14 := hp.resolve_left hpr
  have hpat : p 0 ≠ p 1 ∧ p 2 = p 1 ∧ p 3 = p 0 := by
    have h : ∀ p : Boundary, cl p 0 = 14 → ¬ proper p →
        p 0 ≠ p 1 ∧ p 2 = p 1 ∧ p 3 = p 0 := by decide +kernel
    exact h p h14 hpr
  let q : Boundary := ![p 0, p 1, p 0, p 1]
  have hq : proper q := by
    simp [proper, q, Fin.forall_fin_succ, hpat.1, Ne.symm hpat.1]
  have hcl : cl q 0 = cl p 0 := by
    rw [h14, class_correspondence q hq]
    simp [kind, q]
  have hz (r : Boundary) :
      bondDefects between q r + bondDefects horizontal r r ≤ 0 ↔
        bondDefects between p r + bondDefects horizontal r r ≤ 0 := by
    simp only [Nat.le_zero, Nat.add_eq_zero_iff, bondDefects, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, between, horizontal]
    simp [D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData.between,
      D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip.horizontal,
      Fin.forall_fin_succ, q, hpat.2.1, hpat.2.2]
    simp only [and_assoc, and_left_comm, and_comm]
    repeat' intro
    simp_all
  simpa only [hz, Nat.zero_sub, hcl] using proper_transition_counts q hq s

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.ZeroTemperature
