/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/ZeroTemperature
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/ZeroTemperature
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The saturated signed certificate on four-colour boundaries. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229750.result)
legal_iff: proof_shape=bind-only; consumers=transition_counts
class_correspondence: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=Certificate.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres

/-! The proper zero-defect block is the signed saturated block divided by 8. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
  (Boundary rowLegal pairs compatible saturated proper kind rate step saturated_certificate)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
  (beta good allowed advance finish widthStep colour_bond_iff)

private theorem legal_iff (p : Boundary) (c : Fin 3 → Fin 8) :
    (rowLegal c ∧ compatible p c ∧ good saturated c) ↔
      bondDefects between p (pairs c) + bondDefects horizontal (pairs c) (pairs c) = 0 := by
  simp only [bondDefects, Nat.add_eq_zero_iff, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, between, horizontal,
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
