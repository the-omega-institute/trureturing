/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The saturated signed certificate on four-colour boundaries. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229751.result)
legal_iff: proof_shape=bind-only; consumers=transition_counts
class_correspondence: proof_shape=bind-only; consumers=transition_counts
proper_transition_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=Certificate.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229582Strip

/-! The proper zero-defect block is the signed saturated block divided by 16. -/
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
  simp [rowLegal, compatible, colour_bond_iff, good, saturated, allowed, advance,
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
      Finset.filter_eq_empty_iff, between, horizontal, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq, Prod.fst, Prod.snd]
    simp [q, hpat.2.1, hpat.2.2]
    <;> tauto
  simpa only [hz, Nat.zero_sub, hcl] using proper_transition_counts q hq s

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.ZeroTemperature
