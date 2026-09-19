/- GID: D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Generic/Certificate
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Produce accepted full Lebesgue translation-energy certificates for arbitrary rational polynomials and positive requested widths. -/

import D5.S3.Weil.Separator.TranslationEnergy.Generic.CellCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.Generic

open _root_.Polynomial
open D5.S3.Weil.Separator.TranslationEnergy
open D5.S3.Weil.Separator.TranslationEnergy.Polynomial
open D5.S3.Weil.Separator.TranslationEnergy.LiteralFunction
open scoped BigOperators

def budgetDepth (C eta : Rat) : Nat := Nat.log 2 (Nat.ceil (2 * C / eta)) + 1

def meshDepth (R : Nat) (s : Rat) (pcs qcs : List Rat) (eta : Rat) : Nat :=
  budgetDepth (linearBudget R s pcs qcs * hullLength R s ^ 2) eta

def cutoffDepth (R : Nat) (s : Rat) (pcs qcs : List Rat) (eta : Rat) : Nat :=
  budgetDepth (scalarBudget R s pcs qcs * hullLength R s) eta

def certificatePayloads (R : Nat) (s : Rat) (pcs qcs : List Rat) (w : Nat) :
    List CanonicalCellPayload :=
  genericPayloads R s (meshDepth R s pcs qcs ((1 / 2 : Rat) ^ w))
    (cutoffDepth R s pcs qcs ((1 / 2 : Rat) ^ w)) pcs qcs

def requestedDepth (eta : Rat) : Nat := budgetDepth 1 (2 * eta)

def producedBounds (R : Nat) (s : Rat) (pcs qcs : List Rat) (eta : Rat) : Rat × Rat :=
  let w := requestedDepth eta
  aggregateBounds R s (meshDepth R s pcs qcs ((1 / 2 : Rat) ^ w))
    (certificatePayloads R s pcs qcs w)

def certificateCorrect (R : Nat) (hR : 0 < R) (p q : Rat[X])
    (s eta : Rat) (pcs qcs : List Rat) : Prop :=
  let w := requestedDepth eta
  let delta := (1 / 2 : Rat) ^ w
  let d := meshDepth R s pcs qcs delta
  let m := cutoffDepth R s pcs qcs delta
  let box := producedBounds R s pcs qcs eta
  coefficientPolynomial pcs = p ∧ coefficientPolynomial qcs = q ∧
  checkFull R (normalizeCoefficients pcs) (normalizeCoefficients qcs)
    s d m (4 * m + 4) w (certificatePayloads R s pcs qcs w) = true ∧
  (box.1 : Real) ≤ D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.translationEnergy
    (LiteralFunction.literalRationalTest R hR p q) s ∧
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.translationEnergy
    (LiteralFunction.literalRationalTest R hR p q) s ≤ (box.2 : Real) ∧
  box.2 - box.1 < eta


theorem full_certificate (R : Nat) (hR : 0 < R) (s eta : Rat) (heta : 0 < eta) :
    (∀ pcs qcs : List Rat,
      certificateCorrect R hR (coefficientPolynomial pcs) (coefficientPolynomial qcs)
        s eta pcs qcs) ∧
    (∀ p q : Rat[X], ∃ pcs qcs : List Rat,
      certificateCorrect R hR p q s eta pcs qcs) := by
  have cellAt_strict (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) : a < b := by
    have hi : i < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      simp [cellAt, hnone] at hcell
    have hj : i + 1 < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      rw [cellAt, List.getElem?_eq_getElem hi, hnone] at hcell
      simp at hcell
    rw [cellAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hcell
    change some ((canonicalPoints R s d)[i], (canonicalPoints R s d)[i + 1]) =
      some (a, b) at hcell
    injection hcell with hpair
    injection hpair with ha hb
    subst a
    subst b
    exact (Finset.sortedLT_sort (canonicalPointSet R s d)).getElem_lt_getElem_of_lt (by omega)
  have depth (C e : Rat) (he : 0 < e) :
      C / (2 : Rat) ^ budgetDepth C e < e / 2 := by
    have hc : 2 * C / e ≤ (Nat.ceil (2 * C / e) : Rat) := Nat.le_ceil _
    have hp : (Nat.ceil (2 * C / e) : Rat) <
        (2 : Rat) ^ budgetDepth C e := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : Nat))
        (Nat.ceil (2 * C / e))
    have hpow : (0 : Rat) < 2 ^ budgetDepth C e := by positivity
    apply (div_lt_iff₀ hpow).mpr
    have h := (div_lt_iff₀ he).mp (hc.trans_lt hp)
    nlinarith
  have hall (pcs qcs : List Rat) :
      certificateCorrect R hR (coefficientPolynomial pcs) (coefficientPolynomial qcs)
        s eta pcs qcs := by
    let w := requestedDepth eta
    let delta : Rat := (1 / 2 : Rat) ^ w
    let d := meshDepth R s pcs qcs delta
    let m := cutoffDepth R s pcs qcs delta
    let ps := certificatePayloads R s pcs qcs w
    let L := hullLength R s
    let Cl := linearBudget R s pcs qcs
    let Ce := scalarBudget R s pcs qcs
    have hHull : supportHullUpper R s - supportHullLower R s = L := by
      dsimp [supportHullUpper, supportHullLower, L, hullLength]
      by_cases hs : 0 ≤ s
      · rw [abs_of_nonneg hs, max_eq_right (by linarith),
          min_eq_left (by linarith)]
        ring
      · have hs' : s ≤ 0 := le_of_not_ge hs
        rw [abs_of_nonpos hs', max_eq_left (by linarith),
          min_eq_right (by linarith)]
        ring
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have htol : delta < eta := by
      have ht := depth 1 (2 * eta) (by positivity)
      simpa [delta, w, requestedDepth, div_pow] using ht
    have hcount : ps.length + 1 = (canonicalPoints R s d).length := by
      change (genericPayloads R s d m pcs qcs).length + 1 = _
      simpa only [genericPayloads, List.length_map] using sourceCells_length_add_one R s d
    have hlen : ps.length = (sourceCells R s d).length := by
      change (genericPayloads R s d m pcs qcs).length = _
      exact List.length_map _
    have hidx (i : Nat) (hi : i < ps.length) (a b : Rat)
        (hc : cellAt R s d i = some (a, b)) :
        ps.getD i defaultPayload = genericCanonicalCellPayload R a b s m pcs qcs := by
      have hj : i + 1 < (canonicalPoints R s d).length := by omega
      dsimp [ps, certificatePayloads]
      rw [genericPayloads, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [sourceCells_index R s d i hj, hc]
      rfl
    have hcell (i : Nat) (hi : i < ps.length) :
        ∃ a b, cellAt R s d i = some (a, b) := by
      have hj : i + 1 < (canonicalPoints R s d).length := by omega
      exact ⟨_, _, (show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hj,
          show i < (canonicalPoints R s d).length by omega])⟩
    have hchecks : (List.range ps.length).all (fun i =>
        checkCanonicalCell R (normalizeCoefficients pcs) (normalizeCoefficients qcs)
          s d i m (4 * m + 4) (ps.getD i defaultPayload)) = true := by
      rw [List.all_eq_true]
      intro i hi
      have hi := List.mem_range.mp hi
      obtain ⟨a, b, hc⟩ := hcell i hi
      rw [hidx i hi a b hc]
      exact (cell_certificate R hR s d i m a b hc pcs qcs).1
    have hCl : 0 ≤ Cl := by
      have hB : 0 ≤ coordinateBudget R s := by dsimp [coordinateBudget]; positivity
      have sl (cs : List Rat) : 0 ≤ slope (coordinateBudget R s) cs := by
        induction cs with
        | nil => simp [D5.S3.Weil.Separator.TranslationEnergy.Polynomial.slope]
        | cons c cs ih =>
          simp only [D5.S3.Weil.Separator.TranslationEnergy.Polynomial.slope]
          exact add_nonneg (amplitude_nonneg _ hB cs) (mul_nonneg hB ih)
      dsimp [Cl, linearBudget]
      have hp := amplitude_nonneg (coordinateBudget R s) hB
        (evenizedCoefficients (normalizeCoefficients pcs))
      have hq := amplitude_nonneg (coordinateBudget R s) hB
        (evenizedCoefficients (normalizeCoefficients qcs))
      have hsp := sl (evenizedCoefficients (normalizeCoefficients pcs))
      have hsq := sl (evenizedCoefficients (normalizeCoefficients qcs))
      positivity
    have hsum : (aggregateBounds R s d ps).2 - (aggregateBounds R s d ps).1 =
        ∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i *
          ((ps.getD i defaultPayload).norm.total.2 -
            (ps.getD i defaultPayload).norm.total.1) := by
      simp only [aggregateBounds, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨a, b, hc⟩ := hcell i (Finset.mem_range.mp hi)
      simp only [hc, canonicalCellLength]
      ring
    have hbound : (aggregateBounds R s d ps).2 - (aggregateBounds R s d ps).1 ≤
        Cl * ((L / ((2 ^ d : Nat) : Rat)) * L) +
          Ce * (1 / 2 : Rat) ^ m * L := by
      rw [hsum]
      calc
        _ ≤ Cl * (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i ^ 2) +
            Ce * (1 / 2 : Rat) ^ m *
              (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro i hi
          have hi := Finset.mem_range.mp hi
          obtain ⟨a, b, hc⟩ := hcell i hi
          have hw := (cell_certificate R hR s d i m a b hc pcs qcs).2
          rw [hidx i hi a b hc]
          simp only [canonicalCellLength, hc]
          have hm := mul_le_mul_of_nonneg_left hw
            (sub_nonneg.mpr ((cellAt_strict R s d i a b hc).le))
          dsimp [Cl, Ce]
          linear_combination hm
        _ ≤ _ := by
          rw [hlen, sum_canonicalCellLength_eq_hull, hHull]
          have hg := sum_canonicalCellLength_sq_le R s d hR
          rw [hHull] at hg
          exact add_le_add (mul_le_mul_of_nonneg_left
            hg hCl) le_rfl
    have hd := depth (Cl * L ^ 2) delta hdelta
    have hm := depth (Ce * L) delta hdelta
    have hwidth : (aggregateBounds R s d ps).2 - (aggregateBounds R s d ps).1 ≤ delta := by
      have hmesh : Cl * ((L / ((2 ^ d : Nat) : Rat)) * L) =
          Cl * L ^ 2 / (2 : Rat) ^ d := by push_cast; ring
      have hscalar : Ce * (1 / 2 : Rat) ^ m * L = Ce * L / (2 : Rat) ^ m := by
        rw [div_pow]; ring
      change Cl * L ^ 2 / (2 : Rat) ^ d < delta / 2 at hd
      change Ce * L / (2 : Rat) ^ m < delta / 2 at hm
      rw [hmesh, hscalar] at hbound
      linarith
    have hcheck : checkFull R (normalizeCoefficients pcs) (normalizeCoefficients qcs)
        s d m (4 * m + 4) w ps = true := by
      apply decide_eq_true
      refine ⟨hR, hcount, canonicalPoints_first R s d, ?_, hchecks, hwidth⟩
      have hl : ps.length = (canonicalPoints R s d).length - 1 := by omega
      rw [hl]
      exact canonicalPoints_last R s d
    have fidelity (cs : List Rat) :
        coefficientPolynomial (normalizeCoefficients cs) = coefficientPolynomial cs := by
      unfold normalizeCoefficients
      split_ifs with h
      · subst cs; simp [coefficientPolynomial]
      · rfl
    have hs := checked_literal_translation_energy_sound R
      (coefficientPolynomial pcs) (coefficientPolynomial qcs) s
      (normalizeCoefficients pcs) (normalizeCoefficients qcs)
      (fidelity pcs) (fidelity qcs) d m (4 * m + 4) w ps hcheck
      (literalRationalTest R hR (coefficientPolynomial pcs) (coefficientPolynomial qcs))
      (by intro x; rfl)
    exact ⟨rfl, rfl, hcheck, hs.1, hs.2.1, hwidth.trans_lt htol⟩
  refine ⟨hall, ?_⟩
  intro p q
  obtain ⟨pcs, hp⟩ := coefficientPolynomial_surjective p
  obtain ⟨qcs, hq⟩ := coefficientPolynomial_surjective q
  exact ⟨pcs, qcs, by simpa only [hp, hq] using hall pcs qcs⟩

#print axioms full_certificate
#print axioms certificatePayloads
#print axioms requestedDepth

end D5.S3.Weil.Separator.TranslationEnergy.Generic
