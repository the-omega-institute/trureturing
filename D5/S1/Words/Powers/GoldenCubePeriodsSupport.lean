/- GID: D5/S1/Words/Powers/GoldenCubePeriodsSupport
   generality: I
   mirror-B: none(waiver:formal-kernel-cube-period-necessity)
   mirror-E: none(waiver:kernel-small-cases-in-formal-module)
   anchors: []
   digest: Internal Zeckendorf and rotation support for golden cube periods. -/

import D5.S1.Words.Powers.GoldenFourthPower
import D5.S1.Words.ReturnWords.GoldenArcFirstReturn
import D5.S0.Conventions.WDigits
import Mathlib.Data.List.PeriodicityLemma

namespace D5.S1.Words.Powers

open D5.S0.Conventions
open D5.S1.Words

noncomputable section

local instance : IsTrans Nat (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private def conjugateError (n : Nat) : Real :=
  ((wdigits n).map fun q => Real.goldenConj ^ q).sum

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem pow_add_pow_succ {r : Real} (hr : r ^ 2 + r = 1) {q : Nat}
    (hq : 1 ≤ q) : r ^ q + r ^ (q + 1) = r ^ (q - 1) := by
  conv_lhs =>
    lhs
    rw [show q = q - 1 + 1 by omega, pow_succ]
  conv_lhs =>
    rhs
    rw [show q + 1 = (q - 1) + 2 by omega, pow_add]
  calc
    r ^ (q - 1) * r + r ^ (q - 1) * r ^ 2 =
        r ^ (q - 1) * (r ^ 2 + r) := by ring
    _ = r ^ (q - 1) := by rw [hr, mul_one]

private theorem canonical_pairwise {l : List Nat} (hl : l.IsZeckendorfRep) :
    l.Pairwise fun x y => y + 2 ≤ x := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  exact (List.pairwise_append.mp hl).1

private theorem canonical_two_le {l : List Nat} (hl : l.IsZeckendorfRep) :
    ∀ q ∈ l, 2 ≤ q := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  intro q hq
  exact (List.pairwise_append.mp hl).2.2 q hq 0 (by simp)

private theorem sum_powers_le_sub_head {r : Real} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d q : Nat} {l : List Nat}
    (hpair : (q :: l).Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ q :: l, d + 1 ≤ k) :
    ((q :: l).map fun k => r ^ k).sum ≤ r ^ d - r ^ (q + 1) := by
  induction l generalizing q with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by have := hmin q (by simp); omega)]
      rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
      have := hmin q (by simp)
      omega
  | cons k l ih =>
      rw [List.pairwise_cons] at hpair
      have hkq : k + 2 ≤ q := hpair.1 k (by simp)
      have htail : (k :: l).Pairwise fun x y => y + 2 ≤ x := hpair.2
      have hmin_tail : ∀ m ∈ k :: l, d + 1 ≤ m := by
        intro m hm
        exact hmin m (by simp [hm])
      have hih := ih htail hmin_tail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ q + (r ^ k + (l.map fun m => r ^ m).sum) ≤
            r ^ q + (r ^ d - r ^ (k + 1)) := by
              gcongr
              simpa only [List.map_cons, List.sum_cons] using hih
        _ ≤ r ^ d - r ^ (q + 1) := by
          have hpowers : r ^ q + r ^ (q + 1) ≤ r ^ (k + 1) := by
            rw [pow_add_pow_succ hr (by omega)]
            rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
            omega
          linarith

private theorem sum_powers_lt {r : Real} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d : Nat} {l : List Nat}
    (hpair : l.Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ q ∈ l, d + 1 ≤ q) :
    (l.map fun q => r ^ q).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons q l =>
      refine (sum_powers_le_sub_head hr0 hr1 hr hpair hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (q + 1))

private theorem abs_sum_le_sum_abs : ∀ l : List Real, |l.sum| ≤ (l.map abs).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans (add_le_add le_rfl (abs_sum_le_sum_abs xs))

private theorem abs_conjugate_tail_lt {q : Nat} {l : List Nat}
    (hpair : l.Pairwise fun x y => y + 2 ≤ x) (hmin : ∀ k ∈ l, q + 2 ≤ k) :
    |(l.map fun k => Real.goldenConj ^ k).sum| < Real.goldenRatio⁻¹ ^ (q + 1) := by
  let r : Real := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hbound : (l.map fun k => r ^ k).sum < r ^ (q + 1) :=
    sum_powers_lt hr0 hr1 inv_golden_sq_add_inv_golden hpair hmin
  have hterm : ∀ k ∈ l, |Real.goldenConj ^ k| = r ^ k := by
    intro k _
    dsimp [r]
    rw [Real.inv_goldenRatio]
    rw [abs_pow, abs_of_neg Real.goldenConj_neg]
  calc
    |(l.map fun k => Real.goldenConj ^ k).sum| ≤
        ((l.map fun k => Real.goldenConj ^ k).map abs).sum := by
      exact abs_sum_le_sum_abs _
    _ = (l.map fun k => r ^ k).sum := by
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro k hk
      exact hterm k hk
    _ < r ^ (q + 1) := hbound

private theorem fib_mul_inv_golden {q : Nat} (hq : 2 ≤ q) :
    (Nat.fib q : Real) * Real.goldenRatio⁻¹ =
      (Nat.fib (q - 1) : Real) - Real.goldenConj ^ q := by
  have h := Real.goldenConj_mul_fib_succ_add_fib (q - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q)] at h
  rw [Real.inv_goldenRatio]
  linarith

private def shiftedFibValue (n : Nat) : Nat :=
  ((wdigits n).map fun q => Nat.fib (q - 1)).sum

private theorem sum_fib_mul_inv_golden {l : List Nat} (hmin : ∀ q ∈ l, 2 ≤ q) :
    (l.map fun q => (Nat.fib q : Real) * Real.goldenRatio⁻¹).sum =
      (l.map fun q => (Nat.fib (q - 1) : Real)).sum -
        (l.map fun q => Real.goldenConj ^ q).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
      have hq : 2 ≤ q := hmin q (by simp)
      have hl : ∀ k ∈ l, 2 ≤ k := by
        intro k hk
        exact hmin k (by simp [hk])
      simp only [List.map_cons, List.sum_cons]
      rw [fib_mul_inv_golden hq, ih hl]
      ring

private theorem conjugate_error_decomposition (n : Nat) :
    (n : Real) * Real.goldenRatio⁻¹ =
      (shiftedFibValue n : Real) - conjugateError n := by
  have hcanonical := wdigits_isCanonical n
  have hmin := canonical_two_le hcanonical
  have hterms :
      ((wdigits n).map fun q => (Nat.fib q : Real) * Real.goldenRatio⁻¹).sum =
        ((wdigits n).map fun q => (Nat.fib (q - 1) : Real)).sum - conjugateError n := by
    exact sum_fib_mul_inv_golden hmin
  have hdecode : (n : Real) = ((wdigits n).map fun q => (Nat.fib q : Real)).sum := by
    have hcast : (((wdigits n).map Nat.fib).sum : Real) =
        ((wdigits n).map fun q => (Nat.fib q : Real)).sum := by
      induction wdigits n with
      | nil => simp
      | cons q l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    rw [← hcast]
    exact_mod_cast (decode_wdigits n).symm
  have hmul :
      ((wdigits n).map fun q => (Nat.fib q : Real)).sum * Real.goldenRatio⁻¹ =
        ((wdigits n).map fun q => (Nat.fib q : Real) * Real.goldenRatio⁻¹).sum := by
    induction wdigits n with
    | nil => simp
    | cons q l ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]
  have hshift : (shiftedFibValue n : Real) =
      ((wdigits n).map fun q => (Nat.fib (q - 1) : Real)).sum := by
    unfold shiftedFibValue
    induction wdigits n with
    | nil => simp
    | cons q l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
  rw [hdecode, hmul, hterms, hshift]

private theorem abs_conjugate_error_lt_one (n : Nat) : |conjugateError n| < 1 := by
  have hpair := canonical_pairwise (wdigits_isCanonical n)
  have hmin := canonical_two_le (wdigits_isCanonical n)
  have hbound := abs_conjugate_tail_lt (q := 0) hpair (by simpa using hmin)
  have hinv : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hbound' : |conjugateError n| < Real.goldenRatio⁻¹ := by
    simpa [conjugateError] using hbound
  exact hbound'.trans hinv

private theorem abs_conjugate_error_lt_inv (n : Nat) :
    |conjugateError n| < Real.goldenRatio⁻¹ := by
  have hpair := canonical_pairwise (wdigits_isCanonical n)
  have hmin := canonical_two_le (wdigits_isCanonical n)
  have hbound := abs_conjugate_tail_lt (q := 0) hpair (by simpa using hmin)
  simpa [conjugateError] using hbound

private theorem forward_displacement_eq_of_error_neg {n : Nat}
    (herr : conjugateError n < 0) :
    GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n =
      -conjugateError n := by
  rw [GoldenArcFirstReturnInternal.forwardDisplacement, goldenMechanicalSlope,
    conjugate_error_decomposition, Int.fract_eq_iff]
  refine ⟨by linarith, ?_, ?_⟩
  · have hbound := abs_conjugate_error_lt_one n
    rw [abs_of_neg herr] at hbound
    exact hbound
  · exact ⟨shiftedFibValue n, by push_cast; ring⟩

private theorem backward_displacement_eq_of_error_pos {n : Nat} (hn : 0 < n)
    (herr : 0 < conjugateError n) :
    GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope n =
      conjugateError n := by
  rw [GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
    golden_mechanical_slope_irrational hn]
  have hfract :
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n =
        1 - conjugateError n := by
    rw [GoldenArcFirstReturnInternal.forwardDisplacement, goldenMechanicalSlope,
      conjugate_error_decomposition, Int.fract_eq_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hbound := abs_conjugate_error_lt_one n
      rw [abs_of_pos herr] at hbound
      linarith
    · linarith
    · let z : Int := shiftedFibValue n - 1
      refine ⟨z, ?_⟩
      dsimp [z]
      push_cast
      ring
  rw [hfract]
  ring

private theorem wdigits_fib_singleton {q : Nat} (hq : 2 ≤ q) :
    wdigits (Nat.fib q) = [q] := by
  symm
  apply wdigits_unique
  · simp [List.IsZeckendorfRep]
    omega
  · simp

private theorem conjugate_error_fib {q : Nat} (hq : 2 ≤ q) :
    conjugateError (Nat.fib q) = Real.goldenConj ^ q := by
  simp [conjugateError, wdigits_fib_singleton hq]

private theorem fib_candidate_lt_of_nonsingle {n q : Nat} {pre : List Nat}
    (hpre : pre ≠ []) (hdigits : wdigits n = pre ++ [q]) :
    Nat.fib (q + 2) < n := by
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil pre hpre
  have hpair := canonical_pairwise (wdigits_isCanonical n)
  rw [hdigits, List.pairwise_append] at hpair
  have hq : 2 ≤ q := by
    have hmin := canonical_two_le (wdigits_isCanonical n)
    exact hmin q (by rw [hdigits]; simp)
  have hkq : q + 2 ≤ k := hpair.2.2 k hk q (by simp)
  have hdecode := decode_wdigits n
  rw [hdigits, List.map_append, List.sum_append] at hdecode
  simp only [List.map_singleton, List.sum_singleton] at hdecode
  have hkfib : Nat.fib k ≤ (pre.map Nat.fib).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hqpos : 0 < Nat.fib q := Nat.fib_pos.mpr (by omega)
  have hcand : Nat.fib (q + 2) ≤ Nat.fib k := Nat.fib_mono hkq
  omega

private theorem fib_candidate_one_lt_of_nonsingle {n q : Nat} {pre : List Nat}
    (hq : 2 ≤ q) (hpre : pre ≠ []) (hdigits : wdigits n = pre ++ [q]) :
    Nat.fib (q + 1) < n := by
  have hnext : Nat.fib (q + 1) < Nat.fib (q + 2) := Nat.fib_lt_fib_succ (by omega)
  exact hnext.trans (fib_candidate_lt_of_nonsingle hpre hdigits)

private theorem pow_sub_pow_succ (q : Nat) :
    Real.goldenRatio⁻¹ ^ q - Real.goldenRatio⁻¹ ^ (q + 1) =
      Real.goldenRatio⁻¹ ^ (q + 2) := by
  have hr := inv_golden_sq_add_inv_golden
  calc
    Real.goldenRatio⁻¹ ^ q - Real.goldenRatio⁻¹ ^ (q + 1) =
        Real.goldenRatio⁻¹ ^ q * (1 - Real.goldenRatio⁻¹) := by ring
    _ = Real.goldenRatio⁻¹ ^ q * Real.goldenRatio⁻¹ ^ 2 := by
      congr 1
      linarith
    _ = Real.goldenRatio⁻¹ ^ (q + 2) := by rw [← pow_add]

private theorem forward_displacement_fib_odd {q : Nat} (hq : 2 ≤ q) (hodd : Odd q) :
    GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope (Nat.fib q) =
      Real.goldenRatio⁻¹ ^ q := by
  have herr : conjugateError (Nat.fib q) < 0 := by
    rw [conjugate_error_fib hq, show Real.goldenConj = -(-Real.goldenConj) by ring,
      hodd.neg_pow]
    exact neg_lt_zero.mpr (pow_pos (neg_pos.mpr Real.goldenConj_neg) q)
  calc
    GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope (Nat.fib q) =
        -conjugateError (Nat.fib q) := forward_displacement_eq_of_error_neg herr
    _ = Real.goldenRatio⁻¹ ^ q := by
      rw [conjugate_error_fib hq, Real.inv_goldenRatio, hodd.neg_pow]

private theorem backward_displacement_fib_even {q : Nat} (hq : 2 ≤ q) (heven : Even q) :
    GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope (Nat.fib q) =
      Real.goldenRatio⁻¹ ^ q := by
  have herr : 0 < conjugateError (Nat.fib q) := by
    rw [conjugate_error_fib hq, show Real.goldenConj = -(-Real.goldenConj) by ring,
      heven.neg_pow]
    exact pow_pos (neg_pos.mpr Real.goldenConj_neg) q
  calc
    GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope (Nat.fib q) =
        conjugateError (Nat.fib q) :=
      backward_displacement_eq_of_error_pos (Nat.fib_pos.mpr (by omega)) herr
    _ = Real.goldenRatio⁻¹ ^ q := by
      rw [conjugate_error_fib hq, Real.inv_goldenRatio, heven.neg_pow]

private theorem forward_record_is_fib {n : Nat} (hn : 0 < n)
    (hrecord : ∀ k, 0 < k → k < n →
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n <
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k) :
    ∃ q, 2 ≤ q ∧ n = Nat.fib q := by
  have hne : wdigits n ≠ [] := by
    intro hnil
    have hdecode := decode_wdigits n
    rw [hnil] at hdecode
    simp at hdecode
    omega
  obtain ⟨pre, q, hdigits⟩ := (wdigits n).eq_nil_or_concat.resolve_left hne
  rw [List.concat_eq_append] at hdigits
  have hq : 2 ≤ q := by
    have hmin := canonical_two_le (wdigits_isCanonical n)
    exact hmin q (by rw [hdigits]; simp)
  by_cases hpre : pre = []
  · subst pre
    rw [List.nil_append] at hdigits
    exact ⟨q, hq, by rw [← decode_wdigits n, hdigits]; simp⟩
  have hpair := canonical_pairwise (wdigits_isCanonical n)
  rw [hdigits, List.pairwise_append] at hpair
  have hprePair := hpair.1
  have hpreMin : ∀ k ∈ pre, q + 2 ≤ k := by
    intro k hk
    exact hpair.2.2 k hk q (by simp)
  have htail := abs_conjugate_tail_lt (q := q) hprePair hpreMin
  have herror : conjugateError n =
      (pre.map fun k => Real.goldenConj ^ k).sum + Real.goldenConj ^ q := by
    simp [conjugateError, hdigits]
  rcases Nat.even_or_odd q with heven | hodd
  · have herrpos : 0 < conjugateError n := by
      rw [Real.inv_goldenRatio] at htail
      rw [herror]
      have hqpow : Real.goldenConj ^ q = (-Real.goldenConj) ^ q := by
        exact (heven.neg_pow Real.goldenConj).symm
      have hlower := (abs_lt.mp htail).1
      have hpowers := pow_sub_pow_succ q
      rw [Real.inv_goldenRatio] at hpowers
      have hpos : 0 < (-Real.goldenConj) ^ (q + 2) :=
        pow_pos (neg_pos.mpr Real.goldenConj_neg) _
      rw [hqpow]
      linarith
    have hcand := fib_candidate_one_lt_of_nonsingle hq hpre hdigits
    have hcandpos : 0 < Nat.fib (q + 1) := Nat.fib_pos.mpr (by omega)
    have hsmall :
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope
            (Nat.fib (q + 1)) <
          GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n := by
      have htarget := GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
        golden_mechanical_slope_irrational hn
      have htargetBack := backward_displacement_eq_of_error_pos hn herrpos
      have hcandExact := forward_displacement_fib_odd (q := q + 1) (by omega) heven.add_one
      have herrBound := abs_conjugate_error_lt_inv n
      rw [abs_of_pos herrpos] at herrBound
      have hforward :
          GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n =
            1 - conjugateError n := by
        linarith [htarget, htargetBack]
      rw [hcandExact, hforward]
      have hr := inv_golden_sq_add_inv_golden
      have hpow : Real.goldenRatio⁻¹ ^ (q + 1) < Real.goldenRatio⁻¹ ^ 2 := by
        rw [pow_lt_pow_iff_right_of_lt_one₀ (inv_pos.mpr Real.goldenRatio_pos)
          (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)]
        omega
      linarith
    exact (lt_asymm (hrecord _ hcandpos hcand) hsmall).elim
  · have herrneg : conjugateError n < 0 := by
      rw [Real.inv_goldenRatio] at htail
      rw [herror]
      have hqpow : Real.goldenConj ^ q = -(-Real.goldenConj) ^ q := by
        rw [hodd.neg_pow]
        ring
      have hupper := (abs_lt.mp htail).2
      have hpowers := pow_sub_pow_succ q
      rw [Real.inv_goldenRatio] at hpowers
      have hpos : 0 < (-Real.goldenConj) ^ (q + 2) :=
        pow_pos (neg_pos.mpr Real.goldenConj_neg) _
      rw [hqpow]
      linarith
    have hcand := fib_candidate_lt_of_nonsingle hpre hdigits
    have hcandpos : 0 < Nat.fib (q + 2) := Nat.fib_pos.mpr (by omega)
    have hoddTwo : Odd (q + 2) := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩
    have hcandExact := forward_displacement_fib_odd (q := q + 2) (by omega) hoddTwo
    have htarget := forward_displacement_eq_of_error_neg herrneg
    have hupper := (abs_lt.mp htail).2
    have hpowers := pow_sub_pow_succ q
    have hqpow : Real.goldenConj ^ q = -Real.goldenRatio⁻¹ ^ q := by
      rw [Real.inv_goldenRatio, hodd.neg_pow]
      ring
    have hsmall :
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope
            (Nat.fib (q + 2)) <
          GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope n := by
      rw [hcandExact, htarget, herror, hqpow]
      linarith
    exact (lt_asymm (hrecord _ hcandpos hcand) hsmall).elim

private theorem backward_record_is_fib {n : Nat} (hn : 0 < n)
    (hrecord : ∀ k, 0 < k → k < n →
      GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope n <
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope k) :
    ∃ q, 2 ≤ q ∧ n = Nat.fib q := by
  have hne : wdigits n ≠ [] := by
    intro hnil
    have hdecode := decode_wdigits n
    rw [hnil] at hdecode
    simp at hdecode
    omega
  obtain ⟨pre, q, hdigits⟩ := (wdigits n).eq_nil_or_concat.resolve_left hne
  rw [List.concat_eq_append] at hdigits
  have hq : 2 ≤ q := by
    have hmin := canonical_two_le (wdigits_isCanonical n)
    exact hmin q (by rw [hdigits]; simp)
  by_cases hpre : pre = []
  · subst pre
    rw [List.nil_append] at hdigits
    exact ⟨q, hq, by rw [← decode_wdigits n, hdigits]; simp⟩
  have hpair := canonical_pairwise (wdigits_isCanonical n)
  rw [hdigits, List.pairwise_append] at hpair
  have hprePair := hpair.1
  have hpreMin : ∀ k ∈ pre, q + 2 ≤ k := by
    intro k hk
    exact hpair.2.2 k hk q (by simp)
  have htail := abs_conjugate_tail_lt (q := q) hprePair hpreMin
  have herror : conjugateError n =
      (pre.map fun k => Real.goldenConj ^ k).sum + Real.goldenConj ^ q := by
    simp [conjugateError, hdigits]
  rcases Nat.even_or_odd q with heven | hodd
  · have herrpos : 0 < conjugateError n := by
      rw [Real.inv_goldenRatio] at htail
      rw [herror]
      have hqpow : Real.goldenConj ^ q = (-Real.goldenConj) ^ q := by
        exact (heven.neg_pow Real.goldenConj).symm
      have hlower := (abs_lt.mp htail).1
      have hpowers := pow_sub_pow_succ q
      rw [Real.inv_goldenRatio] at hpowers
      have hpos : 0 < (-Real.goldenConj) ^ (q + 2) :=
        pow_pos (neg_pos.mpr Real.goldenConj_neg) _
      rw [hqpow]
      linarith
    have hcand := fib_candidate_lt_of_nonsingle hpre hdigits
    have hcandpos : 0 < Nat.fib (q + 2) := Nat.fib_pos.mpr (by omega)
    have hevenTwo : Even (q + 2) := by
      obtain ⟨m, hm⟩ := heven
      exact ⟨m + 1, by omega⟩
    have hcandExact := backward_displacement_fib_even (q := q + 2) (by omega) hevenTwo
    have htarget := backward_displacement_eq_of_error_pos hn herrpos
    have hlower := (abs_lt.mp htail).1
    have hpowers := pow_sub_pow_succ q
    have hqpow : Real.goldenConj ^ q = Real.goldenRatio⁻¹ ^ q := by
      rw [Real.inv_goldenRatio]
      exact (heven.neg_pow Real.goldenConj).symm
    have hsmall :
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope
            (Nat.fib (q + 2)) <
          GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope n := by
      rw [hcandExact, htarget, herror, hqpow]
      linarith
    exact (lt_asymm (hrecord _ hcandpos hcand) hsmall).elim
  · have herrneg : conjugateError n < 0 := by
      rw [Real.inv_goldenRatio] at htail
      rw [herror]
      have hqpow : Real.goldenConj ^ q = -(-Real.goldenConj) ^ q := by
        rw [hodd.neg_pow]
        ring
      have hupper := (abs_lt.mp htail).2
      have hpowers := pow_sub_pow_succ q
      rw [Real.inv_goldenRatio] at hpowers
      have hpos : 0 < (-Real.goldenConj) ^ (q + 2) :=
        pow_pos (neg_pos.mpr Real.goldenConj_neg) _
      rw [hqpow]
      linarith
    have hcand := fib_candidate_one_lt_of_nonsingle hq hpre hdigits
    have hcandpos : 0 < Nat.fib (q + 1) := Nat.fib_pos.mpr (by omega)
    have hevenOne : Even (q + 1) := hodd.add_one
    have hcandExact := backward_displacement_fib_even (q := q + 1) (by omega) hevenOne
    have htargetForward := forward_displacement_eq_of_error_neg herrneg
    have htarget := GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
      golden_mechanical_slope_irrational hn
    have herrBound := abs_conjugate_error_lt_inv n
    rw [abs_of_neg herrneg] at herrBound
    have hbackward :
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope n =
          1 + conjugateError n := by
      linarith [htarget, htargetForward]
    have hsmall :
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope
            (Nat.fib (q + 1)) <
          GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope n := by
      rw [hcandExact, hbackward]
      have hpow : Real.goldenRatio⁻¹ ^ (q + 1) < Real.goldenRatio⁻¹ ^ 2 := by
        rw [pow_lt_pow_iff_right_of_lt_one₀ (inv_pos.mpr Real.goldenRatio_pos)
          (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)]
        omega
      have hr := inv_golden_sq_add_inv_golden
      linarith
    exact (lt_asymm (hrecord _ hcandpos hcand) hsmall).elim

private theorem golden_phase_add (i d : Nat) :
    goldenPhase (i + d) =
      Int.fract (goldenPhase i + (d : Real) * goldenMechanicalSlope) := by
  rw [goldenPhase, goldenPhase]
  have harg : (((i + d + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (d : Real) * goldenMechanicalSlope := by
    push_cast
    ring
  rw [harg]
  conv_lhs =>
    enter [1, 1]
    rw [← Int.floor_add_fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)]
  rw [add_assoc, Int.fract_intCast_add]

private theorem fract_add_forward (x : Real) (k : Nat) :
    Int.fract (x + (k : Real) * goldenMechanicalSlope) =
      Int.fract (x + GoldenArcFirstReturnInternal.forwardDisplacement
        goldenMechanicalSlope k) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊(k : Real) * goldenMechanicalSlope⌋, ?_⟩
  rw [GoldenArcFirstReturnInternal.forwardDisplacement]
  linarith [Int.self_sub_fract ((k : Real) * goldenMechanicalSlope)]

private theorem golden_phase_add_of_no_wrap {i k : Nat}
    (hnowrap : goldenPhase i +
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k < 1) :
    goldenPhase (i + k) = goldenPhase i +
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k := by
  rw [golden_phase_add, fract_add_forward]
  apply Int.fract_eq_self.mpr
  exact ⟨add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _), hnowrap⟩

private theorem golden_phase_add_of_wrap {i k : Nat} (hk : 0 < k)
    (hwrap : 1 ≤ goldenPhase i +
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k) :
    goldenPhase (i + k) = goldenPhase i -
      GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope k := by
  have hback := GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
    golden_mechanical_slope_irrational hk
  rw [golden_phase_add, fract_add_forward]
  calc
    Int.fract (goldenPhase i +
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k) =
        Int.fract (goldenPhase i +
          GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k - 1) :=
      (Int.fract_sub_one _).symm
    _ = goldenPhase i +
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k - 1 := by
      apply Int.fract_eq_self.mpr
      constructor
      · linarith
      · have hphase := Int.fract_lt_one (((i + 1 : Nat) : Real) * goldenMechanicalSlope)
        have hforward := Int.fract_lt_one ((k : Real) * goldenMechanicalSlope)
        change goldenPhase i < 1 at hphase
        change GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k < 1
          at hforward
        linarith
    _ = goldenPhase i -
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope k := by
      rw [hback]
      ring

private theorem golden_arc_first_return_record {n d : Nat} {r : Fin (n + 1)}
    (hd : d ∈ goldenArcFirstReturnGapSet n r) :
    (∀ k, 0 < k → k < d →
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope d <
          GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k) ∨
      (∀ k, 0 < k → k < d →
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope d <
          GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope k) := by
  rcases hd with ⟨hdpos, i, hstart, hreturn, hfirst⟩
  simp only [rotationGapArc, Set.mem_Ico] at hstart hreturn ⊢
  by_cases hnowrap : goldenPhase i +
      GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope d < 1
  · have hdphase := golden_phase_add_of_no_wrap (i := i) (k := d) hnowrap
    rw [hdphase] at hreturn
    left
    intro k hkpos hkd
    by_contra hnot
    have hkle : GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k ≤
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope d :=
      le_of_not_gt hnot
    apply hfirst k hkpos hkd
    rw [rotationGapArc]
    have hnowrapk : goldenPhase i +
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k < 1 := by
      linarith
    rw [golden_phase_add_of_no_wrap hnowrapk]
    have hkforward := GoldenArcFirstReturnInternal.forward_displacement_pos
      golden_mechanical_slope_irrational hkpos
    exact ⟨by linarith, by linarith⟩
  · have hwrap : 1 ≤ goldenPhase i +
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope d :=
      le_of_not_gt hnowrap
    have hdphase := golden_phase_add_of_wrap (i := i) hdpos hwrap
    rw [hdphase] at hreturn
    right
    intro k hkpos hkd
    by_contra hnot
    have hkle : GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope k ≤
        GoldenArcFirstReturnInternal.backwardDisplacement goldenMechanicalSlope d :=
      le_of_not_gt hnot
    have hbackd := GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
      golden_mechanical_slope_irrational hdpos
    have hbackk := GoldenArcFirstReturnInternal.backward_displacement_eq_one_sub_forward
      golden_mechanical_slope_irrational hkpos
    have hwrapk : 1 ≤ goldenPhase i +
        GoldenArcFirstReturnInternal.forwardDisplacement goldenMechanicalSlope k := by
      linarith
    apply hfirst k hkpos hkd
    rw [rotationGapArc, golden_phase_add_of_wrap hkpos hwrapk]
    have hkbackward := GoldenArcFirstReturnInternal.backward_displacement_pos
      golden_mechanical_slope_irrational hkpos
    exact ⟨by linarith, by linarith⟩

private theorem golden_arc_first_return_gap_is_fib {n d : Nat} {r : Fin (n + 1)}
    (hd : d ∈ goldenArcFirstReturnGapSet n r) :
    ∃ q, 2 ≤ q ∧ d = Nat.fib q := by
  have hdpos : 0 < d := hd.1
  rcases golden_arc_first_return_record hd with hforward | hbackward
  · exact forward_record_is_fib hdpos hforward
  · exact backward_record_is_fib hdpos hbackward

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

private theorem golden_cylinder_rank_lt_succ (n i : Nat) :
    goldenCylinderRank n i < n + 1 := by
  apply Nat.lt_succ_iff.mpr
  change
    (((Finset.range n).image fun m : Nat =>
      1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).filter
        (fun x => x ≤ goldenPhase i)).card ≤ n
  calc
    _ ≤ ((Finset.range n).image fun m : Nat =>
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).card :=
      Finset.card_filter_le _ _
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

theorem GoldenCubePeriodsInternal.golden_adjacent_gap_is_fib
    {n : Nat} {w : List Bool} {i j : Nat}
    (hadj : AdjacentGoldenOccurrences n w i j) :
    ∃ q, 2 ≤ q ∧ j - i = Nat.fib q := by
  have hs := adjacent_golden_occurrences_iff.mp hadj
  have hgap : j - i ∈ goldenOccurrenceGapSet n w := ⟨i, j, hadj, rfl⟩
  have hrank :
      j - i ∈ goldenRankFirstReturnGapSet n (goldenCylinderRank n i) := by
    rw [← golden_occurrence_gap_set_eq_rank_first_return_gap_set hs.2.1]
    exact hgap
  let r : Fin (n + 1) := ⟨goldenCylinderRank n i, golden_cylinder_rank_lt_succ n i⟩
  have harc : j - i ∈ goldenArcFirstReturnGapSet n r := by
    rw [golden_arc_first_return_gap_set_eq_rank_first_return_gap_set]
    exact hrank
  exact golden_arc_first_return_gap_is_fib harc
/-! ### Regression anchors -/

private theorem golden_cube_root_length_witness :
    IsGoldenPowerFactor 3 [true, false, true] 5 ∧
      [true, false, true].length = Nat.fib 4 := by
  exact ⟨golden_cube_is_power_factor, by decide⟩

private theorem golden_no_cube_root_length_four_below_64 :
    ∀ i < 64, goldenFactor 12 i ≠ wordPower 3 (goldenFactor 4 i) := by
  decide

end

end D5.S1.Words.Powers
