/- GID: D5/S1/Words/Expansions/BasePhiRecursiveStructure
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiRecursiveStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-coordinate and floor fibers governing recursive negative base-phi tails. -/

import D5.S1.Words.Expansions.BasePhiTailBounds
import D5.S1.Words.ZeckendorfBeattyBridge

namespace D5.S1.Words.Expansions.BasePhiRecursiveStructure

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Words
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiNegativeBridge
open D5.S1.Words.Expansions.BasePhiTailBounds

noncomputable section

local instance (priority := low) (p : Prop) : Decidable p :=
  Classical.propDecidable p

/- Library-search receipt (2026-08-22): repository declarations reused below
include `canonicalRaw_unique`, `rawValue_toRaw_Z`,
`goldenReadout_natDigits`, `betaContraction_mem_window`,
`mem_rawToZeckendorf_iff`, and `zeckendorf_beatty_bridge`. Pinned mathlib
provides `Real.goldenRatio_irrational`, `Int.floor_eq_iff`, and the Finsupp
domain embedding operations. No declaration in either source states the
complete-negative-tail fiber classification. -/

/-- Two inputs have the same complete negative-position digit tail. -/
def SameNegativeTail (expansion : BasePhiNegativeExpansion) (M N : Nat) : Prop :=
  ∀ i : Nat, negativeDigit expansion M i = negativeDigit expansion N i

/-- The positive-natural fiber of a complete negative-position digit tail. -/
def negativeTailFiber (expansion : BasePhiNegativeExpansion) (N : Nat) : Set Nat :=
  {M | 0 < M ∧ SameNegativeTail expansion M N}

/-- The second coordinate of a canonical nonnegative base-phi word, in its
closed Beatty form. -/
noncomputable def positiveCoordinate (v : Nat) : Int :=
  ⌊((v : Real) + 1) / Real.goldenRatio ^ 2⌋

private theorem invGoldenSq_eq_two_sub :
    (Real.goldenRatio ^ 2)⁻¹ = 2 - Real.goldenRatio := by
  rw [← inv_pow, Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj]

private theorem invGoldenSq_pos : 0 < (Real.goldenRatio ^ 2)⁻¹ := by
  positivity

private theorem invGoldenSq_lt_one : (Real.goldenRatio ^ 2)⁻¹ < 1 := by
  rw [invGoldenSq_eq_two_sub]
  linarith [Real.one_lt_goldenRatio]

private theorem invGoldenSq_mul_goldenSq :
    (Real.goldenRatio ^ 2)⁻¹ * Real.goldenRatio ^ 2 = 1 := by
  exact inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt Real.goldenRatio_pos))

private theorem betaGolden_eq_golden_phiSq_mul_positive (v : Nat) :
    betaGolden v = D5.S0.Carrier.phi ^ 2 *
      basePhiValue (natLift (toRaw (Z v))) := by
  change betaDigits (toRaw (Z v)) = D5.S0.Carrier.phi ^ 2 *
    basePhiValue (natLift (toRaw (Z v)))
  change (toRaw (Z v)).sum (fun i coefficient =>
      (coefficient : GoldenInt) * D5.S0.Carrier.phi ^ (i + 2)) =
    D5.S0.Carrier.phi ^ 2 *
      (natLift (toRaw (Z v))).sum (fun i coefficient =>
        (coefficient : GoldenInt) *
          (((D5.S0.Carrier.phiUnit ^ i : GoldenIntˣ) : GoldenInt)))
  rw [natLift, Finsupp.sum_embDomain]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i hi
  change (toRaw (Z v) i : GoldenInt) * D5.S0.Carrier.phi ^ (i + 2) =
    D5.S0.Carrier.phi ^ 2 *
      ((toRaw (Z v) i : GoldenInt) *
        (((D5.S0.Carrier.phiUnit ^ (i : Int) : GoldenIntˣ) : GoldenInt)))
  have hpower :
      (((D5.S0.Carrier.phiUnit ^ (i : Int) : GoldenIntˣ) : GoldenInt)) =
        D5.S0.Carrier.phi ^ i := by
    rw [zpow_natCast]
    simp [D5.S0.Carrier.coe_phiUnit]
  rw [hpower, pow_add]
  ring

theorem positive_value_coordinates (v : Nat) :
    let value := basePhiValue (natLift (toRaw (Z v)))
    value.a = (v : Int) - 2 * positiveCoordinate v ∧
      value.b = positiveCoordinate v := by
  let value := basePhiValue (natLift (toRaw (Z v)))
  have hreadout : value.a + 2 * value.b = (v : Int) := by
    have := goldenReadout_natDigits (toRaw (Z v))
    rw [rawValue_toRaw_Z] at this
    exact this
  have hbeta := betaGolden_eq_golden_phiSq_mul_positive v
  have hcontraction := betaContraction_mem_window v
  have hreadoutReal : (value.a : Real) + 2 * (value.b : Real) = (v : Real) := by
    exact_mod_cast hreadout
  have hformula : betaContraction v =
      (v : Real) * (Real.goldenRatio ^ 2)⁻¹ - (value.b : Real) := by
    rw [betaContraction, hbeta]
    have hphiSq : D5.S0.Carrier.phi ^ 2 =
        (1 : GoldenInt) + D5.S0.Carrier.phi := D5.S0.Carrier.phi_sq
    have hmulA : (D5.S0.Carrier.phi ^ 2 * value).a =
        value.a + value.b := by
      rw [hphiSq]
      simp [a_mul]
    have hmulB : (D5.S0.Carrier.phi ^ 2 * value).b =
        value.a + 2 * value.b := by
      rw [hphiSq]
      simp [b_mul]
      ring
    change (((D5.S0.Carrier.phi ^ 2 * value).a +
        (D5.S0.Carrier.phi ^ 2 * value).b : Int) : Real) +
      ((-(D5.S0.Carrier.phi ^ 2 * value).b : Int) : Real) *
        Real.goldenRatio =
      (v : Real) * (Real.goldenRatio ^ 2)⁻¹ - (value.b : Real)
    rw [hmulA, hmulB]
    rw [invGoldenSq_eq_two_sub]
    push_cast
    linear_combination
      (2 - Real.goldenRatio) * hreadoutReal
  have hpsiSq : Real.goldenConj ^ 2 = (Real.goldenRatio ^ 2)⁻¹ := by
    rw [Real.goldenConj_sq, invGoldenSq_eq_two_sub]
    linarith [Real.goldenRatio_add_goldenConj]
  have hnegPsi : -Real.goldenConj = 1 - (Real.goldenRatio ^ 2)⁻¹ := by
    rw [invGoldenSq_eq_two_sub]
    linarith [Real.goldenRatio_add_goldenConj]
  rw [hformula, hpsiSq, hnegPsi] at hcontraction
  have hirr : Irrational
      (((v : Real) + 1) * (Real.goldenRatio ^ 2)⁻¹) := by
    rw [invGoldenSq_eq_two_sub]
    have hbase : Irrational (2 - Real.goldenRatio) := by
      exact Real.goldenRatio_irrational.neg.intCast_add 2
    have hcast : (v : Real) + 1 = ((v + 1 : Nat) : Real) := by norm_num
    rw [hcast]
    exact hbase.natCast_mul (Nat.succ_ne_zero v)
  have hstrict : ((v : Real) + 1) * (Real.goldenRatio ^ 2)⁻¹ <
      (value.b : Real) + 1 := by
    have hle : ((v : Real) + 1) * (Real.goldenRatio ^ 2)⁻¹ ≤
        (value.b : Real) + 1 := by
      linarith [hcontraction.1]
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hirr.ne_int (value.b + 1)
      exact_mod_cast heq)
  have hfloor :
      ⌊((v : Real) + 1) * (Real.goldenRatio ^ 2)⁻¹⌋ = value.b := by
    apply Int.floor_eq_iff.mpr
    constructor
    · linarith [hcontraction.2]
    · exact hstrict
  have hcoordinate : positiveCoordinate v = value.b := by
    rw [positiveCoordinate, div_eq_mul_inv, hfloor]
  constructor
  · calc
      value.a = (v : Int) - 2 * value.b := by omega
      _ = (v : Int) - 2 * positiveCoordinate v := by rw [hcoordinate]
  · exact hcoordinate.symm

private theorem canonical_positive_coordinates {digits : RawDigits}
    (hcanonical : CanonicalRaw digits) :
    let v := rawValue digits
    let value := basePhiValue (natLift digits)
    value.a = (v : Int) - 2 * positiveCoordinate v ∧
      value.b = positiveCoordinate v := by
  have hdigits : digits = toRaw (Z (rawValue digits)) := by
    apply canonicalRaw_unique hcanonical (canonicalRaw_toRaw _)
    rw [rawValue_toRaw_Z]
  rw [hdigits]
  simpa using positive_value_coordinates (rawValue digits)

private theorem inverseSq_eq_one_sub_inverse :
    (Real.goldenRatio ^ 2)⁻¹ = 1 - Real.goldenRatio⁻¹ := by
  rw [invGoldenSq_eq_two_sub, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

private theorem floor_mul_inverseSq (n : Nat) (hn : n ≠ 0) :
    ⌊(n : Real) * (Real.goldenRatio ^ 2)⁻¹⌋ =
      (n : Int) - ⌊(n : Real) * Real.goldenRatio⁻¹⌋ - 1 := by
  have hirr : Irrational ((n : Real) * Real.goldenRatio⁻¹) :=
    Real.goldenRatio_irrational.inv.natCast_mul hn
  have hnotmem : (n : Real) * Real.goldenRatio⁻¹ ∉
      Set.range ((↑) : Int → Real) := by
    rintro ⟨z, hz⟩
    exact hirr.ne_int z hz.symm
  have hceil : ⌈(n : Real) * Real.goldenRatio⁻¹⌉ =
      ⌊(n : Real) * Real.goldenRatio⁻¹⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).2 hnotmem
  have harg : (n : Real) * (Real.goldenRatio ^ 2)⁻¹ =
      -((n : Real) * Real.goldenRatio⁻¹) + (n : Int) := by
    rw [inverseSq_eq_one_sub_inverse]
    push_cast
    ring
  rw [harg, Int.floor_add_intCast, Int.floor_neg, hceil]
  ring

private theorem positiveCoordinate_succ_eq_iff (v : Nat) :
    positiveCoordinate (v + 1) = positiveCoordinate v ↔
      goldenMechanicalLetter (v + 1) = 1 := by
  have hcurrent := floor_mul_inverseSq (v + 1) (by omega)
  have hnext := floor_mul_inverseSq (v + 2) (by omega)
  have hcurrentCoordinate : positiveCoordinate v =
      (v + 1 : Int) -
        ⌊(((v + 1 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ - 1 := by
    rw [positiveCoordinate, div_eq_mul_inv]
    simpa only [Nat.cast_add, Nat.cast_one] using hcurrent
  have hnextCoordinate : positiveCoordinate (v + 1) =
      (v + 2 : Int) -
        ⌊(((v + 2 : Nat) : Real) * Real.goldenRatio⁻¹)⌋ - 1 := by
    rw [positiveCoordinate, div_eq_mul_inv]
    rw [show (((v + 1 : Nat) : Real) + 1) = ((v + 2 : Nat) : Real) by
      push_cast
      ring]
    exact hnext
  rw [hcurrentCoordinate, hnextCoordinate,
    goldenMechanicalLetter, goldenMechanicalSlope]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show (v : Real) + 1 + 1 = (v : Real) + 2 by ring]
  omega

theorem canonical_zero_digit_iff_coordinate_succ
    {digits : RawDigits} (hcanonical : CanonicalRaw digits) :
    digits 0 = 0 ↔
      positiveCoordinate (rawValue digits + 1) =
        positiveCoordinate (rawValue digits) := by
  let v := rawValue digits
  have hdigits : digits = toRaw (Z v) := by
    apply canonicalRaw_unique hcanonical (canonicalRaw_toRaw _)
    rw [rawValue_toRaw_Z]
  have hmem : 2 ∈ wdigits v ↔ digits 0 = 1 := by
    rw [← mem_rawToZeckendorf_iff hcanonical 0]
    rw [rawToZeckendorf_eq_zeckendorf hcanonical]
    rfl
  have hzero : digits 0 = 0 ↔ 2 ∉ wdigits v := by
    have hle := hcanonical.1 0
    constructor
    · intro hz htwo
      exact zero_ne_one (hz.symm.trans (hmem.mp htwo))
    · intro hnot
      by_contra hz
      have hone : digits 0 = 1 := by omega
      exact hnot (hmem.mpr hone)
  rw [hzero, zeckendorf_beatty_bridge, ← positiveCoordinate_succ_eq_iff]

private theorem negativePart_apply_of_negative
    (expansion : BasePhiNegativeExpansion) (N : Nat) {i : Int}
    (hi : i < 0) : negativePart expansion N i = expansion.digit N i := by
  let index : Nat := (-i).toNat - 1
  have hminusPos : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hcast : ((-i).toNat : Int) = -i :=
    Int.toNat_of_nonneg (by omega)
  have hnat : index + 1 = (-i).toNat := by
    dsimp [index]
    exact Nat.sub_add_cancel (by omega)
  have hindex : -((index + 1 : Nat) : Int) = i := by
    rw [hnat, hcast]
    ring
  rw [← hindex, negativePart_apply]

theorem negativePart_binary (expansion : BasePhiNegativeExpansion)
    (N : Nat) : ∀ i : Int, negativePart expansion N i ≤ 1 := by
  intro i
  by_cases hi : i < 0
  · rw [negativePart_apply_of_negative expansion N hi]
    exact expansion.binary N i
  · rw [negativePart_eq_zero_of_nonnegative expansion N (le_of_not_gt hi)]
    omega

theorem negativePart_canonical (expansion : BasePhiNegativeExpansion)
    (N : Nat) : ∀ i : Int,
      negativePart expansion N i = 1 → negativePart expansion N (i + 1) = 0 := by
  intro i hone
  have hi : i < 0 := by
    by_contra hnonnegative
    have hzero := negativePart_eq_zero_of_nonnegative expansion N
      (le_of_not_gt hnonnegative)
    omega
  have hdigit : expansion.digit N i = 1 := by
    rw [negativePart_apply_of_negative expansion N hi] at hone
    exact hone
  have hnext := expansion.canonical N i hdigit
  by_cases hnextNegative : i + 1 < 0
  · rw [negativePart_apply_of_negative expansion N hnextNegative, hnext]
  · rw [negativePart_eq_zero_of_nonnegative expansion N
      (le_of_not_gt hnextNegative)]

private theorem sameNegativeTail_iff_negativeDigits_eq
    (expansion : BasePhiNegativeExpansion) (M N : Nat) :
    SameNegativeTail expansion M N ↔
      negativeDigits expansion M = negativeDigits expansion N := by
  constructor
  · intro htail
    apply Finsupp.ext
    intro i
    have hbool := htail i
    change decide (negativeDigits expansion M i = 1) =
      decide (negativeDigits expansion N i = 1) at hbool
    have hMle := expansion.binary M (-((i + 1 : Nat) : Int))
    have hNle := expansion.binary N (-((i + 1 : Nat) : Int))
    rw [← negativeDigits_apply] at hMle hNle
    have hiff : negativeDigits expansion M i = 1 ↔
        negativeDigits expansion N i = 1 := by
      constructor
      · intro hM
        apply of_decide_eq_true
        calc
          decide (negativeDigits expansion N i = 1) =
              decide (negativeDigits expansion M i = 1) := hbool.symm
          _ = true := by simp only [hM, decide_true]
      · intro hN
        apply of_decide_eq_true
        calc
          decide (negativeDigits expansion M i = 1) =
              decide (negativeDigits expansion N i = 1) := hbool
          _ = true := by simp only [hN, decide_true]
    omega
  · intro hdigits i
    unfold negativeDigit
    rw [← negativeDigits_apply, ← negativeDigits_apply, hdigits]

theorem sameNegativeTail_iff_negativeValue_eq
    (expansion : BasePhiNegativeExpansion) (M N : Nat) :
    SameNegativeTail expansion M N ↔
      basePhiValue (negativePart expansion M) =
        basePhiValue (negativePart expansion N) := by
  rw [sameNegativeTail_iff_negativeDigits_eq]
  constructor
  · intro h
    rw [negativePart, negativePart, h]
  · intro hvalue
    apply Finsupp.embDomain_injective negativeIndexEmbedding
    apply bilateral_basePhi_injective
      (negativePart_binary expansion M) (negativePart_canonical expansion M)
      (negativePart_binary expansion N) (negativePart_canonical expansion N)
      hvalue

noncomputable def positiveValue
    (expansion : BasePhiNegativeExpansion) (N : Nat) : GoldenInt :=
  basePhiValue (natLift (nonnegativeDigits expansion N))

def positiveIndex (expansion : BasePhiNegativeExpansion) (N : Nat) : Nat :=
  rawValue (nonnegativeDigits expansion N)

theorem negativeValue_add_positiveValue
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    basePhiValue (negativePart expansion N) + positiveValue expansion N =
      (N : GoldenInt) := by
  rw [positiveValue, ← basePhiValue_digit_decomposition]
  exact expansion.value_equation N

theorem positiveValue_coordinates
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    (positiveValue expansion N).a =
        (positiveIndex expansion N : Int) -
          2 * positiveCoordinate (positiveIndex expansion N) ∧
      (positiveValue expansion N).b =
        positiveCoordinate (positiveIndex expansion N) := by
  exact canonical_positive_coordinates (nonnegativeDigits_canonical expansion N)

private theorem two_mul_inverseSq_lt_one :
    2 * (Real.goldenRatio ^ 2)⁻¹ < 1 := by
  have hsquare : 2 < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hpos : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  nlinarith [invGoldenSq_mul_goldenSq]

private theorem one_lt_three_mul_inverseSq :
    1 < 3 * (Real.goldenRatio ^ 2)⁻¹ := by
  have hsquare : Real.goldenRatio ^ 2 < 3 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.goldenRatio_lt_two]
  have hpos : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  nlinarith [invGoldenSq_mul_goldenSq]

private theorem inverse_cut_identity :
    (Real.goldenRatio⁻¹ + 2) * (Real.goldenRatio ^ 2)⁻¹ = 1 := by
  rw [Real.inv_goldenRatio, invGoldenSq_eq_two_sub]
  nlinarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj,
    Real.goldenRatio_sq]

def fiberStartInt (tail : GoldenInt) (B : Int) : Int :=
  tail.a + B - 1

private theorem start_coordinate_identity (tail : GoldenInt) (B : Int)
    (htail : embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio) :
    ((fiberStartInt tail B : Int) : Real) + 1 =
      (B : Real) * Real.goldenRatio ^ 2 + embedding tail := by
  rw [fiberStartInt, htail, Real.goldenRatio_sq]
  push_cast
  ring

theorem positiveCoordinate_fiber_small
    (tail : GoldenInt) (B : Int)
    (htail : embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio)
    (htailPos : 0 < embedding tail)
    (htailSmall : embedding tail < Real.goldenRatio⁻¹)
    (v : Nat) :
    positiveCoordinate v = B ↔
      fiberStartInt tail B ≤ (v : Int) ∧
        (v : Int) ≤ fiberStartInt tail B + 2 := by
  let alpha := (Real.goldenRatio ^ 2)⁻¹
  let start := fiberStartInt tail B
  have hstart := start_coordinate_identity tail B htail
  have hstartAlpha : ((start : Real) + 1) * alpha =
      (B : Real) + embedding tail * alpha := by
    rw [show (start : Real) + 1 =
        (B : Real) * Real.goldenRatio ^ 2 + embedding tail by
      simpa [start] using hstart]
    dsimp [alpha]
    rw [add_mul]
    have hcancel : Real.goldenRatio ^ 2 *
        (Real.goldenRatio ^ 2)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt Real.goldenRatio_pos))
    rw [mul_assoc, hcancel, mul_one]
  have halphaPos : 0 < alpha := invGoldenSq_pos
  have hthree : 1 < 3 * alpha := one_lt_three_mul_inverseSq
  have hcut : (Real.goldenRatio⁻¹ + 2) * alpha = 1 := inverse_cut_identity
  constructor
  · intro hcoordinate
    have hfloor : ⌊((v : Real) + 1) * alpha⌋ = B := by
      simpa [positiveCoordinate, div_eq_mul_inv, alpha] using hcoordinate
    have hbounds := Int.floor_eq_iff.mp hfloor
    constructor
    · by_contra hlower
      have hv : (v : Int) ≤ start - 1 := by omega
      have hvReal : (v : Real) ≤ (start : Real) - 1 := by exact_mod_cast hv
      have : ((v : Real) + 1) * alpha < (B : Real) := by
        nlinarith
      exact (not_lt_of_ge hbounds.1) this
    · by_contra hupper
      have hv : start + 3 ≤ (v : Int) := by omega
      have hvReal : (start : Real) + 3 ≤ (v : Real) := by exact_mod_cast hv
      have : (B : Real) + 1 < ((v : Real) + 1) * alpha := by
        nlinarith
      exact (not_lt_of_ge (le_of_lt hbounds.2)) this
  · rintro ⟨hlower, hupper⟩
    change ⌊((v : Real) + 1) * alpha⌋ = B
    apply Int.floor_eq_iff.mpr
    constructor
    · have hlowerReal : (start : Real) ≤ (v : Real) := by exact_mod_cast hlower
      nlinarith
    · have hupperReal : (v : Real) ≤ (start : Real) + 2 := by exact_mod_cast hupper
      nlinarith

theorem positiveCoordinate_fiber_large
    (tail : GoldenInt) (B : Int)
    (htail : embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio)
    (htailLarge : Real.goldenRatio⁻¹ ≤ embedding tail)
    (htailLtOne : embedding tail < 1)
    (v : Nat) :
    positiveCoordinate v = B ↔
      fiberStartInt tail B ≤ (v : Int) ∧
        (v : Int) ≤ fiberStartInt tail B + 1 := by
  let alpha := (Real.goldenRatio ^ 2)⁻¹
  let start := fiberStartInt tail B
  have hstart := start_coordinate_identity tail B htail
  have hstartAlpha : ((start : Real) + 1) * alpha =
      (B : Real) + embedding tail * alpha := by
    rw [show (start : Real) + 1 =
        (B : Real) * Real.goldenRatio ^ 2 + embedding tail by
      simpa [start] using hstart]
    dsimp [alpha]
    rw [add_mul]
    have hcancel : Real.goldenRatio ^ 2 *
        (Real.goldenRatio ^ 2)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt Real.goldenRatio_pos))
    rw [mul_assoc, hcancel, mul_one]
  have halphaPos : 0 < alpha := invGoldenSq_pos
  have htwo : 2 * alpha < 1 := two_mul_inverseSq_lt_one
  have hcut : (Real.goldenRatio⁻¹ + 2) * alpha = 1 := inverse_cut_identity
  constructor
  · intro hcoordinate
    have hfloor : ⌊((v : Real) + 1) * alpha⌋ = B := by
      simpa [positiveCoordinate, div_eq_mul_inv, alpha] using hcoordinate
    have hbounds := Int.floor_eq_iff.mp hfloor
    constructor
    · by_contra hlower
      have hv : (v : Int) ≤ start - 1 := by omega
      have hvReal : (v : Real) ≤ (start : Real) - 1 := by exact_mod_cast hv
      have : ((v : Real) + 1) * alpha < (B : Real) := by
        nlinarith
      exact (not_lt_of_ge hbounds.1) this
    · by_contra hupper
      have hv : start + 2 ≤ (v : Int) := by omega
      have hvReal : (start : Real) + 2 ≤ (v : Real) := by exact_mod_cast hv
      have : (B : Real) + 1 ≤ ((v : Real) + 1) * alpha := by
        nlinarith
      exact (not_le_of_gt hbounds.2) this
  · rintro ⟨hlower, hupper⟩
    change ⌊((v : Real) + 1) * alpha⌋ = B
    apply Int.floor_eq_iff.mpr
    constructor
    · have hlowerReal : (start : Real) ≤ (v : Real) := by exact_mod_cast hlower
      nlinarith
    · have hupperReal : (v : Real) ≤ (start : Real) + 1 := by exact_mod_cast hupper
      nlinarith

end

end D5.S1.Words.Expansions.BasePhiRecursiveStructure
