/- GID: D5/S1/Deficit/RawObservation/NormalizationResidual
   generality: G
   mirror-B: none(waiver:new-formal-source)
   mirror-E: none(waiver:universal-algebraic-proof)
   anchors: []
   utility: none
   digest: Exact normalization-charge fibers and Fibonacci amplification of the lost
     coordinate; equal complete shift observations still need not determine carry legality. -/

import D5.S1.Deficit.RawObservation.ShiftReadout
import D5.S1.Deficit.ChargedCarryPath

set_option autoImplicit false

namespace D5.S1.Deficit.RawObservation

open D5.S0.Carrier D5.S1.Digit D5.S1.Deficit.DoubleFaceLength

private theorem normalized_beta (r : RawDigits) :
    betaDigits (normalize r) = betaGolden (rawValue r) := by
  have h : normalize r = toRaw (Z (rawValue r)) := by
    apply canonicalRaw_unique (normalize_canonical r) (canonicalRaw_toRaw _)
    rw [rawValue_normalize, rawValue_toRaw_Z]
  rw [h]
  rfl

private theorem normalization_decomposition (r : RawDigits) :
    betaDigits r = betaDigits (normalize r) + (carrySignedCount r : GoldenInt) := by
  have h := betaDigits_sub_chargedReduces (charged_normalize_exists r)
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- The charge is the actual coordinate discarded by the actual normalizer. -/
theorem charge_coordinate (r : RawDigits) :
    (betaDigits r).a = (betaGolden (rawValue r)).a + carrySignedCount r := by
  have h := congrArg GoldenInt.a (normalization_decomposition r)
  rw [normalized_beta] at h
  simpa only [a_add, a_intCast] using h

/-- Complete existence criterion for a displayed value and signed normalization charge.
The criterion quantifies over the actual raw inputs and existing carrySignedCount. -/
theorem charge_spectrum_iff (n : Nat) (c : Int) :
    (∃ r : RawDigits, rawValue r = n ∧ carrySignedCount r = c) ↔
      (betaGolden n).a + c ≤ (n : Int) ∧
        (n : Int) ≤ 2 * ((betaGolden n).a + c) := by
  constructor
  · rintro ⟨r, hn, hc⟩
    have ha := charge_coordinate r
    rw [hn, hc] at ha
    exact (display_fiber_iff n ((betaGolden n).a + c)).mp ⟨r, hn, ha⟩
  · intro h
    obtain ⟨r, hn, ha⟩ := (display_fiber_iff n ((betaGolden n).a + c)).mpr h
    have hc := charge_coordinate r
    rw [hn, ha] at hc
    exact ⟨r, hn, by omega⟩

/-- Value plus actual charge is exactly the golden semantic quotient of raw inputs. -/
theorem beta_eq_iff_value_charge (r s : RawDigits) :
    betaDigits r = betaDigits s ↔
      rawValue r = rawValue s ∧ carrySignedCount r = carrySignedCount s := by
  constructor
  · intro h
    have hn := ((beta_eq_iff_display_pair r s).mp h).1
    have hr := charge_coordinate r
    have hs := charge_coordinate s
    have ha := congrArg GoldenInt.a h
    rw [hn] at hr
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, hc⟩
    apply GoldenInt.ext
    · rw [charge_coordinate r, charge_coordinate s, hn, hc]
    · rw [betaDigits_b, betaDigits_b, hn]

/-- The information erased by normalization reappears under every raw shift with
its exact Fibonacci coefficient. The integer difference can have either sign. -/
theorem normalization_shift_defect (r : RawDigits) (k : Nat) :
    (shiftedValue k r : Int) - (shiftedValue k (normalize r) : Int) =
      (Nat.fib k : Int) * carrySignedCount r := by
  rw [shiftedValue_as_coordinate, shiftedValue_as_coordinate,
    normalization_decomposition r, mul_add, b_add]
  simp [b_mul, phi_pow_b]

/-- Replacing a raw input by its canonical display representative preserves all
raw shift observations exactly when its signed normalization charge vanishes. -/
theorem normalization_preserves_all_shifts_iff (r : RawDigits) :
    (∀ k : Nat, shiftedValue k r = shiftedValue k (normalize r)) ↔
      carrySignedCount r = 0 := by
  constructor
  · intro h
    have hd := normalization_shift_defect r 1
    rw [h 1] at hd
    simpa using hd.symm
  · intro hc k
    have hd := normalization_shift_defect r k
    rw [hc, mul_zero] at hd
    exact_mod_cast (sub_eq_zero.mp hd)

private theorem one_digit_canonical (i : Nat) :
    CanonicalRaw (Finsupp.single i 1) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne h]
  · intro j hj
    have hji : j = i := by
      by_contra h
      simp [Finsupp.single_eq_of_ne h] at hj
    subst j
    simp [Finsupp.single_eq_of_ne (by omega : i + 1 ≠ i)]

/-- An infinite family of real raw-state collisions invisible to ALL shift probes:
one input is canonical and the other has an actual legal adjacent carry. -/
theorem all_shifts_hide_carry_applicability (i : Nat) :
    ∃ r s : RawDigits,
      betaDigits r = betaDigits s ∧
      (∀ k : Nat, shiftedValue k r = shiftedValue k s) ∧
      CanonicalRaw r ∧ ¬ CanonicalRaw s ∧ CarryStep s r := by
  let r : RawDigits := Finsupp.single (i + 2) 1
  let s : RawDigits := Finsupp.single i 1 + Finsupp.single (i + 1) 1
  have hs : ChargedCarryStep s r 0 := by
    simpa [r, s] using ChargedCarryStep.adjacent (0 : RawDigits) i
  have he : betaDigits s = betaDigits r := by
    apply sub_eq_zero.mp
    simpa using betaDigits_sub_chargedCarryStep hs
  have hcanon : CanonicalRaw r := one_digit_canonical (i + 2)
  have hnot : ¬ CanonicalRaw s := by
    intro h
    have h0 : s i = 1 := by
      simp [s, Finsupp.single_eq_of_ne (by omega : i ≠ i + 1)]
    have h1 : s (i + 1) = 1 := by
      simp [s, Finsupp.single_eq_of_ne (by omega : i + 1 ≠ i)]
    have hz := h.2 i h0
    omega
  exact ⟨r, s, he.symm, (beta_eq_iff_all_shifts r s).mp he.symm,
    hcanon, hnot, hs.toCarryStep⟩

/-- No proposition of the complete shift-readout sequence can recognize canonical
raw inputs. Golden-state recovery and raw-state recovery are different claims. -/
theorem no_shift_only_canonicality_test :
    ¬ ∃ test : (Nat → Nat) → Prop, ∀ r : RawDigits,
      CanonicalRaw r ↔ test (fun k => shiftedValue k r) := by
  rintro ⟨test, htest⟩
  obtain ⟨r, s, _, hshift, hr, hs, _⟩ := all_shifts_hide_carry_applicability 0
  have hseq : (fun k => shiftedValue k r) = (fun k => shiftedValue k s) := funext hshift
  have ht := (htest r).mp hr
  rw [hseq] at ht
  exact hs ((htest s).mpr ht)

#print axioms charge_spectrum_iff
#print axioms normalization_shift_defect
#print axioms normalization_preserves_all_shifts_iff
#print axioms all_shifts_hide_carry_applicability
#print axioms no_shift_only_canonicality_test

end D5.S1.Deficit.RawObservation
