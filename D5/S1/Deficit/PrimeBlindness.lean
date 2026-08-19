/- GID: D5/S1/Deficit/PrimeBlindness
   generality: I
   mirror-B: D5/B/S1/Deficit/PrimeBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Primality of the inputs does not determine the golden Beatty deficit. -/

import D5.S1.Deficit.GoldenPhaseDeficit
import D5.S1.Deficit.ZeckendorfDisplacementReading

/- Library-search audit trail (2026-08-19):
   * `FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus` closes proposition
     6.28(ii) for every fixed modulus, and its own docstring records that it "does not assert
     prime-classification blindness". That is the gap this module fills, in deliberately the
     same shape: a witness pair whose classification agrees while the deficit differs.
   * `ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor` states
     `(displacementDecode v : ℤ) = ⌊(v+1)·φ⌋ - 1`, whose right side is exactly `goldenShift v`.
     Since `displacementDecode` is a computable `def`, the shift is evaluated through that
     bridge rather than through a square-root bracket.
   * Recorded gap, not filled here: the reduction of the real-valued `deficit` to the integer
     `beattyDeficit` is proved privately in two separate modules
     (`ZeckendorfDisplacementReading.decode_real` and
     `FixedModulusNoncongruence.betaReal_eq_displacement`) and is public in neither, so a
     statement about `deficit` itself cannot be assembled from the public surface. This module
     therefore speaks about `beattyDeficit`, which is public.
-/

namespace D5.S1.Deficit.PrimeBlindness

open D5.S0.Conventions
open D5.S1.Deficit.GoldenPhaseDeficit
open D5.S1.Deficit.ZeckendorfDisplacementReading

/-- The shift is the displacement decode, read through the public Beatty bridge. -/
theorem goldenShift_eq_displacementDecode (v : ℕ) :
    goldenShift v = (displacementDecode v : ℤ) := by
  rw [goldenShift, displacement_decode_eq_beatty_floor]

private theorem wdigits_eval (v : ℕ) (hv : 0 < v) :
    wdigits v = Nat.greatestFib v :: wdigits (v - Nat.fib (Nat.greatestFib v)) := by
  simpa [wdigits] using Nat.zeckendorf_of_pos hv

private theorem decode_two : displacementDecode 2 = 3 := by
  rw [displacementDecode, wdigits_eval 2 (by norm_num)]
  norm_num [Nat.greatestFib, wdigits]

private theorem decode_three : displacementDecode 3 = 5 := by
  rw [displacementDecode, wdigits_eval 3 (by norm_num)]
  norm_num [Nat.greatestFib, wdigits]

private theorem decode_four : displacementDecode 4 = 7 := by
  rw [displacementDecode, wdigits_eval 4 (by norm_num)]
  norm_num [Nat.greatestFib, wdigits, Nat.zeckendorf_of_pos]

private theorem decode_five : displacementDecode 5 = 8 := by
  rw [displacementDecode, wdigits_eval 5 (by norm_num)]
  norm_num [Nat.greatestFib, wdigits]

/-- Primality of the inputs does not determine the Beatty deficit: both witness pairs
consist of primes, yet their deficits differ. -/
theorem beattyDeficit_not_determined_by_primality :
    ∃ v₁ v₂ v₁' v₂' : ℕ,
      Nat.Prime v₁ ∧ Nat.Prime v₂ ∧ Nat.Prime v₁' ∧ Nat.Prime v₂' ∧
        beattyDeficit v₁ v₂ ≠ beattyDeficit v₁' v₂' := by
  refine ⟨2, 2, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [beattyDeficit, goldenShift_eq_displacementDecode,
    show (2 : ℕ) + 2 = 4 from rfl, show (2 : ℕ) + 3 = 5 from rfl,
    decode_two, decode_three, decode_four, decode_five]
  norm_num

#print axioms beattyDeficit_not_determined_by_primality

end D5.S1.Deficit.PrimeBlindness
