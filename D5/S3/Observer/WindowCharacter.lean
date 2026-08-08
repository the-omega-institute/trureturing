/- GID: D5/S3/Observer/WindowCharacter
   generality: G
   mirror-B: D5/B/S3/Observer/WindowCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exclude complex-algebra characters on every nontrivial finite window algebra. -/

import D5.S3.Observer.WindowRegister

namespace D5.S3.Observer.WindowCharacter

open D5.S3.Observer.WindowRegister

noncomputable section

/-- A nontrivial finite window matrix algebra has no unital complex-algebra character. -/
theorem window_algebra_has_no_character (M : ℕ) [NeZero M] (hM : 1 < M) :
    IsEmpty (Matrix (ZMod M) (ZMod M) ℂ →ₐ[ℂ] ℂ) := by
  constructor
  intro character
  have hWeylImage :
      character (clockMatrix M) * character (shiftMatrix M) =
        windowRoot M * (character (shiftMatrix M) * character (clockMatrix M)) := by
    simpa [smul_eq_mul] using congrArg character (window_weyl M)
  have hProductAnnihilated :
      (1 - windowRoot M) *
          (character (clockMatrix M) * character (shiftMatrix M)) = 0 := by
    calc
      (1 - windowRoot M) *
          (character (clockMatrix M) * character (shiftMatrix M)) =
          character (clockMatrix M) * character (shiftMatrix M) -
            windowRoot M *
              (character (shiftMatrix M) * character (clockMatrix M)) := by ring
      _ = 0 := sub_eq_zero.mpr hWeylImage
  have hRootFactor : 1 - windowRoot M ≠ 0 :=
    sub_ne_zero.mpr ((windowRoot_isPrimitiveRoot M).ne_one hM).symm
  have hProductZero :
      character (clockMatrix M) * character (shiftMatrix M) = 0 :=
    (mul_eq_zero.mp hProductAnnihilated).resolve_left hRootFactor
  have hClockPower : character (clockMatrix M) ^ M = 1 := by
    simpa using congrArg character (clockMatrix_pow_card (M := M))
  have hShiftPower : character (shiftMatrix M) ^ M = 1 := by
    simpa using congrArg character (shiftMatrix_pow_card (M := M))
  rcases mul_eq_zero.mp hProductZero with hClockZero | hShiftZero
  · rw [hClockZero, zero_pow (NeZero.ne M)] at hClockPower
    exact zero_ne_one hClockPower
  · rw [hShiftZero, zero_pow (NeZero.ne M)] at hShiftPower
    exact zero_ne_one hShiftPower

end

end D5.S3.Observer.WindowCharacter
