/- GID: D5/S1/Digit/PrimeAxis/NormalizedMotion
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/NormalizedMotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated normalized motion stays canonical and decodes to a product of steps. -/

import D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique

namespace D5.S1.Digit.PrimeAxis.NormalizedMotion

open D5.S1.Digit
open D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique

/- The source clause reads the motion as a state step: the accumulator advances by the
control, and the encoding advances by adding the control's code and renormalizing, so that
motion never produces an illegal encoding.

One step of that is `normalizedPrimeAxisAdd`, already in the repository, and its uniqueness
is `normalized_prime_axis_add_unique`. What did not exist is the iteration: a trajectory of
states, the statement that every state along it is canonical, and the decoder's behaviour
along it. Canonicity is structural here, since `PrimeAxisTable` carries it as a field; the
content is that the decoder turns the whole trajectory into a product. -/

/-- The state after `t` steps of motion under a constant control. -/
noncomputable def motion (z u : PrimeAxisTable) : ℕ → PrimeAxisTable
  | 0 => z
  | (t + 1) => normalizedPrimeAxisAdd (motion z u t) u

/-- Motion never leaves the canonical encodings: every reachable state is a table, and a
table is canonical on every axis by construction. -/
theorem motion_canonical (z u : PrimeAxisTable) (t : ℕ) (p : PrimeAxis) :
    CanonicalRaw ((motion z u t).digits p) :=
  (motion z u t).canonical p

/-- One step multiplies the decoded value by the control's decoded value. -/
theorem decode_motion_succ (z u : PrimeAxisTable) (t : ℕ) :
    decodePrimeAxisTable (motion z u (t + 1)) =
      decodePrimeAxisTable (motion z u t) * decodePrimeAxisTable u := by
  exact (prime_axis_addition_spec (motion z u t) u).2

/-- Along the whole trajectory the decoder is the initial value times a power of the
control: motion in the encoding is multiplication in the value. -/
theorem decode_motion (z u : PrimeAxisTable) :
    ∀ t : ℕ, decodePrimeAxisTable (motion z u t) =
      decodePrimeAxisTable z * decodePrimeAxisTable u ^ t := by
  intro t
  induction t with
  | zero => simp [motion]
  | succ n ih => rw [decode_motion_succ, ih, pow_succ]; ring

end D5.S1.Digit.PrimeAxis.NormalizedMotion
