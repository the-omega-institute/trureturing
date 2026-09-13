/- GID: D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   generality: G
   mirror-B: D5/B/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Rat.Lemmas, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cubic divisibility of generalized harmonic numerators along Adamchuk's progression. -/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

open Finset

namespace D5.S3.ArithSums.AdamchukGeneralizedHarmonicThirtySevenCubeProgression

/-- The generalized harmonic sum `H(36, n)` in OEIS A116184. -/
def H (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (36 : ℕ), (1 : ℚ) / (j : ℚ) ^ n

private def L : ℕ := Nat.factorial 36

private def b (j : ℕ) : ℕ := L / j

private def N (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 36, (b j : ℤ) ^ n

private abbrev R := ZMod (37 ^ 3)

private def C (k : ℕ) : R :=
  ∑ j ∈ Finset.Icc 1 36, (b j : R) ^ 3 * ((b j : R) ^ 36) ^ k

end D5.S3.ArithSums.AdamchukGeneralizedHarmonicThirtySevenCubeProgression
