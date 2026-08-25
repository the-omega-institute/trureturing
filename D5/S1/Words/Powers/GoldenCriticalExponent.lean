/- GID: D5/S1/Words/Powers/GoldenCriticalExponent
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer golden power-freeness begins exactly at exponent four. -/

import Mathlib
import D5.S1.Words.Powers.GoldenFourthPower

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-16, pinned repository and pinned mathlib):
   Repository declarations reused:
   * `GoldenFourthPower.lean` supplies `IsGoldenPowerFactor`,
     `golden_word_fourth_power_free`, and `golden_cube_is_power_factor`.
   * `WordPower.lean` supplies `length_wordPower` and `wordPower_getElem?`.
   * `GoldenFactorComplexity.lean` supplies `goldenFactor`.
   Pinned mathlib declarations reused:
   * `Mathlib/Data/List/Basic.lean:623` supplies `List.ext_getElem?'`.
   * `Mathlib/Order/Bounds/Basic.lean:411` supplies `isLeast_Ici`.
   * A full search below `Mathlib/Combinatorics` (192 files) for
     `power[- ]?free|PowerFree|criticalExponent|Sturmian` returned no matches,
     so pinned mathlib has no directly reusable combinatorics-on-words result.
   Repository search result:
   * Searches below `D5` for power-freeness, critical exponents, and
     `IsGoldenPowerFactor` found the frozen fourth-power theorem and cube
     witness, but no all-exponents or exponent-set characterization.
   Results proved locally rather than reused:
   * The private pointwise formula for `goldenFactor` is reproved below because
     both existing versions are private.
   * Prefix descent, all `k >= 4` power-freeness, the exact exponent set, and
     its least element are proved in this file.
   Premise audit:
   * Prefix descent needs no `u != []`: for `u = []`, both powers and both
     length-zero golden factors are empty.
   * Power-freeness must exclude `u = []`: for every `k` and `i`,
     `IsGoldenPowerFactor k [] i` holds because both sides are empty.
   No third-party ecosystem search was needed after the exact repository and
   pinned-mathlib components above were identified.
-/

namespace D5.S1.Words.Powers.GoldenCriticalExponent

open D5.S1.Words

private theorem goldenFactor_getElem? {n i x : Nat} (hx : x < n) :
    (goldenFactor n i)[x]? = some (goldenWord (i + x)) := by
  rw [goldenFactor, List.getElem?_eq_getElem (by simpa using hx)]
  simp

/-- Every shorter integer power is a prefix power factor of a longer one. -/
theorem isGoldenPowerFactor_of_le {j k : Nat} {u : List Bool} {i : Nat}
    (hjk : j ≤ k) (h : IsGoldenPowerFactor k u i) : IsGoldenPowerFactor j u i := by
  unfold IsGoldenPowerFactor at h ⊢
  apply List.ext_getElem?'
  intro m hm
  have hmj : m < j * u.length := by
    simpa [goldenFactor, length_wordPower] using hm
  have hmk : m < k * u.length :=
    lt_of_lt_of_le hmj (Nat.mul_le_mul_right u.length hjk)
  have hpoint := congrArg (fun w : List Bool => w[m]?) h
  rw [goldenFactor_getElem? hmk, wordPower_getElem? k u m hmk] at hpoint
  rw [goldenFactor_getElem? hmj, wordPower_getElem? j u m hmj]
  exact hpoint

/-- No nonempty word occurs `k` consecutive times in the golden word when `4 ≤ k`. -/
theorem golden_word_power_free_of_four_le {k : Nat} (hk : 4 ≤ k)
    (i : Nat) (u : List Bool) (hu : u ≠ []) : ¬ IsGoldenPowerFactor k u i := by
  intro h
  exact golden_word_fourth_power_free i u hu (isGoldenPowerFactor_of_le hk h)

/-- The integer exponents for which the golden word is power free are exactly `k ≥ 4`. -/
theorem golden_power_free_exponent_set :
    {k : Nat | ∀ u : List Bool, u ≠ [] → ∀ i : Nat, ¬ IsGoldenPowerFactor k u i} =
      Set.Ici 4 := by
  apply Set.Subset.antisymm
  · intro k hk
    change 4 ≤ k
    by_contra hnot
    have hkle : k ≤ 3 := by
      omega
    interval_cases k
    · exact (hk [true] (by simp) 0) (by
        simp [IsGoldenPowerFactor, goldenFactor, wordPower])
    · apply (hk [true] (by simp) 0)
      simp [IsGoldenPowerFactor, goldenFactor, wordPower, goldenWord_zero]
    · exact (hk [true, false, true] (by simp) 5)
        (isGoldenPowerFactor_of_le (by omega) golden_cube_is_power_factor)
    · exact (hk [true, false, true] (by simp) 5) golden_cube_is_power_factor
  · intro k hk u hu i
    exact golden_word_power_free_of_four_le hk i u hu

/-- Four is the least integer exponent at which the golden word is power free. -/
theorem golden_critical_exponent_isLeast :
    IsLeast
      {k : Nat | ∀ u : List Bool, u ≠ [] → ∀ i : Nat, ¬ IsGoldenPowerFactor k u i} 4 := by
  rw [golden_power_free_exponent_set]
  exact isLeast_Ici

#print axioms isGoldenPowerFactor_of_le
#print axioms golden_word_power_free_of_four_le
#print axioms golden_power_free_exponent_set
#print axioms golden_critical_exponent_isLeast

end D5.S1.Words.Powers.GoldenCriticalExponent
