/- GID: D5/S3/Weil/ZetaBridge/FiniteReflectionCompatibleWeilInterpolation
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteReflectionCompatibleWeilInterpolation
   mirror-E: none(waiver:finite-interpolation-extension)
   anchors: []
   digest: Interpolate arbitrary finite reflection-compatible zero data by reusing the existing sign-separated even interpolation theorem. -/

import D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare

/-!
# Finite reflection-compatible Weil interpolation

Library-first extension of `even_weilTestFunction_finite_interpolation`.
The existing single-orbit proof already contains the sign quotient
`reflectionRep`, its frequency separation theorem, and injectivity of gamma.
Those helpers are exposed, without changing their proofs, in the same PR.
Here arbitrary finite data constant on reflection pairs is transported through
that quotient. Neither a new test-function bundle nor a new interpolation
existence assumption is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.EvenTestFunctionFiniteInterpolation
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare

/-- The already existing reflection representative is unchanged by reflection. -/
theorem reflectionRep_reflection (Z : ZeroData) (j : ℕ) :
    reflectionRep Z (Z.reflection j) = reflectionRep Z j := by
  simp [reflectionRep, Nat.min_comm]

/-- Reflection-invariant data descends to the selected sign representative. -/
theorem reflectionRep_value (Z : ZeroData) (a : ℕ → ℂ)
    (ha : ∀ j, a (Z.reflection j) = a j) (j : ℕ) :
    a (reflectionRep Z j) = a j := by
  by_cases h : j ≤ Z.reflection j
  · rw [reflectionRep, Nat.min_eq_left h]
  · rw [reflectionRep, Nat.min_eq_right (Nat.le_of_not_ge h), ha]

/-- Every finite reflection-compatible assignment is realized by an actual
smooth compactly supported even Weil test. The finite index set need not be
reflection closed. Compatibility is imposed on the assignment, and the
existing sign-separated interpolation theorem supplies the test. -/
theorem even_weil_interpolation_on_finite_indices
    (Z : ZeroData) (E : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ j, a (Z.reflection j) = a j) :
    ∃ g : WeilTestFunction, ∀ j ∈ E,
      fourierLaplace g (Z.gamma j) = a j := by
  classical
  let S : Finset ℂ := E.image (fun j => Z.gamma (reflectionRep Z j))
  let chosen (z : {z : ℂ // z ∈ S}) : ℕ :=
    Classical.choose (Finset.mem_image.mp z.property)
  have chosen_spec (z : {z : ℂ // z ∈ S}) :
      Z.gamma (reflectionRep Z (chosen z)) = z.1 :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).2
  let values (z : {z : ℂ // z ∈ S}) : ℂ :=
    a (reflectionRep Z (chosen z))
  have hsep : ∀ ⦃z w : ℂ⦄,
      z ∈ S → w ∈ S → z ≠ w → z ≠ -w :=
    reflectionRep_image_sep Z E
  obtain ⟨g, hg⟩ :=
    even_weilTestFunction_finite_interpolation S hsep values
  have hrep (j : ℕ) (hj : j ∈ E) :
      fourierLaplace g (Z.gamma (reflectionRep Z j)) = a j := by
    let z : {z : ℂ // z ∈ S} :=
      ⟨Z.gamma (reflectionRep Z j), Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    have hread := hg z
    have heq : reflectionRep Z (chosen z) = reflectionRep Z j :=
      gamma_injective Z (chosen_spec z)
    change fourierLaplace g (Z.gamma (reflectionRep Z j)) =
      a (reflectionRep Z (chosen z)) at hread
    rw [heq, reflectionRep_value Z a ha j] at hread
    exact hread
  refine ⟨g, ?_⟩
  intro j hj
  rcases reflectionRep_freq Z j with hsame | hneg
  · rw [← hsame]
    exact hrep j hj
  · calc
      fourierLaplace g (Z.gamma j) =
          fourierLaplace g (-Z.gamma j) :=
        (fourierLaplace_neg g (Z.gamma j)).symm
      _ = fourierLaplace g (Z.gamma (reflectionRep Z j)) := by rw [hneg]
      _ = a j := hrep j hj

/-- A simultaneous unit peak exists on every finite zero set, including sets
containing several unrelated off-line orbits. -/
theorem exists_even_weil_finite_unit_peak (Z : ZeroData) (E : Finset ℕ) :
    ∃ b : WeilTestFunction, ∀ j ∈ E,
      fourierLaplace b (Z.gamma j) = 1 := by
  exact even_weil_interpolation_on_finite_indices Z E (fun _ => 1)
    (fun _ => rfl)

#print axioms even_weil_interpolation_on_finite_indices
#print axioms exists_even_weil_finite_unit_peak

end D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
