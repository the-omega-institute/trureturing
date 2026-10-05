/- GID: D5/S1/Words/Palindromes/PeriodDoubling/KernelSpan
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/KernelSpan
   mirror-E: none(waiver:finite-kernel-span-telescoping)
   anchors: []
   utility: none
   digest: The literal binary kernel records all power-of-two residue subsequences. -/



import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

open scoped BigOperators

/-- All subsequences obtained from every binary-kernel address. -/
def twoKernel {A : Type*} (f : ℕ → A) : Set (ℕ → A) :=
  {g | ∃ e r : ℕ, r < 2 ^ e ∧ g = fun n => f (2 ^ e * n + r)}


end D5.S1.Words.Palindromes.PeriodDoubling
