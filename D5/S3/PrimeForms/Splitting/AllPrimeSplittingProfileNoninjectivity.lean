/- GID: D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct forms share every prime split type; zero-index cases are explicit. -/

import D5.S3.PrimeForms.Splitting.EqualDiscriminantSplittingPortrait

/- Library-search audit trail (2026-08-25):
   * Current-tree searches found the canonical `BinaryQuadraticForm`, its discriminant,
     and `equal_discriminant_splitting_portrait`; they found no explicit distinct-form
     witness together with a profile-separation contrast.
   * Pinned Mathlib defines `QuadraticForm R M` as `QuadraticMap R M R`; its discriminant
     requires a basis. Reusing the repository's coefficient carrier avoids a duplicate
     coordinate conversion and keeps the proof below at the intended interface level.
   * Pinned Mathlib's `jacobiSym` is total on natural indices, takes only `-1`, `0`, `1`,
     and agrees with the Legendre symbol at primes. No local-equivalence theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.AllPrimeSplittingProfileNoninjectivity

open D5.S3.PrimeForms.EisensteinDiscriminant
open D5.S3.PrimeForms.Splitting.EqualDiscriminantSplittingPortrait

/-- Finite data returned by the selected splitting interface. -/
inductive DiscriminantSplittingType where
  | inert
  | ramified
  | split
  deriving DecidableEq, Fintype, Repr

/-- The chosen profile reads the Jacobi symbol of the form discriminant.

At a prime this is the Legendre split/ramified/inert trichotomy. The definition is total
at nonprime indices solely so that its degenerate behavior can be audited. It deliberately
forgets all coefficients beyond the discriminant and makes no local-equivalence claim. -/
def discriminantSplittingType (Q : BinaryQuadraticForm) (p : Nat) :
    DiscriminantSplittingType :=
  if jacobiSym Q.discriminant p = -1 then .inert
  else if jacobiSym Q.discriminant p = 0 then .ramified
  else .split

/-- Equality of the selected finite splitting data at every prime-labelled index. -/
def SameAllPrimeSplittingProfile (Q Q' : BinaryQuadraticForm) : Prop :=
  ∀ p : Nat, p.Prime → discriminantSplittingType Q p = discriminantSplittingType Q' p

/-- The reference form `x^2 + y^2`. -/
def collisionFormOne : BinaryQuadraticForm := ⟨1, 0, 1⟩

/-- The distinct form `x^2 + 2xy + 2y^2` with the same discriminant `-4`. -/
def collisionFormTwo : BinaryQuadraticForm := ⟨1, 2, 2⟩

/-- A form of discriminant one, used by the positive discrimination control. -/
def splitControlForm : BinaryQuadraticForm := ⟨1, 1, 0⟩

/-- The zero binary quadratic form. -/
def zeroForm : BinaryQuadraticForm := ⟨0, 0, 0⟩

/-- Two unequal global forms have the same selected splitting type at every prime. -/
theorem all_prime_splitting_profile_not_injective :
    collisionFormOne ≠ collisionFormTwo ∧
      SameAllPrimeSplittingProfile collisionFormOne collisionFormTwo := by
  constructor
  · intro hEqual
    have hCoefficient := congrArg BinaryQuadraticForm.b hEqual
    norm_num [collisionFormOne, collisionFormTwo] at hCoefficient
  · intro p _
    have hDiscriminant :
        collisionFormOne.discriminant = collisionFormTwo.discriminant := by
      norm_num [collisionFormOne, collisionFormTwo, BinaryQuadraticForm.discriminant]
    have hSymbol :=
      equal_discriminant_splitting_portrait
        collisionFormOne collisionFormTwo hDiscriminant p
    simp only [discriminantSplittingType]
    rw [hSymbol]

#print axioms all_prime_splitting_profile_not_injective

/-- The profile is not constant: two forms are separated at the prime three. -/
theorem splitting_profile_distinguishes_some_global_forms :
    splitControlForm ≠ zeroForm ∧
      ∃ p : Nat, p.Prime ∧
        discriminantSplittingType splitControlForm p ≠
          discriminantSplittingType zeroForm p := by
  constructor
  · intro hEqual
    have hCoefficient := congrArg BinaryQuadraticForm.b hEqual
    norm_num [splitControlForm, zeroForm] at hCoefficient
  · refine ⟨3, by norm_num, ?_⟩
    have hSplitDiscriminant : splitControlForm.discriminant = 1 := by
      norm_num [splitControlForm, BinaryQuadraticForm.discriminant]
    have hZeroDiscriminant : zeroForm.discriminant = 0 := by
      norm_num [zeroForm, BinaryQuadraticForm.discriminant]
    have hSplitSymbol : jacobiSym splitControlForm.discriminant 3 = 1 := by
      simp [hSplitDiscriminant]
    have hZeroSymbol : jacobiSym zeroForm.discriminant 3 = 0 := by
      rw [hZeroDiscriminant]
      exact jacobiSym.zero_left (by norm_num)
    simp [discriminantSplittingType, hSplitSymbol, hZeroSymbol]

#print axioms splitting_profile_distinguishes_some_global_forms

/-- The nonzero reference form realizes all three readings at explicit prime indices. -/
theorem reference_form_realizes_all_splitting_types :
    discriminantSplittingType collisionFormOne 3 = .inert ∧
      discriminantSplittingType collisionFormOne 2 = .ramified ∧
        discriminantSplittingType collisionFormOne 5 = .split := by
  have hDiscriminant : collisionFormOne.discriminant = -4 := by
    norm_num [collisionFormOne, BinaryQuadraticForm.discriminant]
  have hThree : jacobiSym collisionFormOne.discriminant 3 = -1 := by
    rw [hDiscriminant, jacobiSym.mod_left]
    norm_num [jacobiSym.at_two, ZMod.χ₈_nat_eq_if_mod_eight]
  have hTwo : jacobiSym collisionFormOne.discriminant 2 = 0 := by
    rw [hDiscriminant, jacobiSym.mod_left]
    simpa using jacobiSym.zero_left (by norm_num : 1 < 2)
  have hFive : jacobiSym collisionFormOne.discriminant 5 = 1 := by
    rw [hDiscriminant, jacobiSym.mod_left]
    norm_num
  simp [discriminantSplittingType, hThree, hTwo, hFive]

#print axioms reference_form_realizes_all_splitting_types

/-- The zero form is ramified at every index strictly above one, hence at every prime. -/
theorem zero_form_is_ramified_above_one (p : Nat) (hp : 1 < p) :
    discriminantSplittingType zeroForm p = .ramified := by
  have hDiscriminant : zeroForm.discriminant = 0 := by
    norm_num [zeroForm, BinaryQuadraticForm.discriminant]
  have hSymbol : jacobiSym zeroForm.discriminant p = 0 := by
    rw [hDiscriminant]
    exact jacobiSym.zero_left hp
  simp [discriminantSplittingType, hSymbol]

#print axioms zero_form_is_ramified_above_one

/-- The lower bound in the preceding zero-form conclusion cannot be dropped: totalized
indices zero and one are both read as split rather than ramified. -/
theorem index_above_one_is_necessary_for_zero_form_ramification :
    discriminantSplittingType zeroForm 0 = .split ∧
      discriminantSplittingType zeroForm 1 = .split := by
  simp [discriminantSplittingType, zeroForm, BinaryQuadraticForm.discriminant]

#print axioms index_above_one_is_necessary_for_zero_form_ramification

/- Assumption and degeneracy audit:
   * The two noninjectivity/control theorems are closed and have no typeclass assumptions.
   * The prime proof in `SameAllPrimeSplittingProfile` is only an interface-domain label;
     equal discriminants actually give equality at every natural index.
   * Primality is not load-bearing for zero-form ramification, so its theorem is stated with
     the weaker condition `1 < p`. That hypothesis feeds `jacobiSym.zero_left`; the named
     theorem immediately below supplies both excluded counterexamples.
   * There is no varying carrier type, map, or size parameter, so empty/singleton carriers,
     identity maps, and `n = 0` are inapplicable. The relevant constant zero object and index
     zero are tested above, and the positive control proves the profile itself is not constant.
-/

end D5.S3.PrimeForms.Splitting.AllPrimeSplittingProfileNoninjectivity
