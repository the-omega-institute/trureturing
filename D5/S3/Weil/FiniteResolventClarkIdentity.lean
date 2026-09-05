/- GID: D5/S3/Weil/FiniteResolventClarkIdentity
   generality: I
   mirror-B: D5/B/S3/Weil/FiniteResolventClarkIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite paired spectra obey the resolvent-weighted Cayley--Clark identity. -/

import D5.S3.Weil.TestFunctions.CayleyMomentTransport

/-!
# Finite resolvent--Clark identity

Library-search and duplication audit trail (2026-09-05):
* Literal, spelling-variant, symbol, digest-index, generalized-body, and in-flight
  searches found no theorem identifying a finite resolvent-weighted atomic spectrum
  with its Cayley pushforward and a supplied Clark measure.
* `FiniteSpectralCayleyIdentity` treats unit-modulus points and diagonal determinants;
  it does not calculate a measure pushforward. `PositiveCayleyScaleTransport` compares
  two Cayley scales but does not give the finite atomic expansion below.
* The canonical `cayleyCircle`, `resolventDensity`, and `cayleyCompactification`
  declarations are imported rather than redeclared.
* Pinned Mathlib supplies `withDensity_sum`, `withDensity_smul_measure`,
  `withDensity_add_measure`, `dirac_withDensity`, `Measure.map_sum`,
  `Measure.map_smul`, `Measure.map_add`, and `Measure.map_dirac`.
* The source's unconditional identification with a Clark measure depends on analytic
  Clark/Herglotz machinery not yet formalized here. The final theorem therefore asks
  explicitly that the supplied Clark measure have the displayed atomic expansion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace D5.S3.Weil.FiniteResolventClarkIdentity

open D5.S3.Weil.TestFunctions.CayleyMomentTransport
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The finite real-line spectrum containing both signs of every ordinate. -/
noncomputable def pairedOrdinateMeasure
    {J : Type*} [Fintype J] (mass : J → ENNReal) (ordinate : J → Real) : Measure Real :=
  Measure.sum fun j =>
    mass j • (Measure.dirac (ordinate j) + Measure.dirac (-ordinate j))

/-- The explicit atomic circle measure obtained from the paired spectrum after
resolvent weighting and Cayley compactification. -/
noncomputable def finiteAtomicClarkMeasure
    {J : Type*} [Fintype J] (a : Real) (ha : 0 < a)
    (mass : J → ENNReal) (ordinate : J → Real) : Measure Circle :=
  Measure.sum fun j =>
    (mass j * (resolventDensity a (ordinate j) : ENNReal)) •
      (Measure.dirac (cayleyCircle a ha (ordinate j)) +
        Measure.dirac (cayleyCircle a ha (-ordinate j)))

private theorem measurable_cayley_circle (a : Real) (ha : 0 < a) :
    Measurable (cayleyCircle a ha) := by
  apply Continuous.measurable
  apply Continuous.subtype_mk
  change Continuous (fun xi : Real => cayleyCharacter a xi)
  unfold cayleyCharacter
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro xi hzero
  have himaginary := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re] at himaginary
  norm_num at himaginary
  linarith

private theorem compactification_of_paired_atom
    (a : Real) (ha : 0 < a) (mass : ENNReal) (ordinate : Real) :
    cayleyCompactification a ha
        (mass • (Measure.dirac ordinate + Measure.dirac (-ordinate))) =
      (mass * (resolventDensity a ordinate : ENNReal)) •
        (Measure.dirac (cayleyCircle a ha ordinate) +
          Measure.dirac (cayleyCircle a ha (-ordinate))) := by
  unfold cayleyCompactification
  rw [MeasureTheory.withDensity_smul_measure,
    MeasureTheory.withDensity_add_measure]
  simp only [MeasureTheory.dirac_withDensity, Measure.map_smul,
    Measure.map_add _ _ (measurable_cayley_circle a ha), Measure.map_dirac,
    resolventDensity, neg_sq, smul_add, smul_smul]

/-- Resolvent weighting and Cayley pushforward send every finite paired ordinate
spectrum to the displayed atomic circle measure, with the exact resolvent mass. -/
theorem finite_atomic_cayley_pushforward
    {J : Type*} [Fintype J] (a : Real) (ha : 0 < a)
    (mass : J → ENNReal) (ordinate : J → Real) :
    cayleyCompactification a ha (pairedOrdinateMeasure mass ordinate) =
      finiteAtomicClarkMeasure a ha mass ordinate := by
  unfold cayleyCompactification pairedOrdinateMeasure finiteAtomicClarkMeasure
  rw [MeasureTheory.withDensity_sum]
  rw [Measure.map_sum (measurable_cayley_circle a ha).aemeasurable]
  apply congrArg Measure.sum
  funext j
  exact compactification_of_paired_atom a ha (mass j) (ordinate j)

/-- At the natural half scale, the resolvent compactification, its explicit finite
atomic Li measure, and any Clark measure with that expansion are the same measure. -/
theorem finite_resolvent_clark_identity
    {J : Type*} [Fintype J] (mass : J → ENNReal) (ordinate : J → Real)
    (clarkMeasure : Measure Circle)
    (hclark : clarkMeasure =
      finiteAtomicClarkMeasure (1 / 2 : Real) (by norm_num) mass ordinate) :
    cayleyCompactification (1 / 2 : Real) (by norm_num)
        (pairedOrdinateMeasure mass ordinate) =
      finiteAtomicClarkMeasure (1 / 2 : Real) (by norm_num) mass ordinate ∧
    finiteAtomicClarkMeasure (1 / 2 : Real) (by norm_num) mass ordinate =
      clarkMeasure := by
  exact ⟨finite_atomic_cayley_pushforward (1 / 2 : Real) (by norm_num)
    mass ordinate, hclark.symm⟩

#print axioms pairedOrdinateMeasure
#print axioms finiteAtomicClarkMeasure
#print axioms finite_atomic_cayley_pushforward
#print axioms finite_resolvent_clark_identity

end D5.S3.Weil.FiniteResolventClarkIdentity
