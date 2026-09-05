/- GID: D5/S3/Weil/Separator/UnconditionalExplicitFormula
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/UnconditionalExplicitFormula
   mirror-E: none(waiver:kernel-verified-identities-and-reduction-only)
   anchors: []
   digest: Remove both convergence hypotheses and isolate the small-support Poincare target. -/

import D5.S3.Weil.Separator.ArchimedeanConvergence
import D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
import D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable

/-!
# Unconditional explicit formula and energy identity

The frozen archimedean and symmetric convergence theorems discharge the two
convergence premises of the repository's frozen explicit formula and
prime--archimedean energy identity. The small-support result then removes the
finite prime contribution when the support scale lies below the first prime
power.

The analytic identities remain relative to supplied `ZeroData`; existence is
not asserted, and M1-b remains open. The test functions are the repository's
`WeilTestFunction`. The final theorem is only a reduction to an archimedean
inequality, not a proof of that open inequality or of the Riemann hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Weil.Separator.UnconditionalExplicitFormula

open MeasureTheory Set
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Separator.ArchimedeanConvergence
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- The classical explicit formula for every repository Weil test function,
with both convergence witnesses supplied by frozen repository theorems. -/
theorem explicitFormula_unconditional (Z : ZeroData) (g : WeilTestFunction) :
    zeroSum Z g (symmetricConvergent_of_zeroData Z g) =
      poleTerm g - primeTerm g +
        archimedeanTerm g (archimedeanConvergent_of_weilTestFunction g) := by
  exact D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.weil_explicit_formula Z g
    (symmetricConvergent_of_zeroData Z g)
    (archimedeanConvergent_of_weilTestFunction g)

/-- The frozen prime--archimedean energy decomposition, with its zero-side and
archimedean convergence premises discharged for every repository Weil test
function. -/
theorem energyIdentity_unconditional (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L) :
    zeroSum Z (convolutionSquare f)
        (symmetricConvergent_of_zeroData Z (convolutionSquare f)) =
      ((2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
        archimedeanJumpEnergy f + arithmeticJumpEnergy L f -
        (2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f : ℝ) : ℂ) := by
  exact (prime_archimedean_energy_identity Z f L hSupport
    (symmetricConvergent_of_zeroData Z (convolutionSquare f))
    (archimedeanConvergent_of_weilTestFunction (convolutionSquare f))).1

/-- Below the first prime power, the finite set indexing the arithmetic jump
energy is empty. -/
theorem activePrimePowers_eq_empty_of_exp_lt_two (L : ℝ)
    (hL : Real.exp (2 * L) < 2) :
    activePrimePowers L = ∅ := by
  have hfloor : ⌊Real.exp (2 * L)⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_pos (2 * L)).le).2 hL
  apply Finset.eq_empty_of_forall_notMem
  intro n hn
  rw [activePrimePowers, Finset.mem_filter, Finset.mem_Ioc] at hn
  have hn_one : n = 1 := by omega
  subst n
  exact hn.2 ArithmeticFunction.vonMangoldt_apply_one

/-- If the support scale lies below the first prime power, the full
prime--archimedean Poincare inequality is equivalent to its reduced
archimedean part. This theorem does not assert the reduced inequality. -/
theorem smallSupport_poincare_reduction (f : WeilTestFunction) (L : ℝ)
    (hL : Real.exp (2 * L) < 2) :
    ((2 * totalPrimeWeight L - archimedeanConstant) * l2Mass f ≤
        2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
          archimedeanJumpEnergy f + arithmeticJumpEnergy L f) ↔
      (-archimedeanConstant) * l2Mass f ≤
        2 * Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) +
          archimedeanJumpEnergy f := by
  have hactive : activePrimePowers L = ∅ :=
    activePrimePowers_eq_empty_of_exp_lt_two L hL
  simp [totalPrimeWeight, arithmeticJumpEnergy, hactive]

-- The conditional zero-data domain is inhabited whenever zero data is supplied.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

-- The repository test-function domain has a canonical inhabitant.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

-- The support and small-scale hypotheses are jointly satisfiable.
example :
    ∃ (f : WeilTestFunction) (L : ℝ),
      tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-L) L ∧ Real.exp (2 * L) < 2 := by
  let f : WeilTestFunction :=
    { toFun := fun _ => 0
      contDiff' := contDiff_const
      hasCompactSupport' := by simp [HasCompactSupport]
      even' := by simp }
  refine ⟨f, 0, ?_, ?_⟩
  · change tsupport (fun _ : ℝ => (0 : ℂ)) ⊆ Set.Icc (-0) 0
    simp
  · norm_num

#print axioms explicitFormula_unconditional
#print axioms energyIdentity_unconditional
#print axioms activePrimePowers_eq_empty_of_exp_lt_two
#print axioms smallSupport_poincare_reduction

end

end D5.S3.Weil.Separator.UnconditionalExplicitFormula
