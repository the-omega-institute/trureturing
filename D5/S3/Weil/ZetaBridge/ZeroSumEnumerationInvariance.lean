/- GID: D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Symmetric zero sums and their limits are independent of the zero enumeration. -/

import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZeroSum

open Filter
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

noncomputable section

private def enumerationEquiv (Z Z' : ZeroData) : ℕ ≃ ℕ :=
  (zeroEquiv Z).trans (zeroEquiv Z').symm

private theorem enumerationEquiv_zero (Z Z' : ZeroData) (n : ℕ) :
    Z'.zero (enumerationEquiv Z Z' n) = Z.zero n := by
  change ((zeroEquiv Z') ((zeroEquiv Z').symm (zeroEquiv Z n))).1 = Z.zero n
  rw [Equiv.apply_symm_apply]
  rfl

private theorem enumerationEquiv_gamma (Z Z' : ZeroData) (n : ℕ) :
    Z'.gamma (enumerationEquiv Z Z' n) = Z.gamma n := by
  unfold ZeroData.gamma
  rw [enumerationEquiv_zero]

private theorem enumerationEquiv_multiplicity (Z Z' : ZeroData) (n : ℕ) :
    Z'.multiplicity (enumerationEquiv Z Z' n) = Z.multiplicity n := by
  rw [multiplicity_eq_zeroMult Z', multiplicity_eq_zeroMult Z,
    enumerationEquiv_zero]

/-- A finite symmetric zero sum is independent of the duplicate-free exhaustive enumeration. -/
theorem truncatedZeroSum_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction) (T : ℝ) :
    truncatedZeroSum Z g T = truncatedZeroSum Z' g T := by
  unfold truncatedZeroSum
  refine Finset.sum_equiv (enumerationEquiv Z Z') ?_ ?_
  · intro n
    simp only [ZeroData.mem_symmetricIndices]
    rw [enumerationEquiv_gamma]
  · intro n _hn
    unfold zeroSummand
    rw [enumerationEquiv_multiplicity, enumerationEquiv_gamma]

/-- Symmetric convergence is independent of the zero enumeration. -/
theorem symmetricConvergent_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction) :
    SymmetricConvergent Z g ↔ SymmetricConvergent Z' g := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa only [truncatedZeroSum_enum_invariant Z Z' g] using hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa only [truncatedZeroSum_enum_invariant Z Z' g] using hz

/-- The symmetric zero-sum value is independent of both enumeration and convergence witness. -/
theorem zeroSum_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction)
    (h : SymmetricConvergent Z g) (h' : SymmetricConvergent Z' g) :
    zeroSum Z g h = zeroSum Z' g h' := by
  apply zeroSum_eq_of_tendsto Z g h
  simpa only [truncatedZeroSum_enum_invariant Z Z' g] using
    truncatedZeroSum_tendsto Z' g h'

-- The conditional convergence hypotheses are jointly witnessable by their binders.
example (Z Z' : ZeroData) (g : WeilTestFunction)
    (h : SymmetricConvergent Z g) (h' : SymmetricConvergent Z' g) :
    SymmetricConvergent Z g ∧ SymmetricConvergent Z' g :=
  ⟨h, h'⟩

-- The supplied zero-data domain is inhabited independently of the conclusions.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

-- The test-function domain has a frozen canonical inhabitant.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms truncatedZeroSum_enum_invariant
#print axioms symmetricConvergent_enum_invariant
#print axioms zeroSum_enum_invariant

end

end D5.S3.Weil.ZeroSum
