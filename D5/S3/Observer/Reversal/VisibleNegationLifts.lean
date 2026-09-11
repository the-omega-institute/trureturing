/- GID: D5/S3/Observer/Reversal/VisibleNegationLifts
   generality: G
   mirror-B: D5/B/S3/Observer/Reversal/VisibleNegationLifts
   mirror-E: none(waiver:symbolic-linear-classification)
   anchors: []
   utility: none
   digest: All involutive lifts of visible negation are classified by idempotents in the observation kernel. -/

import D5.S0.Conventions.InvolutionDecomposition

/-!
# Involutive lifts of a visible minus sign

The canonical half-sum is the existing involution decomposition, not a new
parity convention. The content here classifies *all* linear state involutions
with the same observed minus sign. No finite-dimensional or orthogonality
hypothesis is imposed. The classification is algebraic, not a physical
realizability or time-reversal theorem.

Source: NS_OBSERVER_DYNAMICS_RH_THEORY, Proposition 1.2. Repository-first search
read InvolutionDecomposition and InvolutionDecompositionUniqueness. The former
supplies the fixed-part law used below; neither classifies observation-kernel
lifts. Mathlib's LinearMap operations and module normalization are reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Reversal.VisibleNegationLifts

open D5.S0.Conventions.InvolutionDecomposition

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- The existing canonical fixed summand, packaged as a linear map. -/
def fixedPart (R : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (2 : ℝ)⁻¹ • (LinearMap.id + R)

private theorem fixedPart_fixed (R : E →ₗ[ℝ] E)
    (hR : Function.Involutive R) (x : E) :
    R (fixedPart R x) = fixedPart R x := by
  exact (involution_even_odd_decomposition R hR x).2.1

/-- The canonical fixed summand is an idempotent. -/
theorem fixedPart_idempotent (R : E →ₗ[ℝ] E)
    (hR : Function.Involutive R) (x : E) :
    fixedPart R (fixedPart R x) = fixedPart R x := by
  change (2 : ℝ)⁻¹ • (fixedPart R x + R (fixedPart R x)) = _
  rw [fixedPart_fixed R hR x]
  module

/-- A visible minus sign annihilates the entire fixed summand. -/
theorem fixedPart_in_observation_kernel (P : E →ₗ[ℝ] F) (R : E →ₗ[ℝ] E)
    (hvisible : ∀ x, P (R x) = -P x) (x : E) :
    P (fixedPart R x) = 0 := by
  change P ((2 : ℝ)⁻¹ • (x + R x)) = 0
  rw [map_smul, map_add, hvisible, add_neg_cancel, smul_zero]

/-- Every involution lifting the observed minus sign has a hidden
idempotent representation. The converse constructs the involution law;
uniqueness is the separate theorem below. -/
theorem visible_negation_iff_hidden_idempotent
    (P : E →ₗ[ℝ] F) (R : E →ₗ[ℝ] E) :
    (Function.Involutive R ∧ ∀ x, P (R x) = -P x) ↔
      ∃ H : E →ₗ[ℝ] E,
        (∀ x, H (H x) = H x) ∧
        (∀ x, P (H x) = 0) ∧
        (∀ x, R x = (2 : ℝ) • H x - x) := by
  constructor
  · rintro ⟨hR, hvisible⟩
    refine ⟨fixedPart R, fixedPart_idempotent R hR,
      fixedPart_in_observation_kernel P R hvisible, ?_⟩
    intro x
    change R x = (2 : ℝ) • ((2 : ℝ)⁻¹ • (x + R x)) - x
    module
  · rintro ⟨H, hH, hkernel, hformula⟩
    constructor
    · intro x
      rw [hformula (R x), hformula x, map_sub, map_smul, hH x]
      module
    · intro x
      rw [hformula x, map_sub, map_smul, hkernel x, smul_zero, zero_sub]

/-- The hidden idempotent is determined by the full involution, even though
it is invisible to the original observation. -/
theorem hidden_idempotent_unique (R H : E →ₗ[ℝ] E)
    (hformula : ∀ x, R x = (2 : ℝ) • H x - x) : H = fixedPart R := by
  ext x
  change H x = (2 : ℝ)⁻¹ • (x + R x)
  rw [hformula x]
  module

/-- Reverse the retained subspace and preserve the complementary subspace. -/
def visibleReflection (P : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  LinearMap.id - (2 : ℝ) • P

/-- A projection induces a genuine state involution with visible action -I. -/
theorem visibleReflection_spec (P : E →ₗ[ℝ] E)
    (hP : ∀ x, P (P x) = P x) :
    Function.Involutive (visibleReflection P) ∧
      (∀ x, P (visibleReflection P x) = -P x) ∧
      (∀ x, P x = 0 → visibleReflection P x = x) := by
  constructor
  · intro x
    change (x - (2 : ℝ) • P x) - (2 : ℝ) • P (x - (2 : ℝ) • P x) = x
    rw [map_sub, map_smul, hP x]
    module
  constructor
  · intro x
    change P (x - (2 : ℝ) • P x) = -P x
    rw [map_sub, map_smul, hP x]
    module
  · intro x hx
    change x - (2 : ℝ) • P x = x
    rw [hx, smul_zero, sub_zero]

#print axioms fixedPart
#print axioms fixedPart_idempotent
#print axioms fixedPart_in_observation_kernel
#print axioms visible_negation_iff_hidden_idempotent
#print axioms hidden_idempotent_unique
#print axioms visibleReflection
#print axioms visibleReflection_spec

end D5.S3.Observer.Reversal.VisibleNegationLifts
