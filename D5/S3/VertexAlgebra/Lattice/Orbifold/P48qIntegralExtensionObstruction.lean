import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero
import OmegaMath.LinearAlgebra.Eigenspace.Intertwining

/-!
An integral conformal grading obstructs an inclusion of a nonzero invariant
selection of the native P48q twisted sector.

For the branching application, a fixed left coset `xK` labels a branch with
twist `x⁻¹ g x ∈ K`. Once the branch gives a cubic twisted module for that
twist under the hypotheses of `actual_twisted_spectrum_of_order_three_isometry`,
use its conformal zero mode as the source endomorphism. The spectrum theorem
excludes every integer cast to `ℂ` as a label. An injective branch inclusion
intertwining conformal zero modes into an integrally spanned extension then
forces the branch module to vanish.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegralExtensionObstruction

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open P48qAllJetWickField (nativeField)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero_no_integer_eigenvalue)
open scoped VertexOperator

local notation "nativeLZero" =>
  HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6)

/-- An injective map intertwining the native conformal zero mode on a stable
subspace with an endomorphism spanned by its integer eigenspaces forces that
subspace to be zero. Each image vector uses only finitely many integer weights. -/
theorem eq_bot_of_integral_conformal_inclusion
    {W : Type*} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W)
    (hGraded : (⨆ n : ℤ, L.eigenspace (n : ℂ)) = ⊤)
    (S : Submodule ℂ State) (hStable : ∀ x ∈ S, nativeLZero x ∈ S)
    (f : S →ₗ[ℂ] W) (hInjective : Function.Injective f)
    (hIntertwines : ∀ x : S, f (LinearMap.restrict nativeLZero hStable x) = L (f x)) : S = ⊥ := by
  have hNoEigenvalue (n : ℤ) :
      ¬ Module.End.HasEigenvalue (LinearMap.restrict nativeLZero hStable) (n : ℂ) := by
    intro hEigenvalue
    obtain ⟨x, hx⟩ := hEigenvalue.exists_hasEigenvector
    have hne : (x : State) ≠ 0 := fun h =>
      (Module.End.hasEigenvector_iff.mp hx).2 (Subtype.ext h)
    apply totalLZero_no_integer_eigenvalue n x hne
    simpa only [LinearMap.coe_restrict_apply, Submodule.coe_smul,
      native_conformal_coeff_neg_six_eq_totalLZero] using
      congrArg (fun y : S => (y : State)) hx.apply_eq_smul
  have vanishes := Omega.LinearAlgebra.eq_zero_of_injective_intertwiner_of_no_eigenvalue
    (LinearMap.restrict nativeLZero hStable) L (fun n : ℤ => (n : ℂ))
    hGraded hNoEigenvalue f hInjective hIntertwines
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Submodule.mem_bot]
  exact congrArg (fun y : S => (y : State)) (vanishes ⟨x, hx⟩)

#print axioms eq_bot_of_integral_conformal_inclusion

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegralExtensionObstruction
