import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero

/-!
A finite sum of integral eigenspaces in an extension cannot contain the
image of a nonzero invariant selection of the native P48q twisted sector.
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
  classical
  let E (n : ℤ) := L.eigenspace (n : ℂ)
  let shift (n : ℤ) : Module.End ℂ W := L - (n : ℂ) • LinearMap.id
  have shift_mem (n : ℤ) (grades : Finset ℤ) {v : W} (hv : v ∈ grades.sup E) :
      shift n v ∈ grades.sup E := by
    refine (Finset.sup_le_iff.mpr ?_ : grades.sup E ≤ (grades.sup E).comap (shift n)) hv
    intro m hm w hw
    change shift n w ∈ grades.sup E
    have heigen := Module.End.mem_eigenspace_iff.mp hw
    have hw' : w ∈ grades.sup E := (Finset.le_sup (f := E) hm) hw
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, heigen]
    exact (grades.sup E).sub_mem
      ((grades.sup E).smul_mem (m : ℂ) hw') ((grades.sup E).smul_mem (n : ℂ) hw')
  -- At each step the shifted image loses one weight. The corresponding
  -- shift on the source has zero kernel by the native spectrum theorem.
  have vanishes (grades : Finset ℤ) : ∀ x : S, f x ∈ grades.sup E → x = 0 := by
    induction grades using Finset.induction_on with
    | empty =>
      intro x hx
      apply hInjective
      simpa using hx
    | insert n grades _ ih =>
      intro x hx
      rw [Finset.sup_insert] at hx
      obtain ⟨v, hv, w, hw, hsum⟩ := Submodule.mem_sup.mp hx
      have hvzero : shift n v = 0 := by
        simpa [shift, sub_eq_zero] using (Module.End.mem_eigenspace_iff.mp hv)
      have hshift : shift n (f x) ∈ grades.sup E := by
        rw [← hsum, map_add, hvzero, zero_add]
        exact shift_mem n grades hw
      have hsource : LinearMap.restrict nativeLZero hStable x - (n : ℂ) • x = 0 := by
        apply ih
        simpa only [map_sub, map_smul, hIntertwines, shift, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] using hshift
      by_contra hxne
      have hne : (x : State) ≠ 0 := fun h => hxne (Subtype.ext h)
      apply totalLZero_no_integer_eigenvalue n x hne
      simpa only [LinearMap.coe_restrict_apply, Submodule.coe_smul,
        native_conformal_coeff_neg_six_eq_totalLZero] using
        congrArg (fun y : S => (y : State)) (sub_eq_zero.mp hsource)
  refine le_antisymm (fun x hx => ?_) bot_le
  let s : S := ⟨x, hx⟩
  have hs : f s ∈ (⨆ n : ℤ, E n) := by
    rw [show (⨆ n : ℤ, E n) = ⊤ from hGraded]
    exact Submodule.mem_top
  change f s ∈ ((⨆ n : ℤ, E n : Submodule ℂ W) : Set W) at hs
  rw [Submodule.coe_iSup_eq_iUnion_finset_coe_biSup] at hs
  obtain ⟨grades, hgrades⟩ := Set.mem_iUnion.mp hs
  rw [← Finset.sup_eq_iSup] at hgrades
  rw [Submodule.mem_bot]
  exact congrArg (fun y : S => (y : State)) (vanishes grades s hgrades)

#print axioms eq_bot_of_integral_conformal_inclusion

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegralExtensionObstruction
