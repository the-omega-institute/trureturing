module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import OmegaBuild.Commands

/-!
Omega original.

An injective intertwiner into an eigenspace span detects eigenvalues of the source.
-/

compile_only_with_mathlib

set_option autoImplicit false

public section

namespace Omega.LinearAlgebra

/-- If the target is spanned by eigenspaces with labels absent from the source's point
spectrum, an injective intertwiner forces every source vector to vanish.
Each image vector belongs to a finite sum of the target eigenspaces. -/
theorem eq_zero_of_injective_intertwiner_of_no_eigenvalue
    {R : Type*} {V : Type*} {W : Type*} {ι : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (A : Module.End R V) (B : Module.End R W)
    (label : ι → R) (hSpan : (⨆ i, B.eigenspace (label i)) = ⊤)
    (hNoEigenvalue : ∀ i, ¬ A.HasEigenvalue (label i))
    (f : V →ₗ[R] W) (hInjective : Function.Injective f)
    (hIntertwines : ∀ x : V, f (A x) = B (f x)) : ∀ x : V, x = 0 := by
  classical
  let E (i : ι) := B.eigenspace (label i)
  let shift (i : ι) : Module.End R W := B - label i • LinearMap.id
  have shift_mem (i : ι) (grades : Finset ι) {v : W} (hv : v ∈ grades.sup E) :
      shift i v ∈ grades.sup E := by
    refine (Finset.sup_le_iff.mpr ?_ : grades.sup E ≤ (grades.sup E).comap (shift i)) hv
    intro j hj w hw
    change shift i w ∈ grades.sup E
    have heigen := Module.End.mem_eigenspace_iff.mp hw
    have hw' : w ∈ grades.sup E := (Finset.le_sup (f := E) hj) hw
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, heigen]
    exact (grades.sup E).sub_mem
      ((grades.sup E).smul_mem (label j) hw') ((grades.sup E).smul_mem (label i) hw')
  -- Each shift removes one eigenspace from the sum and has zero kernel on the source.
  have vanishes (grades : Finset ι) : ∀ x : V, f x ∈ grades.sup E → x = 0 := by
    induction grades using Finset.induction_on with
    | empty =>
      intro x hx
      apply hInjective
      simpa only [Finset.sup_empty, Submodule.mem_bot, map_zero] using hx
    | insert i grades _ ih =>
      intro x hx
      rw [Finset.sup_insert] at hx
      obtain ⟨v, hv, w, hw, hsum⟩ := Submodule.mem_sup.mp hx
      have hvzero : shift i v = 0 := by
        simpa [shift, sub_eq_zero] using (Module.End.mem_eigenspace_iff.mp hv)
      have hshift : shift i (f x) ∈ grades.sup E := by
        rw [← hsum, map_add, hvzero, zero_add]
        exact shift_mem i grades hw
      have hsource : A x - label i • x = 0 := by
        apply ih
        simpa only [map_sub, map_smul, hIntertwines, shift, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] using hshift
      by_contra hxne
      exact hNoEigenvalue i (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hsource), hxne⟩)
  intro x
  have hx : f x ∈ (⨆ i, E i) := by
    rw [show (⨆ i, E i) = ⊤ from hSpan]
    exact Submodule.mem_top
  change f x ∈ ((⨆ i, E i : Submodule R W) : Set W) at hx
  rw [Submodule.coe_iSup_eq_iUnion_finset_coe_biSup] at hx
  obtain ⟨grades, hgrades⟩ := Set.mem_iUnion.mp hx
  rw [← Finset.sup_eq_iSup] at hgrades
  exact vanishes grades x hgrades

end Omega.LinearAlgebra
