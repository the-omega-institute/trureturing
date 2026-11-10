/- GID: D5/S3/FiniteGroups/GroupAlgebra/ProjectiveScalarExtension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ProjectiveScalarExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Projective, mathlib/module/Mathlib.RepresentationTheory.Intertwining, mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Lift]
   utility: none
   digest: Extension from a field to a nonzero commutative algebra preserves and reflects group-algebra projectivity for arbitrary representations. -/

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RepresentationTheory.Intertwining

/-!
Projectivity under coefficient extension, without a finiteness hypothesis.

The public definition uses Mathlib's algebra homomorphism on endomorphism
rings, rather than reconstructing the action laws.  The projectivity proof
uses the scalar-extension adjunction on actual intertwining maps.  Descent
uses a k-linear functional on R taking 1 to 1.  Tensoring a surjection remains
surjective, and a section after extension descends by insertion and contraction.
This avoids any commutativity assumption on the group algebra and does not
require an algebra structure over the noncommutative ring k[G].

The helpers are consumed by the single public equivalence.  The fixed free
cover in `projective_of_free_section` is only a way to use the universe-polymorphic
projectivity API; it imposes no smallness condition on the original module.

The native proof uses the lifting and contraction constructions above.  The
corresponding Scribe explains the coefficient-ring application and its
prime-field boundary; no separate application theorem is retained.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension

open scoped MonoidAlgebra TensorProduct

universe uk uR uG uV uW uU

noncomputable section

section Lifting

variable {k : Type uk} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup U] [Module k U]

-- Transfer Mathlib's module lifting property through its existing equivalence
-- between intertwining maps and group-algebra linear maps.
private theorem lift_intertwiner (ρ : Representation k G V)
    (σ : Representation k G W) (τ : Representation k G U)
    [Module.Projective k[G] ρ.asModule]
    (f : σ.IntertwiningMap τ) (g : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) :
    ∃ s : ρ.IntertwiningMap σ, ∀ v, f (s v) = g v := by
  let fA := Representation.IntertwiningMap.equivLinearMapAsModule σ τ f
  let gA := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ g
  have hfA : Function.Surjective fA := by
    intro y
    obtain ⟨x, hx⟩ := hf (τ.asModuleEquiv y)
    refine ⟨σ.asModuleEquiv.symm x, ?_⟩
    exact τ.asModuleEquiv.injective hx
  obtain ⟨s, hs⟩ := Module.projective_lifting_property fA gA hfA
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm s, ?_⟩
  intro v
  exact congrArg τ.asModuleEquiv (LinearMap.congr_fun hs (ρ.asModuleEquiv.symm v))

-- Only the canonical free cover is needed for projectivity.  In particular,
-- there is no categorical Small assumption linking uk, uG and uV.
private theorem projective_of_free_section (ρ : Representation k G V)
    (h : ∀ f : (Representation.free k G ρ.asModule).IntertwiningMap ρ,
      Function.Surjective f →
        ∃ s : ρ.IntertwiningMap (Representation.free k G ρ.asModule),
          ∀ v, f (s v) = v) :
    Module.Projective k[G] ρ.asModule := by
  apply Module.Projective.of_lifting_property''
  intro q hq
  let σ := Representation.free k G ρ.asModule
  let e := Representation.finsuppLEquivFreeAsModule k G ρ.asModule
  let qA : σ.asModule →ₗ[k[G]] ρ.asModule := q.comp e.symm.toLinearMap
  let f : σ.IntertwiningMap ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm qA
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x, hx⟩ := hq (ρ.asModuleEquiv.symm v)
    refine ⟨σ.asModuleEquiv (e x), ?_⟩
    change ρ.asModuleEquiv (q (e.symm (e x))) = v
    rw [e.symm_apply_apply, hx, ρ.asModuleEquiv.apply_symm_apply]
  obtain ⟨s, hs⟩ := h f hf
  let sA := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ s
  refine ⟨e.symm.toLinearMap.comp sA, ?_⟩
  apply LinearMap.ext
  intro v
  apply ρ.asModuleEquiv.injective
  exact hs (ρ.asModuleEquiv v)

end Lifting

section Extension

variable {k : Type uk} {R : Type uR} {G : Type uG}
variable [CommRing k] [CommRing R] [Algebra k R] [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Scalar extension of the actual representation, with G acting on the second
tensor factor.  In particular, its value on `r ⊗ₜ v` is `r ⊗ₜ ρ g v`. -/
def scalarExtension (R : Type uR) [CommRing R] [Algebra k R]
    (ρ : Representation k G V) : Representation R G (R ⊗[k] V) :=
  (Module.End.baseChangeHom k R V).toMonoidHom.comp ρ

-- Coefficient restriction, used only as the right adjoint to scalar extension.
private def restrictRepresentation {W : Type uW} [AddCommGroup W]
    [Module R W] [Module k W] [IsScalarTower k R W]
    (σ : Representation R G W) : Representation k G W where
  toFun g := (σ g).restrictScalars k
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

private def restrictIntertwiner {W : Type uW} {U : Type uU}
    [AddCommGroup W] [AddCommGroup U] [Module R W] [Module R U]
    [Module k W] [Module k U] [IsScalarTower k R W] [IsScalarTower k R U]
    {σ : Representation R G W} {τ : Representation R G U}
    (f : σ.IntertwiningMap τ) :
    (restrictRepresentation (k := k) σ).IntertwiningMap
      (restrictRepresentation (k := k) τ) where
  toLinearMap := f.toLinearMap.restrictScalars k
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    exact Representation.IntertwiningMap.isIntertwining σ τ f g w

private def scalarExtensionMap (ρ : Representation k G V) (σ : Representation k G W)
    (f : ρ.IntertwiningMap σ) :
    (scalarExtension R ρ).IntertwiningMap (scalarExtension R σ) where
  toLinearMap := f.toLinearMap.baseChange R
  isIntertwining' g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r v
    change r ⊗ₜ[k] f (ρ g v) = r ⊗ₜ[k] σ g (f v)
    exact congrArg (fun x : W => r ⊗ₜ[k] x)
      (Representation.IntertwiningMap.isIntertwining ρ σ f g v)

private def unitIntertwiner (ρ : Representation k G V) :
    ρ.IntertwiningMap (restrictRepresentation (k := k) (scalarExtension R ρ)) where
  toLinearMap := TensorProduct.mk k R V (1 : R)
  isIntertwining' g := by ext v; rfl

-- The scalar-extension adjunction, constructed from the existing linear-map
-- adjunction.  The only new obligation is the G-equivariance identity.
private def extendIntertwiner (ρ : Representation k G V)
    {W : Type uW} [AddCommGroup W] [Module R W] [Module k W]
    [IsScalarTower k R W] (σ : Representation R G W)
    (s : ρ.IntertwiningMap (restrictRepresentation (k := k) σ)) :
    (scalarExtension R ρ).IntertwiningMap σ where
  toLinearMap := s.toLinearMap.liftBaseChange R
  isIntertwining' g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r v
    change (s.toLinearMap.liftBaseChange R) (r ⊗ₜ[k] ρ g v) =
      σ g ((s.toLinearMap.liftBaseChange R) (r ⊗ₜ[k] v))
    simp only [LinearMap.liftBaseChange_tmul]
    have hs : s (ρ g v) = σ g (s v) :=
      Representation.IntertwiningMap.isIntertwining ρ
        (restrictRepresentation (k := k) σ) s g v
    change r • s (ρ g v) = σ g (r • s v)
    rw [hs]
    exact ((σ g).map_smul r (s v)).symm

private def contract (ell : R →ₗ[k] k) : R ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (TensorProduct.map ell (LinearMap.id : V →ₗ[k] V))

@[simp] private theorem contract_tmul (ell : R →ₗ[k] k) (r : R) (v : V) :
    contract ell (r ⊗ₜ[k] v) = ell r • v := by
  simp [contract]

private def contractIntertwiner (ρ : Representation k G V) (ell : R →ₗ[k] k) :
    (restrictRepresentation (k := k) (scalarExtension R ρ)).IntertwiningMap ρ where
  toLinearMap := contract ell
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro r v
    change contract ell (r ⊗ₜ[k] ρ g v) = ρ g (contract ell (r ⊗ₜ[k] v))
    simp only [contract_tmul, map_smul]

-- Naturality is needed to descend a section of a scalar-extended surjection.
private theorem contract_natural (ell : R →ₗ[k] k) (f : V →ₗ[k] W) :
    f.comp (contract ell) =
      (contract ell).comp ((f.baseChange R).restrictScalars k) := by
  apply TensorProduct.ext'
  intro r v
  change f (contract ell (r ⊗ₜ[k] v)) = contract ell (r ⊗ₜ[k] f v)
  simp only [contract_tmul, map_smul]

end Extension

/-- For any group and any representation over a field, extension to a nonzero
commutative algebra preserves and reflects projectivity over the group algebra.
The field, algebra, group and representation have independent universes. -/
theorem projective_iff_scalarExtension
    {k : Type uk} {R : Type uR} {G : Type uG} {V : Type uV}
    [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
    [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Module.Projective k[G] ρ.asModule ↔
      Module.Projective R[G] (scalarExtension R ρ).asModule := by
  classical
  let ρR := scalarExtension R ρ
  constructor
  · intro hρ
    letI : Module.Projective k[G] ρ.asModule := hρ
    apply projective_of_free_section ρR
    intro f hf
    let σ := Representation.free R G ρR.asModule
    let X := ρR.asModule →₀ R[G]
    let σk := restrictRepresentation (k := k) σ
    let τk := restrictRepresentation (k := k) ρR
    let fk : σk.IntertwiningMap τk := restrictIntertwiner f
    have hfk : Function.Surjective fk := hf
    obtain ⟨s, hs⟩ := lift_intertwiner ρ σk τk fk (unitIntertwiner ρ) hfk
    let t : ρR.IntertwiningMap σ := extendIntertwiner ρ σ s
    have hs' (v : V) : f (s v) = (1 : R) ⊗ₜ[k] v := hs v
    have ht : f.toLinearMap.comp t.toLinearMap = LinearMap.id := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro r v
      change f (r • s v) = r ⊗ₜ[k] v
      rw [map_smul, hs' v]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact ⟨t, fun x => LinearMap.congr_fun ht x⟩
  · intro hρR
    letI : Module.Projective R[G] ρR.asModule := hρR
    obtain ⟨ell, hEll⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : R) ≠ 0)
    apply projective_of_free_section ρ
    intro f hf
    let σ := Representation.free k G ρ.asModule
    let fR : (scalarExtension R σ).IntertwiningMap ρR := scalarExtensionMap σ ρ f
    have hfR : Function.Surjective fR :=
      LinearMap.baseChange_surjective R (g := f.toLinearMap) hf
    obtain ⟨s, hs⟩ := lift_intertwiner ρR (scalarExtension R σ) ρR fR
      (Representation.IntertwiningMap.id ρR) hfR
    let t : ρ.IntertwiningMap σ :=
      (contractIntertwiner σ ell).comp
        ((restrictIntertwiner (k := k) s).comp (unitIntertwiner ρ))
    refine ⟨t, ?_⟩
    intro v
    change f (contract ell (s ((1 : R) ⊗ₜ[k] v))) = v
    calc
      f (contract ell (s ((1 : R) ⊗ₜ[k] v))) =
          contract ell (fR (s ((1 : R) ⊗ₜ[k] v))) :=
        LinearMap.congr_fun (contract_natural ell f.toLinearMap) _
      _ = contract ell ((1 : R) ⊗ₜ[k] v) :=
        congrArg (contract ell) (hs ((1 : R) ⊗ₜ[k] v))
      _ = v := by rw [contract_tmul, hEll, one_smul]

end

end D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
