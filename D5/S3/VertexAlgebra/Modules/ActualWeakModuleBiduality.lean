/-
Source-only implementation.  Native elaboration and kernel acceptance are pending.
The declarations below add the original weak-module bidual evaluation bridge;
all supplied duality, realization, classification, and ModuleHom records remain
literal inputs.  The arbitrary-multiplicity map is the algebraic evaluation map;
only the inverse ModuleIso uses finite multiplicities.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom ActualWeakModuleRealization ActualWeakModuleDuality
open FullJacobiCurrentTransport FullJacobiIntertwiner

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Canonical
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)

/-- The actual realization projection, transported in its dependent codomain.
This map is consumed by the equivalence readback below. -/
def dualKappa (c : Discriminant D) :
    Multiplicity (dualModule A) (-c) →ₗ[ℂ] Module.Dual ℂ (Multiplicity A c) := by
  simpa only [DualMultiplicity, neg_neg] using kappa (DualMultiplicity A) (-c)

/-- The supplied realization equivalence, with the literal neg_neg index read back. -/
def dualMultiplicityEquiv (c : Discriminant D) :
    Multiplicity (dualModule A) (-c) ≃ₗ[ℂ] Module.Dual ℂ (Multiplicity A c) := by
  simpa only [dualModule, DualMultiplicity, neg_neg] using
    (multiplicityEquiv (DualMultiplicity A) hD (-c))

@[simp] theorem dualMultiplicityEquiv_apply (c : Discriminant D)
    (z : Multiplicity (dualModule A) (-c)) :
    dualMultiplicityEquiv A hD c z = dualKappa A c z := by
  simp [dualMultiplicityEquiv, dualKappa, dualModule, DualMultiplicity, multiplicityEquiv]

@[simp] theorem dualMultiplicityEquiv_symm_apply (c : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) :
    (dualMultiplicityEquiv A hD c).symm φ = dualIota A c φ := by
  simp [dualMultiplicityEquiv, dualIota, dualModule, DualMultiplicity, multiplicityEquiv]

/-- The actual multiplicity component of algebraic bidual evaluation. -/
def bidualFamily : Families A (dualModule (dualModule A)) := fun c =>
  (iota (DualMultiplicity (dualModule A)) c).comp
    ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
      (Module.Dual.eval ℂ (Multiplicity A c)))

/-- The canonical original ModuleHom A -> dualModule (dualModule A). -/
def bidualHom : ModuleHom A (dualModule (dualModule A)) :=
  extend hD (bidualFamily A hD)

/-- The finite-dimensional reflexivity instance is obtained on the original
multiplicity; no finiteness of the oscillator or whole carrier is used. -/
include hD in
private theorem dualMultiplicity_finite
    [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]
    (c : Discriminant D) : Module.Finite ℂ (Multiplicity (dualModule A) c) := by
  let e := multiplicityEquiv (DualMultiplicity A) hD c
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The ordinary evaluation naturality supplier, retained on the actual
multiplicity maps used below. -/
theorem eval_natural (c : Discriminant D)
    {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
    (f : Multiplicity A c →ₗ[ℂ] Y) :
    f.dualMap.dualMap.comp (Module.Dual.eval ℂ (Multiplicity A c)) =
      (Module.Dual.eval ℂ Y).comp f := by
  exact Module.Dual.eval_naturality f

end Canonical

section Natural
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

private def dualDualFamily (f : ModuleHom A B) :
    Families (dualModule (dualModule A)) (dualModule (dualModule B)) := fun c =>
  (iota (DualMultiplicity (dualModule B)) c).comp
    (((restrict (dualHom hD f) (-c)).dualMap).comp
      (kappa (DualMultiplicity (dualModule A)) c))

private theorem dualDualFamily_natural (f : ModuleHom A B)
    (c : Discriminant D) (x : Multiplicity A c) :
    dualDualFamily hD f c (bidualFamily A hD c x) =
      bidualFamily B hD c (restrict f c x) := by
  simp only [dualDualFamily, bidualFamily, LinearMap.comp_apply, kappa_iota]
  apply congrArg (iota (DualMultiplicity (dualModule B)) c)
  apply LinearMap.ext
  intro z
  have ht : restrict (dualHom hD f) (-c) z =
      (dualMultiplicityEquiv A hD c).symm
        ((dualMultiplicityEquiv B hD c z).comp (restrict f c)) := by
    obtain ⟨φ,rfl⟩ := (dualMultiplicityEquiv B hD c).symm.surjective z
    rw [LinearEquiv.apply_symm_apply, dualMultiplicityEquiv_symm_apply,
      dualHom_dualIota, dualMultiplicityEquiv_symm_apply]
  have heval := LinearMap.congr_fun (eval_natural (A := A) c (restrict f c)) x
  have heval' := congrArg
    (fun ψ : Module.Dual ℂ (Module.Dual ℂ (Multiplicity B c)) =>
      ψ (dualMultiplicityEquiv B hD c z)) heval
  simp only [LinearMap.dualMap_apply, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
  calc
    _ = ((dualMultiplicityEquiv B hD c z).comp (restrict f c)) x := by
      rw [ht, LinearEquiv.apply_symm_apply]
    _ = _ := heval'

theorem bidualHom_natural (f : ModuleHom A B) :
    (bidualHom B hD).comp f =
      (dualHom hD (dualHom hD f)).comp (bidualHom A hD) := by
  apply (recordEquiv A (dualModule (dualModule B))).injective
  apply (homMultiplicityEquiv A (dualModule (dualModule B)) hD).injective
  funext c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualHom B hD).comp f).linearMap (x.val : X) =
    ((dualHom hD (dualHom hD f)).comp (bidualHom A hD)).linearMap (x.val : X)
  have hl := extend_ground hD (bidualFamily B hD) c (restrict f c x)
  have hr := extend_ground hD (dualDualFamily hD f) c (bidualFamily A hD c x)
  rw [LinearMap.comp_apply]
  change (bidualHom B hD).linearMap (f.linearMap (x.val : X)) = _
  rw [show (restrict f c x).val.val = f.linearMap (x.val : X) by rfl]
  rw [hl]
  change (dualHom hD (dualHom hD f)).linearMap
      ((bidualFamily A hD c x).val) =
    (dualDualFamily hD f c (bidualFamily A hD c x)).val at hr
  rw [← hr]
  exact congrArg Subtype.val (dualDualFamily_natural hD f c x)

end Natural

section FiniteIso
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- The inverse family uses the actual kappa of the outer realization and the
finite-dimensional `Module.evalEquiv` on the original multiplicity. -/
def bidualInverseFamily :
    Families (dualModule (dualModule A)) A := fun c =>
  (Module.evalEquiv ℂ (Multiplicity A c)).symm.toLinearMap.comp
    ((dualMultiplicityEquiv A hD c).dualMap.symm.toLinearMap.comp
      (kappa (DualMultiplicity (dualModule A)) c))

private theorem bidualInverseFamily_left (c : Discriminant D)
    (x : Multiplicity A c) :
    bidualInverseFamily A hD c (bidualFamily A hD c x) = x := by
  simp only [bidualInverseFamily, bidualFamily, LinearMap.comp_apply, kappa_iota,
    LinearEquiv.dualMap_apply, LinearEquiv.dualMap_symm,
    LinearEquiv.symm_apply_apply, Module.evalEquiv_apply,
    LinearEquiv.symm_apply_apply]

private theorem bidualInverseFamily_right (c : Discriminant D)
    (z : Multiplicity (dualModule (dualModule A)) c) :
    bidualFamily A hD c (bidualInverseFamily A hD c z) = z := by
  have hz : z = iota (DualMultiplicity (dualModule A)) c
      (kappa (DualMultiplicity (dualModule A)) c z) := by
    simpa [dualModule, DualMultiplicity, multiplicityEquiv] using
      ((multiplicityEquiv (DualMultiplicity (dualModule A)) hD c).symm_apply_apply z).symm
  rw [hz]
  simp only [bidualInverseFamily, bidualFamily, LinearMap.comp_apply, kappa_iota,
    LinearEquiv.dualMap_apply, LinearEquiv.dualMap_symm,
    LinearEquiv.apply_symm_apply, Module.evalEquiv_apply]
  rfl

def bidualInverseHom : ModuleHom (dualModule (dualModule A)) A :=
  extend hD (bidualInverseFamily A hD)

include hD in
private theorem hom_ext_restrict
    {M : Type v} {N : Type w} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    {J : FullJacobiLatticeModule D M} {K : FullJacobiLatticeModule D N}
    (f g : ModuleHom J K) (h : restrict f = restrict g) : f = g := by
  apply (recordEquiv J K).injective
  apply (homMultiplicityEquiv J K hD).injective
  exact h

private theorem bidual_left_inverse :
    (bidualInverseHom A hD).comp (bidualHom A hD) = ModuleHom.id A := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualInverseHom A hD).comp (bidualHom A hD)).linearMap (x.val : X) = x.val
  have h1 := extend_ground hD (bidualFamily A hD) c x
  have h2 := extend_ground hD (bidualInverseFamily A hD) c (bidualFamily A hD c x)
  rw [LinearMap.comp_apply, h1, h2]
  exact congrArg Subtype.val (bidualInverseFamily_left A hD c x)

private theorem bidual_right_inverse :
    (bidualHom A hD).comp (bidualInverseHom A hD) =
      ModuleHom.id (dualModule (dualModule A)) := by
  apply hom_ext_restrict hD
  funext c
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change ((bidualHom A hD).comp (bidualInverseHom A hD)).linearMap (z.val : _) = z.val
  have h1 := extend_ground hD (bidualInverseFamily A hD) c z
  have h2 := extend_ground hD (bidualFamily A hD) c (bidualInverseFamily A hD c z)
  rw [LinearMap.comp_apply, h1, h2]
  exact congrArg Subtype.val (bidualInverseFamily_right A hD c z)

/-- Finite-multiplicity biduality as an actual original ModuleIso record. -/
def bidualIso : ModuleIso A (dualModule (dualModule A)) := by
  letI : ∀ c : Discriminant D, Module.Finite ℂ (Multiplicity (dualModule A) c) :=
    fun c => dualMultiplicity_finite A hD c
  exact {
  linearEquiv :=
    { toLinearMap := (bidualHom A hD).linearMap
      invFun := (bidualInverseHom A hD).linearMap
      left_inv := by
        intro x
        exact congrArg (fun g : ModuleHom A A => g.linearMap x)
          (bidual_left_inverse A hD)
      right_inv := by
        intro z
        exact congrArg (fun g : ModuleHom (dualModule (dualModule A))
            (dualModule (dualModule A)) => g.linearMap z)
          (bidual_right_inverse A hD) }
    intertwines := (bidualHom A hD).intertwines }

end FiniteIso
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality
