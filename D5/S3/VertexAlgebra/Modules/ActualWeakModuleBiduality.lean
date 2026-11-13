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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
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
  exact (LinearEquiv.cast (R := ℂ)
    (M := fun d => Module.Dual ℂ (Multiplicity A d)) (neg_neg c)).toLinearMap.comp
      (kappa (DualMultiplicity A) (-c))

/-- The supplied realization equivalence, with the literal neg_neg index read back. -/
def dualMultiplicityEquiv (c : Discriminant D) :
    Multiplicity (dualModule A) (-c) ≃ₗ[ℂ] Module.Dual ℂ (Multiplicity A c) := by
  exact (multiplicityEquiv (DualMultiplicity A) hD (-c)).trans
    (LinearEquiv.cast (R := ℂ)
      (M := fun d => Module.Dual ℂ (Multiplicity A d)) (neg_neg c))

@[simp] theorem dualMultiplicityEquiv_apply (c : Discriminant D)
    (z : Multiplicity (dualModule A) (-c)) :
    dualMultiplicityEquiv A hD c z = dualKappa A c z := by
  rfl

@[simp] theorem dualMultiplicityEquiv_symm_apply (c : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) :
    (dualMultiplicityEquiv A hD c).symm φ = dualIota A c φ := by
  rfl

/-- The actual multiplicity component of algebraic bidual evaluation. -/
def bidualFamily : Families A (dualModule (dualModule A)) := fun c =>
  (iota (DualMultiplicity (dualModule A)) c).comp
    ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
      (Module.Dual.eval ℂ (Multiplicity A c)))

/-- The canonical original ModuleHom A -> dualModule (dualModule A). -/
def bidualHom : ModuleHom A (dualModule (dualModule A)) :=
  extend hD (bidualFamily A hD)

include hD in
/-- The finite-dimensional reflexivity instance is obtained on the original
multiplicity; no finiteness of the oscillator or whole carrier is used. -/
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

/-- Cancel the actual outer realization and transpose before choosing a finite inverse. -/
private theorem linear_inverse_left (c : Discriminant D)
    (r : Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c)) →ₗ[ℂ] Multiplicity A c)
    (hr : ∀ x, r (Module.Dual.eval ℂ (Multiplicity A c) x) = x)
    (x : Multiplicity A c) :
    r ((dualMultiplicityEquiv A hD c).dualMap.symm
      (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x))) = x := by
  have hf : bidualFamily A hD c x =
      iota (DualMultiplicity (dualModule A)) c
        ((dualMultiplicityEquiv A hD c).dualMap
          (Module.Dual.eval ℂ (Multiplicity A c) x)) :=
    (LinearMap.comp_apply (iota (DualMultiplicity (dualModule A)) c)
      ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
        (Module.Dual.eval ℂ (Multiplicity A c))) x).trans
      (congrArg (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun
        (LinearMap.comp_apply (dualMultiplicityEquiv A hD c).dualMap.toLinearMap
          (Module.Dual.eval ℂ (Multiplicity A c)) x))
  have hk := (congrArg (kappa (DualMultiplicity (dualModule A)) c).toAddHom.toFun hf).trans
    (kappa_iota (DualMultiplicity (dualModule A)) c
      ((dualMultiplicityEquiv A hD c).dualMap
        (Module.Dual.eval ℂ (Multiplicity A c) x)))
  exact (congrArg (fun t : DualMultiplicity (dualModule A) c =>
    r ((dualMultiplicityEquiv A hD c).dualMap.symm t)) hk).trans
      ((congrArg r.toAddHom.toFun
        ((dualMultiplicityEquiv A hD c).dualMap.symm_apply_apply
          (Module.Dual.eval ℂ (Multiplicity A c) x))).trans (hr x))


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

/-- Transport contravariant naturality through ordinary equivalences before
substituting the concrete realized multiplicity types. -/
private theorem dualMultiplicityEquiv_natural
    {M : Type*} {N : Type*} {P : Type*} {Q : Type*} (eM : P ≃ M) (eN : Q ≃ N)
    (iM : M → P) (iN : N → Q)
    (hM : ∀ φ, eM.symm φ = iM φ) (hN : ∀ ψ, eN.symm ψ = iN ψ)
    (g : Q → P) (t : N → M)
    (h : ∀ ψ, g (iN ψ) = iM (t ψ)) (q : Q) :
    eM (g q) = t (eN q) := by
  have hq : iN (eN q) = q := (hN (eN q)).symm.trans (eN.symm_apply_apply q)
  have hg := (congrArg g hq.symm).trans (h (eN q))
  exact (congrArg eM (hg.trans (hM (t (eN q))).symm)).trans
    (eM.apply_symm_apply (t (eN q)))

private theorem dualDualFamily_natural (f : ModuleHom A B)
    (c : Discriminant D) (x : Multiplicity A c) :
    dualDualFamily hD f c (bidualFamily A hD c x) =
      bidualFamily B hD c (restrict f c x) := by
  have hdn (q : Multiplicity (dualModule B) (-c)) :
      dualMultiplicityEquiv A hD c (restrict (dualHom hD f) (-c) q) =
        (dualMultiplicityEquiv B hD c q).comp (restrict f c) := by
    exact @dualMultiplicityEquiv_natural
      (Module.Dual ℂ (Multiplicity A c)) (Module.Dual ℂ (Multiplicity B c))
      (Multiplicity (dualModule A) (-c)) (Multiplicity (dualModule B) (-c))
      (dualMultiplicityEquiv A hD c).toEquiv (dualMultiplicityEquiv B hD c).toEquiv
      (dualIota A c).toAddHom.toFun (dualIota B c).toAddHom.toFun
      (dualMultiplicityEquiv_symm_apply A hD c) (dualMultiplicityEquiv_symm_apply B hD c)
      (restrict (dualHom hD f) (-c)).toAddHom.toFun
      (fun ψ : Module.Dual ℂ (Multiplicity B c) => ψ.comp (restrict f c))
      (dualHom_dualIota hD f c) q
  let eA := (dualMultiplicityEquiv A hD c).dualMap
  let eB := (dualMultiplicityEquiv B hD c).dualMap
  let y := Module.Dual.eval ℂ (Multiplicity A c) x
  have hf : bidualFamily A hD c x =
      iota (DualMultiplicity (dualModule A)) c (eA y) :=
    (LinearMap.comp_apply (iota (DualMultiplicity (dualModule A)) c)
      (eA.toLinearMap.comp (Module.Dual.eval ℂ (Multiplicity A c))) x).trans
      (congrArg (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun
        (LinearMap.comp_apply eA.toLinearMap (Module.Dual.eval ℂ (Multiplicity A c)) x))
  have hk : kappa (DualMultiplicity (dualModule A)) c
      (bidualFamily A hD c x) = eA y :=
    (congrArg (kappa (DualMultiplicity (dualModule A)) c).toAddHom.toFun hf).trans
      (kappa_iota (DualMultiplicity (dualModule A)) c (eA y))
  have he : (restrict (dualHom hD f) (-c)).dualMap (eA y) =
      eB (Module.Dual.eval ℂ (Multiplicity B c) (restrict f c x)) := by
    apply LinearMap.ext
    intro q
    exact LinearMap.congr_fun (hdn q) x
  have hd : dualDualFamily hD f c (bidualFamily A hD c x) =
      iota (DualMultiplicity (dualModule B)) c
        ((restrict (dualHom hD f) (-c)).dualMap
          (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x))) :=
    (LinearMap.comp_apply (iota (DualMultiplicity (dualModule B)) c)
      ((restrict (dualHom hD f) (-c)).dualMap.comp
        (kappa (DualMultiplicity (dualModule A)) c)) (bidualFamily A hD c x)).trans
      (congrArg (iota (DualMultiplicity (dualModule B)) c).toAddHom.toFun
        (LinearMap.comp_apply (restrict (dualHom hD f) (-c)).dualMap
          (kappa (DualMultiplicity (dualModule A)) c) (bidualFamily A hD c x)))
  have hb : bidualFamily B hD c (restrict f c x) =
      iota (DualMultiplicity (dualModule B)) c
        (eB (Module.Dual.eval ℂ (Multiplicity B c) (restrict f c x))) :=
    (LinearMap.comp_apply (iota (DualMultiplicity (dualModule B)) c)
      (eB.toLinearMap.comp (Module.Dual.eval ℂ (Multiplicity B c))) (restrict f c x)).trans
      (congrArg (iota (DualMultiplicity (dualModule B)) c).toAddHom.toFun
        (LinearMap.comp_apply eB.toLinearMap (Module.Dual.eval ℂ (Multiplicity B c))
          (restrict f c x)))
  exact hd.trans (((congrArg (fun t : DualMultiplicity (dualModule A) c =>
    iota (DualMultiplicity (dualModule B)) c
      ((restrict (dualHom hD f) (-c)).dualMap t)) hk).trans
    (congrArg (iota (DualMultiplicity (dualModule B)) c).toAddHom.toFun he)).trans hb.symm)


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
  have ha := extend_ground hD (bidualFamily A hD) c x
  change (extend hD (bidualFamily B hD)).linearMap (restrict f c x).val.val =
    (extend hD (dualDualFamily hD f)).linearMap
      ((extend hD (bidualFamily A hD)).linearMap x.val.val)
  exact hl.trans
    ((congrArg (fun t : Multiplicity (dualModule (dualModule B)) c => t.val.val)
      (dualDualFamily_natural hD f c x).symm).trans
        (((congrArg (extend hD (dualDualFamily hD f)).linearMap.toAddHom.toFun ha).trans hr).symm))

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
  set_option synthInstance.maxHeartbeats 200000 in
    have he (y : Multiplicity A c) :
      (Module.evalEquiv ℂ (Multiplicity A c)).symm
        (Module.Dual.eval ℂ (Multiplicity A c) y) = y := by
      simpa only [Module.evalEquiv_apply] using
        (Module.evalEquiv ℂ (Multiplicity A c)).symm_apply_apply y
    exact linear_inverse_left A hD c
      (Module.evalEquiv ℂ (Multiplicity A c)).symm.toLinearMap he x

private theorem bidualInverseFamily_right (c : Discriminant D)
    (z : Multiplicity (dualModule (dualModule A)) c) :
    bidualFamily A hD c (bidualInverseFamily A hD c z) = z := by
  have hf : bidualFamily A hD c (bidualInverseFamily A hD c z) =
      iota (DualMultiplicity (dualModule A)) c
        ((dualMultiplicityEquiv A hD c).dualMap
          (Module.Dual.eval ℂ (Multiplicity A c) (bidualInverseFamily A hD c z))) :=
    (LinearMap.comp_apply (iota (DualMultiplicity (dualModule A)) c)
      ((dualMultiplicityEquiv A hD c).dualMap.toLinearMap.comp
        (Module.Dual.eval ℂ (Multiplicity A c))) (bidualInverseFamily A hD c z)).trans
      (congrArg (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun
        (LinearMap.comp_apply (dualMultiplicityEquiv A hD c).dualMap.toLinearMap
          (Module.Dual.eval ℂ (Multiplicity A c)) (bidualInverseFamily A hD c z)))
  have hg : bidualInverseFamily A hD c z =
      (Module.evalEquiv ℂ (Multiplicity A c)).symm
        ((dualMultiplicityEquiv A hD c).dualMap.symm
          (kappa (DualMultiplicity (dualModule A)) c z)) :=
    (LinearMap.comp_apply (Module.evalEquiv ℂ (Multiplicity A c)).symm.toLinearMap
      ((dualMultiplicityEquiv A hD c).dualMap.symm.toLinearMap.comp
        (kappa (DualMultiplicity (dualModule A)) c)) z).trans
      (congrArg (Module.evalEquiv ℂ (Multiplicity A c)).symm.toEquiv
        (LinearMap.comp_apply (dualMultiplicityEquiv A hD c).dualMap.symm.toLinearMap
          (kappa (DualMultiplicity (dualModule A)) c) z))
  have he := (congrArg (Module.Dual.eval ℂ (Multiplicity A c)).toAddHom.toFun hg).trans
    ((Module.evalEquiv ℂ (Multiplicity A c)).apply_symm_apply
      ((dualMultiplicityEquiv A hD c).dualMap.symm
        (kappa (DualMultiplicity (dualModule A)) c z)))
  have ht := (congrArg (dualMultiplicityEquiv A hD c).dualMap.toEquiv he).trans
    ((dualMultiplicityEquiv A hD c).dualMap.apply_symm_apply
      (kappa (DualMultiplicity (dualModule A)) c z))
  exact hf.trans ((congrArg (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun ht).trans
    ((multiplicityEquiv (DualMultiplicity (dualModule A)) hD c).symm_apply_apply z))


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
  change (extend hD (bidualInverseFamily A hD)).linearMap
    ((extend hD (bidualFamily A hD)).linearMap x.val.val) = x.val.val
  exact ((congrArg (extend hD (bidualInverseFamily A hD)).linearMap.toAddHom.toFun h1).trans h2).trans
    (congrArg (fun t : Multiplicity A c => t.val.val) (bidualInverseFamily_left A hD c x))

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
  change (extend hD (bidualFamily A hD)).linearMap
    ((extend hD (bidualInverseFamily A hD)).linearMap z.val.val) = z.val.val
  exact ((congrArg (extend hD (bidualFamily A hD)).linearMap.toAddHom.toFun h1).trans h2).trans
    (congrArg (fun t : Multiplicity (dualModule (dualModule A)) c => t.val.val)
      (bidualInverseFamily_right A hD c z))

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
