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

/-- Abstract the ordinary double-dual evaluation calculation before substituting
large realized weak-module multiplicities. The original transpose compatibility
is used pointwise; the concrete consumer separately cancels actual kappa/iota. -/
private theorem dualMap_eval_transport
    {M N P Q DP DQ : Type*}
    (eM : P → M → ℂ) (eN : Q → N → ℂ)
    (dM : M → DP) (dN : N → DQ)
    (pairP : DP → P → ℂ) (pairQ : DQ → Q → ℂ)
    (f : M → N) (g : Q → P) (dualG : DP → DQ)
    (hExt : Function.Injective pairQ)
    (hDM : ∀ x p, pairP (dM x) p = eM p x)
    (hDN : ∀ x q, pairQ (dN x) q = eN q x)
    (hG : ∀ φ q, pairQ (dualG φ) q = pairP φ (g q))
    (hNat : ∀ q x, eM (g q) x = eN q (f x)) (x : M) :
    dualG (dM x) = dN (f x) := by
  apply hExt
  funext q
  rw [hG, hDM, hDN, hNat]

/-- Transport contravariant naturality through ordinary equivalences before
substituting the concrete realized multiplicity types. -/
private theorem dualMultiplicityEquiv_natural
    {M N P Q : Type*} (eM : P ≃ M) (eN : Q ≃ N)
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
  have hcancel := kappa_iota (DualMultiplicity (dualModule A)) c
    ((dualMultiplicityEquiv A hD c).dualMap (Module.Dual.eval ℂ (Multiplicity A c) x))
  have hnat := dualMap_eval_transport
    (M := Multiplicity A c) (N := Multiplicity B c)
    (P := Multiplicity (dualModule A) (-c)) (Q := Multiplicity (dualModule B) (-c))
    (DP := DualMultiplicity (dualModule A) c)
    (DQ := DualMultiplicity (dualModule B) c)
    (fun p y => (dualMultiplicityEquiv A hD c p).toAddHom.toFun y)
    (fun q y => (dualMultiplicityEquiv B hD c q).toAddHom.toFun y)
    (fun y => (dualMultiplicityEquiv A hD c).dualMap (Module.Dual.eval ℂ (Multiplicity A c) y))
    (fun y => (dualMultiplicityEquiv B hD c).dualMap (Module.Dual.eval ℂ (Multiplicity B c) y))
    (fun φ p => φ.toAddHom.toFun p) (fun φ q => φ.toAddHom.toFun q)
    (restrict f c).toAddHom.toFun (restrict (dualHom hD f) (-c)).toAddHom.toFun
    (restrict (dualHom hD f) (-c)).dualMap.toAddHom.toFun
    (fun _ _ h => DFunLike.ext _ _ (fun q => congrFun h q))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun q y => congrArg (fun ψ : Module.Dual ℂ (Multiplicity A c) => ψ.toAddHom.toFun y)
      (dualMultiplicityEquiv_natural
        (dualMultiplicityEquiv A hD c).toEquiv (dualMultiplicityEquiv B hD c).toEquiv
        (dualIota A c).toAddHom.toFun (dualIota B c).toAddHom.toFun
        (dualMultiplicityEquiv_symm_apply A hD c) (dualMultiplicityEquiv_symm_apply B hD c)
        (restrict (dualHom hD f) (-c)).toAddHom.toFun
        (fun ψ : Module.Dual ℂ (Multiplicity B c) => ψ.comp (restrict f c))
        (dualHom_dualIota hD f c) q)) x
  have h := (congrArg (fun Φ : DualMultiplicity (dualModule A) c =>
    iota (DualMultiplicity (dualModule B)) c
      ((restrict (dualHom hD f) (-c)).dualMap Φ)) hcancel).trans
    (congrArg (iota (DualMultiplicity (dualModule B)) c).toAddHom.toFun hnat)
  exact h

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

/-- Compose an abstract equivalence with a realized inclusion and its left inverse
before substituting the large double-realized multiplicity types. -/
private theorem linear_inverse_left
    {V W Q Z : Type*} (e : V → W) (ei : W → V) (d : W → Q) (di : Q → W)
    (i : Q → Z) (k : Z → Q)
    (hKI : ∀ q, k (i q) = q) (hD : ∀ w, di (d w) = w) (hE : ∀ v, ei (e v) = v)
    (x : V) : ei (di (k (i (d (e x))))) = x := by
  rw [hKI, hD, hE]

/-- The corresponding right inverse uses actual realization reconstruction. -/
private theorem linear_inverse_right
    {V W Q Z : Type*} (e : V → W) (ei : W → V) (d : W → Q) (di : Q → W)
    (i : Q → Z) (k : Z → Q)
    (hIK : ∀ z, i (k z) = z) (hD : ∀ q, d (di q) = q) (hE : ∀ w, e (ei w) = w)
    (z : Z) : i (d (e (ei (di (k z))))) = z := by
  rw [hE, hD, hIK]

private theorem bidualInverseFamily_left (c : Discriminant D)
    (x : Multiplicity A c) :
    bidualInverseFamily A hD c (bidualFamily A hD c x) = x := by
  have he (y : Multiplicity A c) :
    (Module.evalEquiv ℂ (Multiplicity A c)).symm
      (Module.Dual.eval ℂ (Multiplicity A c) y) = y := by
    simpa only [Module.evalEquiv_apply] using
      (Module.evalEquiv ℂ (Multiplicity A c)).symm_apply_apply y
  have h := linear_inverse_left
    (Module.Dual.eval ℂ (Multiplicity A c)).toAddHom.toFun
    (Module.evalEquiv ℂ (Multiplicity A c)).symm.toAddHom.toFun
    (dualMultiplicityEquiv A hD c).dualMap.toAddHom.toFun
    (dualMultiplicityEquiv A hD c).dualMap.symm.toAddHom.toFun
    (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun
    (kappa (DualMultiplicity (dualModule A)) c).toAddHom.toFun
    (kappa_iota (DualMultiplicity (dualModule A)) c)
    (dualMultiplicityEquiv A hD c).dualMap.toEquiv.symm_apply_apply
    he x
  exact h

private theorem bidualInverseFamily_right (c : Discriminant D)
    (z : Multiplicity (dualModule (dualModule A)) c) :
    bidualFamily A hD c (bidualInverseFamily A hD c z) = z := by
  have he (y : Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c))) :
    Module.Dual.eval ℂ (Multiplicity A c)
      ((Module.evalEquiv ℂ (Multiplicity A c)).symm y) = y := by
    simpa only [Module.evalEquiv_apply] using
      (Module.evalEquiv ℂ (Multiplicity A c)).apply_symm_apply y
  have h := linear_inverse_right
    (Module.Dual.eval ℂ (Multiplicity A c)).toAddHom.toFun
    (Module.evalEquiv ℂ (Multiplicity A c)).symm.toAddHom.toFun
    (dualMultiplicityEquiv A hD c).dualMap.toAddHom.toFun
    (dualMultiplicityEquiv A hD c).dualMap.symm.toAddHom.toFun
    (iota (DualMultiplicity (dualModule A)) c).toAddHom.toFun
    (kappa (DualMultiplicity (dualModule A)) c).toAddHom.toFun
    (multiplicityEquiv (DualMultiplicity (dualModule A)) hD c).symm_apply_apply
    (dualMultiplicityEquiv A hD c).dualMap.toEquiv.apply_symm_apply
    he z
  exact h

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
