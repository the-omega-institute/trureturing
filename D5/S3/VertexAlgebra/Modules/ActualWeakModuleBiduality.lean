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
  have cancel {M N P Q : Type u}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      [AddCommMonoid P] [Module ℂ P] [AddCommMonoid Q] [Module ℂ Q]
      (e : N ≃ₗ[ℂ] P) (m : Q ≃ₗ[ℂ] P) (ev : M →ₗ[ℂ] N) (r : N →ₗ[ℂ] M)
      (hr : ∀ x, r (ev x) = x) (x : M) :
      r (e.symm (m.toLinearMap
        ((m.symm.toLinearMap.comp (e.toLinearMap.comp ev)) x))) = x := by
    as_aux_lemma =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      exact hr x
  exact @cancel (Multiplicity A c)
    (Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c)))
    (DualMultiplicity (dualModule A) c) (Multiplicity (dualModule (dualModule A)) c)
    _ _ _ _ _ _ _ _ (dualMultiplicityEquiv A hD c).dualMap
    (multiplicityEquiv (DualMultiplicity (dualModule A)) hD c)
    (Module.Dual.eval ℂ (Multiplicity A c)) r hr x


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
  have lift_natural {MA NA PA QA : Type u} {MB NB PB QB : Type v}
      [AddCommMonoid MA] [Module ℂ MA] [AddCommMonoid NA] [Module ℂ NA]
      [AddCommMonoid PA] [Module ℂ PA] [AddCommMonoid QA] [Module ℂ QA]
      [AddCommMonoid MB] [Module ℂ MB] [AddCommMonoid NB] [Module ℂ NB]
      [AddCommMonoid PB] [Module ℂ PB] [AddCommMonoid QB] [Module ℂ QB]
      (eA : NA ≃ₗ[ℂ] PA) (eB : NB ≃ₗ[ℂ] PB)
      (mA : QA ≃ₗ[ℂ] PA) (mB : QB ≃ₗ[ℂ] PB)
      (evA : MA →ₗ[ℂ] NA) (evB : MB →ₗ[ℂ] NB)
      (f : MA →ₗ[ℂ] MB) (g : PA →ₗ[ℂ] PB) (x : MA)
      (h : g (eA (evA x)) = eB (evB (f x))) :
      (mB.symm.toLinearMap.comp (g.comp mA.toLinearMap))
        ((mA.symm.toLinearMap.comp (eA.toLinearMap.comp evA)) x) =
      (mB.symm.toLinearMap.comp (eB.toLinearMap.comp evB)) (f x) := by
    as_aux_lemma =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply]
      exact congrArg (fun t => mB.symm t) h
  have scalar_dual {M : Type v} {N : Type u}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      (g : M →ₗ[ℂ] N) (φ : Module.Dual ℂ N) (z : M) :
      g.dualMap φ z = φ (g z) := by as_aux_lemma => rfl
  have scalar_equiv_dualA {M N : Type u}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      (e : M ≃ₗ[ℂ] N) (φ : Module.Dual ℂ N) (z : M) :
      e.dualMap φ z = φ (e z) := by as_aux_lemma => rfl
  have scalar_equiv_dualB {M N : Type v}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      (e : M ≃ₗ[ℂ] N) (φ : Module.Dual ℂ N) (z : M) :
      e.dualMap φ z = φ (e z) := by as_aux_lemma => rfl
  have scalar_evalA {M : Type u} [AddCommMonoid M] [Module ℂ M]
      (z : M) (φ : Module.Dual ℂ M) :
      Module.Dual.eval ℂ M z φ = φ z := by as_aux_lemma => rfl
  have scalar_evalB {M : Type v} [AddCommMonoid M] [Module ℂ M]
      (z : M) (φ : Module.Dual ℂ M) :
      Module.Dual.eval ℂ M z φ = φ z := by as_aux_lemma => rfl
  have scalar_comp {M : Type u} {N : Type v}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      (φ : Module.Dual ℂ N) (f : M →ₗ[ℂ] N) (z : M) :
      φ.comp f z = φ (f z) := by as_aux_lemma => rfl
  have hdn (q : Multiplicity (dualModule B) (-c)) :
      dualMultiplicityEquiv A hD c (restrict (dualHom hD f) (-c) q) =
        (dualMultiplicityEquiv B hD c q).comp (restrict f c) := by
    let eLeft : Multiplicity (dualModule A) (-c) ≃ Module.Dual ℂ (Multiplicity A c) :=
      { toFun := fun z => dualMultiplicityEquiv A hD c z
        invFun := fun φ => (dualMultiplicityEquiv A hD c).symm φ
        left_inv := fun z => (dualMultiplicityEquiv A hD c).symm_apply_apply z
        right_inv := fun φ => (dualMultiplicityEquiv A hD c).apply_symm_apply φ }
    let eRight : Multiplicity (dualModule B) (-c) ≃ Module.Dual ℂ (Multiplicity B c) :=
      { toFun := fun z => dualMultiplicityEquiv B hD c z
        invFun := fun ψ => (dualMultiplicityEquiv B hD c).symm ψ
        left_inv := fun z => (dualMultiplicityEquiv B hD c).symm_apply_apply z
        right_inv := fun ψ => (dualMultiplicityEquiv B hD c).apply_symm_apply ψ }
    have hnatural := @dualMultiplicityEquiv_natural
      (Module.Dual ℂ (Multiplicity A c)) (Module.Dual ℂ (Multiplicity B c))
      (Multiplicity (dualModule A) (-c)) (Multiplicity (dualModule B) (-c))
      eLeft eRight
      (fun φ => dualIota A c φ) (fun ψ => dualIota B c ψ)
      (fun φ => dualMultiplicityEquiv_symm_apply A hD c φ)
      (fun ψ => dualMultiplicityEquiv_symm_apply B hD c ψ)
      (fun z => restrict (dualHom hD f) (-c) z)
      (fun ψ : Module.Dual ℂ (Multiplicity B c) => ψ.comp (restrict f c))
      (fun ψ => dualHom_dualIota hD f c ψ) q
    have hleft (z : Multiplicity (dualModule A) (-c)) :
        dualMultiplicityEquiv A hD c z = eLeft z := by
      apply LinearMap.ext
      intro t
      rfl
    have hright (z : Multiplicity (dualModule B) (-c)) :
        eRight z = dualMultiplicityEquiv B hD c z := by
      apply LinearMap.ext
      intro t
      rfl
    exact (hleft (restrict (dualHom hD f) (-c) q)).trans
      (hnatural.trans (congrArg (fun ψ : Module.Dual ℂ (Multiplicity B c) =>
        ψ.comp (restrict f c)) (hright q)))

  let eA := (dualMultiplicityEquiv A hD c).dualMap
  let eB := (dualMultiplicityEquiv B hD c).dualMap
  let y := Module.Dual.eval ℂ (Multiplicity A c) x
  have he : (restrict (dualHom hD f) (-c)).dualMap (eA y) =
      eB (Module.Dual.eval ℂ (Multiplicity B c) (restrict f c x)) := by
    apply LinearMap.ext
    intro q
    have h1 := @scalar_dual (Multiplicity (dualModule B) (-c))
      (Multiplicity (dualModule A) (-c)) _ _ _ _ (restrict (dualHom hD f) (-c)) (eA y) q
    have h2 := @scalar_equiv_dualA (Multiplicity (dualModule A) (-c))
      (Module.Dual ℂ (Multiplicity A c)) _ _ _ _ (dualMultiplicityEquiv A hD c) y
      (restrict (dualHom hD f) (-c) q)
    have h3 := scalar_evalA x
      (dualMultiplicityEquiv A hD c (restrict (dualHom hD f) (-c) q))
    have h4 := congrArg (fun φ : Module.Dual ℂ (Multiplicity A c) => φ x) (hdn q)
    have h5 := scalar_comp (dualMultiplicityEquiv B hD c q) (restrict f c) x
    have h6 :=
      (@scalar_equiv_dualB (Multiplicity (dualModule B) (-c))
        (Module.Dual ℂ (Multiplicity B c)) _ _ _ _ (dualMultiplicityEquiv B hD c)
        (Module.Dual.eval ℂ (Multiplicity B c) (restrict f c x)) q).trans
          (scalar_evalB (restrict f c x) (dualMultiplicityEquiv B hD c q))
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6.symm))))
  exact @lift_natural (Multiplicity A c)
    (Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c)))
    (DualMultiplicity (dualModule A) c) (Multiplicity (dualModule (dualModule A)) c)
    (Multiplicity B c) (Module.Dual ℂ (Module.Dual ℂ (Multiplicity B c)))
    (DualMultiplicity (dualModule B) c) (Multiplicity (dualModule (dualModule B)) c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eA eB
    (multiplicityEquiv (DualMultiplicity (dualModule A)) hD c)
    (multiplicityEquiv (DualMultiplicity (dualModule B)) hD c)
    (Module.Dual.eval ℂ (Multiplicity A c)) (Module.Dual.eval ℂ (Multiplicity B c))
    (restrict f c) (restrict (dualHom hD f) (-c)).dualMap x he


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
  have cancel {M N P Q : Type u}
      [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
      [AddCommMonoid P] [Module ℂ P] [AddCommMonoid Q] [Module ℂ Q]
      (ev : M ≃ₗ[ℂ] N) (e : N ≃ₗ[ℂ] P) (m : Q ≃ₗ[ℂ] P) (z : Q) :
      (m.symm.toLinearMap.comp (e.toLinearMap.comp ev.toLinearMap))
        ((ev.symm.toLinearMap.comp (e.symm.toLinearMap.comp m.toLinearMap)) z) = z := by
    as_aux_lemma =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  exact @cancel (Multiplicity A c)
    (Module.Dual ℂ (Module.Dual ℂ (Multiplicity A c)))
    (DualMultiplicity (dualModule A) c) (Multiplicity (dualModule (dualModule A)) c)
    _ _ _ _ _ _ _ _ (Module.evalEquiv ℂ (Multiplicity A c))
    (dualMultiplicityEquiv A hD c).dualMap
    (multiplicityEquiv (DualMultiplicity (dualModule A)) hD c) z


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
