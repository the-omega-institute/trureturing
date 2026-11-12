/- GID: D5/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonPivotalMonoidality
   mirror-B: D5/B/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonPivotalMonoidality
   status: source-only proposed proof bodies; native/kernel false. -/
/- SOURCE ONLY. Full original-carrier proposals; no native acceptance claim. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (carry zeroCarry unitCharacter unitCharacter_nonzero)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleRealization ActualWeakModuleDuality ActualWeakModuleBiduality
open ActualWeakModuleUniversalField (P PairSector targetModule tag)
open ActualWeakModuleProductMultiplicity ActualWeakModuleProductNaturality
open ActualWeakModuleAssociator ActualWeakModulePentagon ActualWeakModuleUnits
open ActualWeakModuleUnitCoherence ActualWeakModuleDualTensorator
open ActualWeakModuleBalancing (theta thetaScalar restrict_theta)

open private restrict_extend from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private restrict_identity from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private multiplicity_induction from D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator
open private unitDualHom_eta0 from D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensoratorUnit
open private carry_symm from D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
open private restrict_comp transpose_read bidual_read bidual_read_apply pivotal_classified bidualIota from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Tensor
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- The complete target functional. Its coordinate is read at (-d,-c),
independently of the original input carry(c,d). -/
def pivotalPairFunctional (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    Module.Dual ℂ (Multiplicity (targetModule (dualModule B) (dualModule A)) (-(c+d))) :=
  Xi (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
    (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) ⊗ₜ[ℂ]
      kappa (DualMultiplicity (dualModule B)) d (bidualFamily B hD d y))

/-- Reciprocity on an arbitrary test fiber, including equal total and unequal
individual labels. Both Xi evaluations use their actual normalized mu. -/
private theorem tensor_transpose_fiber (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d)
    (i : Fiber (D := D) (-(c+d)))
    (z : Multiplicity (dualModule B) i.val.1)
    (w : Multiplicity (dualModule A) i.val.2) :
    dualMultiplicityEquiv (targetModule A B) hD (c+d)
      (restrict (dualTensorHom A B hD) (-(c+d))
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) i (z ⊗ₜ[ℂ] w)))
      (jAt A B hD (c+d) ⟨(c,d),rfl⟩ (x ⊗ₜ[ℂ] y)) =
      k hD c d * pivotalPairFunctional A B hD c d x y
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) i (z ⊗ₜ[ℂ] w)) := by
  let j : Fiber (D := D) (c+d) := ⟨(c,d),rfl⟩
  let ri : Fiber (D := D) (-(c+d)) := ⟨(-d,-c),by abel⟩
  by_cases hi : i = ri
  · subst i
    obtain ⟨ψ,rfl⟩ := (dualMultiplicityEquiv B hD d).symm.surjective z
    obtain ⟨φ,rfl⟩ := (dualMultiplicityEquiv A hD c).symm.surjective w
    have hk := dualTensorHom_jAt A B hD c d ψ φ
    have hk' := hk
    simp only [dualMultiplicityEquiv_symm_apply, dualIota, neg_neg] at hk' ⊢
    change _ = k hD c d *
      Xi (dualModule B) (dualModule A) hD (-(c+d)) ri _
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ri _)
    rw [hk']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      dualMultiplicityEquiv_apply, dualKappa, dualIota, neg_neg, kappa_iota,
      Xi, fiberRead, LinearMap.comp_apply, LinearMap.dualMap_apply,
      mu_jAt, DirectSum.component.lof_self, reversePairing_tmul, bidual_read_apply,
      dualMultiplicityEquiv_symm_apply, LinearEquiv.apply_symm_apply]
    ring
  · let ji : Fiber (D := D) (c+d) := ⟨(-i.val.2,-i.val.1), by
      calc
        -i.val.2 + -i.val.1 = -(i.val.1+i.val.2) := by abel
        _ = c+d := by rw [i.property, neg_neg]⟩
    have hj : j ≠ ji := by
      intro he
      apply hi
      apply Subtype.ext
      apply Prod.ext
      · have hh := congrArg (fun a : Fiber (D := D) (c+d) => -a.val.2) he
        simpa only [j, ri, ji, neg_neg] using hh.symm
      · have hh := congrArg (fun a : Fiber (D := D) (c+d) => -a.val.1) he
        simpa only [j, ri, ji, neg_neg] using hh.symm
    have hz := Xi_jAt_wrong A B hD (c+d) ji j hj
      (kappa (DualMultiplicity B) i.val.1 z ⊗ₜ[ℂ]
        kappa (DualMultiplicity A) i.val.2 w) (x ⊗ₜ[ℂ] y)
    have hw := Xi_jAt_wrong (dualModule B) (dualModule A) hD (-(c+d)) ri i hi
      (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) ⊗ₜ[ℂ]
        kappa (DualMultiplicity (dualModule B)) d (bidualFamily B hD d y)) (z ⊗ₜ[ℂ] w)
    let read : Module.Dual ℂ (Multiplicity (targetModule A B) (c+d)) := by
      simpa only [DualMultiplicity, neg_neg] using
        readFunctional A B hD (-(c+d)) i (z ⊗ₜ[ℂ] w)
    have hread : read (jAt A B hD (c+d) j (x ⊗ₜ[ℂ] y)) = 0 := by
      simpa only [read, readFunctional, LinearMap.comp_apply, TensorProduct.map_tmul,
        reverseFiber, neg_neg, ji] using hz
    rw [dualTensorHom, restrict_extend, dualTensorFamily_jAt]
    have hh := congrArg (fun a : ℂ => k hD (-i.val.2) (-i.val.1) * a) hread
    simpa only [read, dualMultiplicityEquiv, dualModule, DualMultiplicity,
      ActualWeakModuleRealization.multiplicityEquiv, neg_neg, map_smul, kappa_iota,
      LinearMap.smul_apply, smul_eq_mul, pivotalPairFunctional, hw, mul_zero] using hh

/-- All functional tests are exhausted separately from the source fibers.
This consumes the actual finite mu/nu decomposition, with no finite-space premise. -/
private theorem tensor_transpose_all (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    ((dualMultiplicityEquiv (targetModule A B) hD (c+d)).dualMap
      (Module.Dual.eval ℂ (Multiplicity (targetModule A B) (c+d))
        (jAt A B hD (c+d) ⟨(c,d),rfl⟩ (x ⊗ₜ[ℂ] y)))).comp
        (restrict (dualTensorHom A B hD) (-(c+d))) =
      k hD c d • pivotalPairFunctional A B hD c d x y := by
  apply LinearMap.ext
  intro t
  apply multiplicity_induction (dualModule B) (dualModule A) hD (-(c+d))
    (fun t => dualMultiplicityEquiv (targetModule A B) hD (c+d)
      (restrict (dualTensorHom A B hD) (-(c+d)) t)
        (jAt A B hD (c+d) ⟨(c,d),rfl⟩ (x ⊗ₜ[ℂ] y)) =
      (k hD c d • pivotalPairFunctional A B hD c d x y) t)
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ t
  exact tensor_transpose_fiber A B hD c d x y

/-- Left path on an arbitrary input oscillator vector: the original source
transport uses carry(c,d); the target functional still reads carry(-d,-c). -/
private theorem tensor_left_pair (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    ((dualHom hD (dualTensorHom A B hD)).comp
      (pivotalHom (targetModule A B) hD)).linearMap
      (tag A B c d x y v) =
      (pivotalScalar hD (c+d) * k hD c d) •
        DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ]
          DualMultiplicity (targetModule (dualModule B) (dualModule A)) s) (c+d)
          (transport D (representative D (c+d)) (carry D hD c d) v ⊗ₜ[ℂ]
            pivotalPairFunctional A B hD c d x y) := by
  have hclass := classification_j A B hD c d (x ⊗ₜ[ℂ] y)
    (transport D (representative D (c+d)) (carry D hD c d) v)
  rw [(transportLinearEquiv D _ _).symm_apply_apply] at hclass
  change (dualHom hD (dualTensorHom A B hD)).linearMap
    ((pivotalHom (targetModule A B) hD).linearMap _) = _
  rw [← hclass, pivotal_classified]
  simp only [map_smul]
  unfold bidualFamily
  rw [classification_iota, dualHom_carrier, tensor_transpose_all]
  simp only [TensorProduct.tmul_smul, map_smul, smul_smul]

/-- Right path: its tensorator is K_(DB,DA), with coefficient k(-d,-c). -/
private theorem tensor_right_pair (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    ((dualTensorHom (dualModule B) (dualModule A) hD).comp
      (productHom hD (pivotalHom A hD) (pivotalHom B hD))).linearMap
      (tag A B c d x y v) =
      (pivotalScalar hD c * pivotalScalar hD d * k hD (-d) (-c)) •
        DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ]
          DualMultiplicity (targetModule (dualModule B) (dualModule A)) s) (c+d)
          (transport D (representative D (c+d)) (carry D hD c d) v ⊗ₜ[ℂ]
            pivotalPairFunctional A B hD c d x y) := by
  change (dualTensorHom (dualModule B) (dualModule A) hD).linearMap
    ((productHom hD (pivotalHom A hD) (pivotalHom B hD)).linearMap _) = _
  rw [productHom_pair, TensorProduct.map_tmul, restrict_pivotalHom, restrict_pivotalHom]
  simp only [pivotalFamily, LinearMap.smul_apply, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, map_smul, smul_smul]
  rw [dualTensorHom_pair]
  simp only [readFunctional, LinearMap.comp_apply, TensorProduct.map_tmul,
    pivotalPairFunctional, reverseFiber, smul_smul, mul_assoc]

/-- FULL original ModuleHom monoidality. The functional calculation includes
all target tests; pair_induction now exhausts every original source vector. -/
theorem pivotalHom_tensor :
    (dualHom hD (dualTensorHom A B hD)).comp (pivotalHom (targetModule A B) hD) =
      (dualTensorHom (dualModule B) (dualModule A) hD).comp
        (productHom hD (pivotalHom A hD) (pivotalHom B hD)) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  apply ActualWeakModuleBraiding.pair_induction A B
    (fun z => ((dualHom hD (dualTensorHom A B hD)).comp
      (pivotalHom (targetModule A B) hD)).linearMap z =
      ((dualTensorHom (dualModule B) (dualModule A) hD).comp
        (productHom hD (pivotalHom A hD) (pivotalHom B hD))).linearMap z)
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ z
  intro c d x y v
  rw [tensor_left_pair, tensor_right_pair, pivotalScalar_cochain]

/-- Single-charge readback exposes BOTH carries and every target functional
coordinate, including all mismatched individual fibers of equal total. -/
theorem pivotalHom_tensor_single (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (l : Charge D) (f : Oscillator D) :
    ((dualHom hD (dualTensorHom A B hD)).comp
      (pivotalHom (targetModule A B) hD)).linearMap
      (tag A B c d x y (Finsupp.single l f)) =
      (pivotalScalar hD c * pivotalScalar hD d * k hD (-d) (-c) *
        epsilon D l (carry D hD c d)) •
        DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ]
          DualMultiplicity (targetModule (dualModule B) (dualModule A)) s) (c+d)
          (Finsupp.single (l+carry D hD c d) f ⊗ₜ[ℂ]
            ({ toFun := fun t =>
                epsilon D (-carry D hD (-d) (-c)) (carry D hD (-d) (-c)) *
                  reversePairing
                    (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x) ⊗ₜ[ℂ]
                      kappa (DualMultiplicity (dualModule B)) d (bidualFamily B hD d y))
                    (ActualWeakModuleScalarProbes.tensorCoordinates (t.val.val (-d,-c))
                      (-carry D hD (-d) (-c),0))
               map_add' := by
                 intro z w
                 simp only [Submodule.coe_add, DFinsupp.add_apply, map_add,
                   Finsupp.add_apply, mul_add]
               map_smul' := by
                 intro a z
                 simp only [Submodule.coe_smul, DFinsupp.smul_apply, map_smul,
                   Finsupp.smul_apply, smul_eq_mul]
                 ring } : DualMultiplicity
                   (targetModule (dualModule B) (dualModule A)) (c+d))) := by
  rw [pivotalHom_tensor, tensor_right_pair, transport_single,
    ← TensorProduct.smul_tmul', map_smul, smul_smul]
  apply congrArg (fun ψ : DualMultiplicity
      (targetModule (dualModule B) (dualModule A)) (c+d) =>
    (pivotalScalar hD c * pivotalScalar hD d * k hD (-d) (-c) *
      epsilon D l (carry D hD c d)) •
      DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ]
        DualMultiplicity (targetModule (dualModule B) (dualModule A)) s) (c+d)
        (Finsupp.single (l+carry D hD c d) f ⊗ₜ[ℂ] ψ))
  apply LinearMap.ext
  intro t
  exact Xi_coordinate (dualModule B) (dualModule A) hD (-(c+d))
    ⟨(-d,-c),by abel⟩ _ t

end Tensor

section Unit
variable (hD : (gramReal D).PosDef)

/-- Computation on the actual eta generator, tested on the entire algebraic
unit dual. The subsequent carrier proof uses the supplied unit exhaustion. -/
private theorem pivotal_unit_eta :
    restrict ((dualHom hD (unitDualHom hD)).comp (pivotalHom (I D) hD)) 0 (eta0 hD) =
      iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD) := by
  apply (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity (I D)) hD 0).injective
  apply LinearMap.ext
  intro y
  rw [restrict_comp, transpose_read, restrict_pivotalHom]
  simp only [pivotalFamily, LinearMap.smul_apply, pivotalScalar_zero, one_smul,
    LinearMap.comp_apply, bidual_read, LinearEquiv.dualMap_apply, Module.Dual.eval_apply,
    kappa_iota]
  have hy : y = etaCoefficient hD y • eta0 hD := (etaCoefficient_inverse hD y).symm
  rw [hy]
  simp only [map_smul, LinearMap.smul_apply, unitDualHom_eta0, kappa_iota,
    unitCapFunctional, neg_zero, dualMultiplicityEquiv_apply, dualKappa, etaCoefficient_eta0, smul_eq_mul, mul_one]

/-- The full unit computation retains transportInverse D 0 zeroCarry.
The supplied unit_classified exhausts the actual unit carrier, so all source
fibers and all oscillator vectors enter the proof. -/
theorem pivotalHom_unit_carrier (v : Carrier D) :
    ((dualHom hD (unitDualHom hD)).comp (pivotalHom (I D) hD)).linearMap v =
      DirectSum.lof ℂ _ (fun c => Carrier D ⊗[ℂ] DualMultiplicity (I D) c) 0
        (transportInverse D 0 (zeroCarry D hD) v ⊗ₜ[ℂ] unitCapFunctional hD) := by
  have hi : v = classified hD (I D) 0 (eta0 hD)
      (transportInverse D 0 (zeroCarry D hD) v) := by
    rw [unit_classified]
    exact (LinearMap.congr_fun (transportInverse_right D 0 (zeroCarry D hD)) v).symm
  calc
    _ = ((dualHom hD (unitDualHom hD)).comp (pivotalHom (I D) hD)).linearMap
        (classified hD (I D) 0 (eta0 hD)
          (transportInverse D 0 (zeroCarry D hD) v)) := by rw [← hi]
    _ = _ := by rw [classified_natural, pivotal_unit_eta, classification_iota]

/-- FULL ModuleHom unit equality follows from the actual all-carrier
calculation, with its inverse zero-carry transport. -/
theorem pivotalHom_unit :
    (dualHom hD (unitDualHom hD)).comp (pivotalHom (I D) hD) = unitDualHom hD := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  rw [pivotalHom_unit_carrier, unitDualHom_carrier]

end Unit

section CapTheta
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- Full cap/theta compatibility. Both wrong total fibers vanish; in the
matching case the original cap at DA contributes u(c), not u(-c). -/
theorem pivotalHom_cap_theta :
    (evaluation (dualModule A) hD).comp
      (productHom hD (pivotalHom A hD) (ModuleHom.id (dualModule A))) =
    (evaluation A hD).comp
      ((ActualWeakModuleBraiding.braidIso A (dualModule A)).hom.comp
        (productHom hD (theta A hD).hom (ModuleHom.id (dualModule A)))) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro t
  apply ActualWeakModuleBraiding.pair_induction A (dualModule A)
    (fun t => ((evaluation (dualModule A) hD).comp
      (productHom hD (pivotalHom A hD) (ModuleHom.id (dualModule A)))).linearMap t =
      ((evaluation A hD).comp
        ((ActualWeakModuleBraiding.braidIso A (dualModule A)).hom.comp
          (productHom hD (theta A hD).hom (ModuleHom.id (dualModule A))))).linearMap t)
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ t
  intro c r x z v
  change (evaluation (dualModule A) hD).linearMap
    ((productHom hD (pivotalHom A hD) (ModuleHom.id (dualModule A))).linearMap _) =
    (evaluation A hD).linearMap (ActualWeakModuleBraiding.braid A (dualModule A)
      ((productHom hD (theta A hD).hom (ModuleHom.id (dualModule A))).linearMap _))
  rw [productHom_pair, productHom_pair, TensorProduct.map_tmul, TensorProduct.map_tmul,
    restrict_identity, restrict_identity, restrict_pivotalHom, restrict_theta]
  by_cases he : c+r = 0
  · have hr : r = -c := by
      calc r = -c+(c+r) := by abel
           _ = -c := by rw [he, add_zero]
    subst r
    obtain ⟨φ,rfl⟩ := (dualMultiplicityEquiv A hD c).symm.surjective z
    have hcap := evaluation_pair (dualModule A) hD (-c)
      (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x))
      ((dualMultiplicityEquiv A hD c).symm φ) v
    have hb : bidualIota A c
        (kappa (DualMultiplicity (dualModule A)) c (bidualFamily A hD c x)) =
        bidualFamily A hD c x := by
      simpa only [bidualIota] using
        (ActualWeakModuleRealization.multiplicityEquiv
          (DualMultiplicity (dualModule A)) hD c).symm_apply_apply (bidualFamily A hD c x)
    simp only [bidualIota] at hb
    simp only [dualIota, neg_neg, hb, bidual_read_apply,
      LinearEquiv.apply_symm_apply] at hcap
    simp only [dualMultiplicityEquiv_symm_apply] at hcap
    simp only [pivotalFamily, LinearMap.smul_apply, TensorProduct.smul_tmul',
      map_smul, smul_smul, dualMultiplicityEquiv_symm_apply]
    rw [hcap, ActualWeakModuleBraiding.braid_tag, map_smul, evaluation_pair]
    rw [carry_symm hD (-c) c]
    simp only [map_smul, smul_smul]
    congr 1
    rw [pivotalScalar_ribbon]
    field_simp [unitCharacter_nonzero D hD c] <;> ring
  · have hr : r+c ≠ 0 := by simpa only [add_comm] using he
    rw [evaluation_pair_wrong (dualModule A) hD c r he]
    change 0 = (evaluation A hD).linearMap
      (ActualWeakModuleBraiding.braid A (dualModule A)
        (tag A (dualModule A) c r (thetaScalar c • x) z v))
    rw [ActualWeakModuleBraiding.braid_tag, map_smul,
      evaluation_pair_wrong A hD r c hr, smul_zero]

end CapTheta
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality
