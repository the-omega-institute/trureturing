/- SOURCE ONLY / UNCOMPILED / UNACCEPTED.
The unit dual tensorator uses the original eta0/etaCoefficient and inverse
zero-carry transport. This file makes no assertion about an ordinary bidual.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (zeroCarry)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleRealization ActualWeakModuleDuality
open ActualWeakModuleUniversalField (P PairSector targetModule elementary)
open ActualWeakModuleProductMultiplicity (classified)
open ActualWeakModuleProductNaturality
open ActualWeakModuleUnits

open private left_ext from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
open private right_ext from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
open private multiplicity_linear_ext from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator
open private restrict_identity from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private familyMap restrict_extend from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section ExtensionInverse
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

/-- Actual two-sided classification transports propagate a proved component
inverse to every original carrier vector. Consumed below by both unit laws. -/
private theorem extend_inverse_apply (f : Families A B) (g : Families B A)
    (h : ∀ c x, g c (f c x) = x) (v : X) :
    (extend hD g).linearMap ((extend hD f).linearMap v) = v := by
  have hm : (familyMap g).comp (familyMap f) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro c
    apply TensorProduct.ext
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, familyMap, DirectSum.lmap_lof,
      TensorProduct.map_tmul, LinearMap.id_apply, h]
  change classificationEquiv A hD (familyMap g
    ((classificationEquiv B hD).symm (classificationEquiv B hD
      (familyMap f ((classificationEquiv A hD).symm v))))) = v
  rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, hm,
    LinearMap.id_apply, LinearEquiv.apply_symm_apply]

end ExtensionInverse

section Unit
variable (hD : (gramReal D).PosDef)

/-- Only equality transport along -0=0; no scalar is inserted in the functional. -/
def unitCapFunctional : DualMultiplicity (I D) 0 := by
  simpa only [neg_zero] using etaCoefficient hD

/-- The nonzero unit fiber is its actual one-dimensional eta fiber.
All other ORIGINAL unit fibers are zero by the supplied exhaustion theorem. -/
def unitDualFamily : Families (I D) (dualModule (I D)) := fun c => by
  by_cases hc : c = 0
  · subst c
    exact (etaCoefficient hD).smulRight
      (iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD))
  · exact 0

/-- The actual K0, as an original full module morphism. -/
def unitDualHom : ModuleHom (I D) (dualModule (I D)) :=
  extend hD (unitDualFamily hD)

/-- The inverse reads the actual dual realization, then evaluates at eta0. -/
def unitDualInverseFamily : Families (dualModule (I D)) (I D) := fun c => by
  by_cases hc : c = 0
  · subst c
    let read : Multiplicity (dualModule (I D)) 0 →ₗ[ℂ]
        Module.Dual ℂ (Multiplicity (I D) 0) := by
      simpa only [neg_zero] using kappa (DualMultiplicity (I D)) 0
    exact
      { toFun z := read z (eta0 hD) • eta0 hD
        map_add' z w := by simp only [map_add, LinearMap.add_apply, add_smul]
        map_smul' a z := by
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul] }
  · exact 0

def unitDualInverseHom : ModuleHom (dualModule (I D)) (I D) :=
  extend hD (unitDualInverseFamily hD)

private theorem unitDualFamily_left (c : Discriminant D) (x : Multiplicity (I D) c) :
    unitDualInverseFamily hD c (unitDualFamily hD c x) = x := by
  by_cases hc : c = 0
  · subst c
    simp only [unitDualFamily, unitDualInverseFamily, dif_pos rfl,
      LinearMap.smulRight_apply, LinearMap.coe_mk, map_smul, kappa_iota]
    simpa only [unitCapFunctional, neg_zero, etaCoefficient_eta0,
      LinearMap.smul_apply, smul_eq_mul, mul_one] using etaCoefficient_inverse hD x
  · rw [unit_multiplicity_wrong hD c hc x]
    simp

private theorem dualUnit_wrong (c : Discriminant D) (hc : c ≠ 0)
    (z : Multiplicity (dualModule (I D)) c) : z = 0 := by
  apply (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity (I D)) hD c).injective
  change kappa (DualMultiplicity (I D)) c z = kappa (DualMultiplicity (I D)) c 0
  rw [map_zero]
  apply LinearMap.ext
  intro x
  have hn : -c ≠ 0 := by simpa only [neg_eq_zero] using hc
  rw [unit_multiplicity_wrong hD (-c) hn x, map_zero]

private theorem unitDualFamily_right (c : Discriminant D)
    (z : Multiplicity (dualModule (I D)) c) :
    unitDualFamily hD c (unitDualInverseFamily hD c z) = z := by
  by_cases hc : c = 0
  · subst c
    let read : Multiplicity (dualModule (I D)) 0 →ₗ[ℂ]
        Module.Dual ℂ (Multiplicity (I D) 0) := by
      simpa only [neg_zero] using kappa (DualMultiplicity (I D)) 0
    have hφ : read z = read z (eta0 hD) • etaCoefficient hD := by
      apply LinearMap.ext
      intro x
      conv_lhs => rw [← etaCoefficient_inverse hD x]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    apply (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity (I D)) hD 0).injective
    change kappa (DualMultiplicity (I D)) 0
      (unitDualFamily hD 0 (unitDualInverseFamily hD 0 z)) =
        kappa (DualMultiplicity (I D)) 0 z
    simpa only [unitDualFamily, unitDualInverseFamily, dif_pos rfl,
      LinearMap.coe_mk, LinearMap.smulRight_apply, map_smul,
      etaCoefficient_eta0, smul_eq_mul, mul_one, kappa_iota,
      unitCapFunctional, neg_zero, read] using hφ.symm
  · rw [dualUnit_wrong hD c hc z]
    simp

/-- Both laws hold on EVERY original vector, including all charge/oscillator
states. The proof uses only the actual eta exhaustion, with no carrier finiteness. -/
def unitDualIso : ModuleIso (I D) (dualModule (I D)) where
  linearEquiv :=
    { toLinearMap := (unitDualHom hD).linearMap
      invFun := (unitDualInverseHom hD).linearMap
      left_inv := extend_inverse_apply hD (unitDualFamily hD) (unitDualInverseFamily hD)
        (unitDualFamily_left hD)
      right_inv := extend_inverse_apply hD (unitDualInverseFamily hD) (unitDualFamily hD)
        (unitDualFamily_right hD) }
  intertwines := (unitDualHom hD).intertwines

/-- Actual full-carrier formula: inverse unit transport is not discarded. -/
theorem unitDualHom_carrier (v : Carrier D) :
    (unitDualHom hD).linearMap v =
      DirectSum.lof ℂ _ (fun c => Carrier D ⊗[ℂ] DualMultiplicity (I D) c) 0
        (transportInverse D 0 (zeroCarry D hD) v ⊗ₜ[ℂ] unitCapFunctional hD) := by
  change classificationEquiv (dualModule (I D)) hD
    (familyMap (unitDualFamily hD) ((classificationEquiv (I D) hD).symm v)) = _
  rw [unit_classification_inverse]
  simp only [elementary, familyMap, DirectSum.lmap_lof, TensorProduct.map_tmul,
    LinearMap.id_apply, unitDualFamily, dif_pos rfl,
    LinearMap.smulRight_apply, etaCoefficient_eta0, one_smul]
  exact classification_iota (DualMultiplicity (I D)) hD 0 _ _

/-- The raw inverse-unit epsilon factor is literal, even when beta_0 is nonzero. -/
theorem unitDualHom_single (l : Charge D) (p : Oscillator D) :
    (unitDualHom hD).linearMap (Finsupp.single l p) =
      ((epsilon D (-zeroCarry D hD) (zeroCarry D hD))⁻¹ *
        epsilon D l (-zeroCarry D hD)) •
      DirectSum.lof ℂ _ (fun c => Carrier D ⊗[ℂ] DualMultiplicity (I D) c) 0
        (Finsupp.single (l-zeroCarry D hD) p ⊗ₜ[ℂ] unitCapFunctional hD) := by
  rw [unitDualHom_carrier, transportInverse_single, ← TensorProduct.smul_tmul', map_smul]

private theorem unitDualHom_eta0 :
    restrict (unitDualHom hD) 0 (eta0 hD) =
      iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD) := by
  rw [unitDualHom, restrict_extend]
  simp only [unitDualFamily, dif_pos rfl, LinearMap.smulRight_apply,
    etaCoefficient_eta0, one_smul]

/-- Full unit cap normalization on the entire original P(I,I), not just the
unit vacuum. The original inverse zero-carry in K0 is exactly cancelled. -/
theorem unitDualHom_cap :
    (evaluation (I D) hD).comp
      (productHom hD (unitDualHom hD) (ModuleHom.id (I D))) =
        (leftUnitIso hD (I D)).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply left_ext hD (I D)
  intro c v x
  change (evaluation (I D) hD).linearMap
      ((productHom hD (unitDualHom hD) (ModuleHom.id (I D))).linearMap
        (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,c)
          (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x)))) =
    leftUnit hD (I D) (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x)))
  rw [productHom_pair, TensorProduct.map_tmul, unitDualHom_eta0, restrict_identity]
  by_cases hc : c = 0
  · subst c
    have he := evaluation_pair (I D) hD 0 (etaCoefficient hD) x v
    have hh : (evaluation (I D) hD).linearMap
        (DirectSum.lof ℂ _ (PairSector (dualModule (I D)) (I D)) (0,0)
          (v ⊗ₜ[ℂ] (iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD) ⊗ₜ[ℂ] x))) =
        etaCoefficient hD x • transport D 0 (zeroCarry D hD)
          (transport D (representative D 0) (zeroCarry D hD) v) := by
      simpa only [dualIota, neg_zero, unitCapFunctional,
        LatticeChargedQuotientScalar.unitCharacter_zero, one_mul,
        LatticeChargedQuotientScalar.zeroCarry] using he
    rw [hh, leftUnit_elementary]
    conv_rhs => rw [← etaCoefficient_inverse hD x]
    simp only [classified, TensorProduct.tmul_smul, map_smul,
      LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    congr 1
    exact (unit_classified hD
      (transport D (representative D 0) (zeroCarry D hD) v)).symm
  · rw [unit_multiplicity_wrong hD c hc x]
    simp

end Unit

section UnitDiagrams
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

private theorem readFunctional_unit_left (s : Discriminant D)
    (φ : DualMultiplicity A s) :
    readFunctional (I D) A hD s ⟨(s,0),add_zero s⟩
      (iota (DualMultiplicity A) s φ ⊗ₜ[ℂ]
        iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD)) =
      φ.comp (restrict (leftUnitIso hD A).hom (-s)) := by
  apply multiplicity_linear_ext (I D) A hD (-s)
  rintro ⟨⟨a,b⟩,hab⟩ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul x y =>
    by_cases ha : a = 0
    · subst a
      have hb : b = -s := by simpa only [zero_add] using hab
      subst b
      rw [← etaCoefficient_inverse hD x]
      simp only [← TensorProduct.smul_tmul', map_smul, LinearMap.comp_apply]
      congr 1
      have hx := Xi_jAt (I D) A hD (-s)
        ⟨(0,-s),zero_add (-s)⟩ (φ ⊗ₜ[ℂ] etaCoefficient hD)
        (eta0 hD ⊗ₜ[ℂ] y)
      simpa only [readFunctional, LinearMap.comp_apply, TensorProduct.map_tmul,
        kappa_iota, reverseFiber, neg_zero, unitCapFunctional, reversePairing_tmul,
        etaCoefficient_eta0, one_mul, restrict_leftUnit_jAt] using hx
    · rw [unit_multiplicity_wrong hD a ha x]
      simp

private theorem readFunctional_unit_right (s : Discriminant D)
    (φ : DualMultiplicity A s) :
    k hD (-s) 0 • readFunctional A (I D) hD s ⟨(0,s),zero_add s⟩
      (iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD) ⊗ₜ[ℂ]
        iota (DualMultiplicity A) s φ) =
      φ.comp (restrict (rightUnitIso hD A).hom (-s)) := by
  apply multiplicity_linear_ext A (I D) hD (-s)
  rintro ⟨⟨a,b⟩,hab⟩ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul x y =>
    by_cases hb : b = 0
    · subst b
      have ha : a = -s := by simpa only [add_zero] using hab
      subst a
      rw [← etaCoefficient_inverse hD y]
      simp only [TensorProduct.tmul_smul, map_smul]
      congr 1
      have hx := Xi_jAt A (I D) hD (-s)
        ⟨(-s,0),add_zero (-s)⟩ (etaCoefficient hD ⊗ₜ[ℂ] φ)
        (x ⊗ₜ[ℂ] eta0 hD)
      have hh : readFunctional A (I D) hD s ⟨(0,s),zero_add s⟩
          (iota (DualMultiplicity (I D)) 0 (unitCapFunctional hD) ⊗ₜ[ℂ]
            iota (DualMultiplicity A) s φ)
          (jAt A (I D) hD (-s) ⟨(-s,0),add_zero (-s)⟩
            (x ⊗ₜ[ℂ] eta0 hD)) = φ x := by
        simpa only [readFunctional, LinearMap.comp_apply, TensorProduct.map_tmul,
          kappa_iota, reverseFiber, neg_zero, unitCapFunctional, reversePairing_tmul,
          etaCoefficient_eta0, mul_one] using hx
      simp only [LinearMap.smul_apply, smul_eq_mul, hh, k_zero_right,
        LinearMap.comp_apply, restrict_rightUnit_jAt, map_smul]
    · rw [unit_multiplicity_wrong hD b hb y]
      simp

/-- First full unit diagram, on the entire original P(A*,I).
The factor u(s) on both paths comes from the actual right unitor. -/
theorem dualTensorHom_unit_left :
    (dualTensorHom (I D) A hD).comp
      (productHom hD (ModuleHom.id (dualModule A)) (unitDualHom hD)) =
    (dualHom hD (leftUnitIso hD A).hom).comp
      (rightUnitIso hD (dualModule A)).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply right_ext hD (dualModule A)
  intro s v z
  obtain ⟨φ,rfl⟩ :=
    (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD s).symm.surjective z
  change (dualTensorHom (I D) A hD).linearMap
      ((productHom hD (ModuleHom.id (dualModule A)) (unitDualHom hD)).linearMap
        (DirectSum.lof ℂ _ (PairSector (dualModule A) (I D)) (s,0)
          (v ⊗ₜ[ℂ] (iota (DualMultiplicity A) s φ ⊗ₜ[ℂ] eta0 hD)))) =
    (dualHom hD (leftUnitIso hD A).hom).linearMap
      (rightUnit hD (dualModule A)
        (DirectSum.lof ℂ _ (PairSector (dualModule A) (I D)) (s,0)
          (v ⊗ₜ[ℂ] (iota (DualMultiplicity A) s φ ⊗ₜ[ℂ] eta0 hD))))
  rw [productHom_pair, TensorProduct.map_tmul, restrict_identity, unitDualHom_eta0,
    dualTensorHom_pair, rightUnit_elementary]
  simp only [add_zero, neg_zero, k_zero_left, neg_neg,
    LatticeChargedQuotientScalar.carry_zero_right, map_smul]
  rw [classification_iota, dualHom_carrier, readFunctional_unit_left]
  rfl

/-- Second full unit diagram, on the entire original P(I,A*).
k(-s,0)=u(-s) is exactly the scalar in the transposed right unitor. -/
theorem dualTensorHom_unit_right :
    (dualTensorHom A (I D) hD).comp
      (productHom hD (unitDualHom hD) (ModuleHom.id (dualModule A))) =
    (dualHom hD (rightUnitIso hD A).hom).comp
      (leftUnitIso hD (dualModule A)).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply left_ext hD (dualModule A)
  intro s v z
  obtain ⟨φ,rfl⟩ :=
    (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD s).symm.surjective z
  change (dualTensorHom A (I D) hD).linearMap
      ((productHom hD (unitDualHom hD) (ModuleHom.id (dualModule A))).linearMap
        (DirectSum.lof ℂ _ (PairSector (I D) (dualModule A)) (0,s)
          (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] iota (DualMultiplicity A) s φ)))) =
    (dualHom hD (rightUnitIso hD A).hom).linearMap
      (leftUnit hD (dualModule A)
        (DirectSum.lof ℂ _ (PairSector (I D) (dualModule A)) (0,s)
          (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] iota (DualMultiplicity A) s φ))))
  rw [productHom_pair, TensorProduct.map_tmul, unitDualHom_eta0, restrict_identity,
    dualTensorHom_pair, leftUnit_elementary]
  simp only [zero_add, neg_zero, LatticeChargedQuotientScalar.carry_zero_left]
  rw [classification_iota, dualHom_carrier]
  have hh := readFunctional_unit_right A hD s φ
  rw [← hh]
  simp only [TensorProduct.tmul_smul, map_smul]

end UnitDiagrams
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator
