/-
SOURCE ONLY / UNCOMPILED / UNACCEPTED.
Units of the literal ActualWeakModuleUniversalField.P.  The original section
is retained; beta_0 is G n_0 and is never replaced by zero.  All tensor sums
are algebraic and all supports belong to the individual input vector.
The full original VOA/CFT/anomaly/fusion/string/AdS goal remains incomplete.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductMultiplicity
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalUnits
import D5.S3.VertexAlgebra.Sectors.LatticeChargedTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraCurrents LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (zeroCarry representative_zero unitCharacter unitCharacter_nonzero)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualCurrentTaylor ActualGroundJointWeights ActualGroundChargedSelection
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes (sectorModule sectorModule_mode tensorCoordinates coordinate)
open ActualWeakModuleUniversalField (P PairSector targetModule U elementary translation)
open ActualWeakModuleProductMultiplicity (classified classified_modes)

open private currentState_single inverseGram_left inverseGram_right from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
open private jointWeightMap from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private gramMap_injective class_representative class_gram from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private model_induction from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

/-- The original charge-zero sector, with its original field laws. -/
abbrev I (D : LatticeData) := sectorModule D 0

variable (hD : (gramReal D).PosDef)

private def tensorOneHom (a : Charge D) :
    ModuleHom (sectorModule D a) (tensorModule (sectorModule D a) ℂ) where
  linearMap := (TensorProduct.mk ℂ (Carrier D) ℂ).flip 1
  intertwines a m x := by
    simp only [tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.flip_apply, TensorProduct.mk_apply]

/-- Literal nested subtype: joint weight inside the original Omega inside I. -/
def eta0 : Multiplicity (I D) 0 := by
  let n := zeroCarry D hD
  have hc (i : Fin D.rank) (m : ℤ) :
      current (I D) i m (Finsupp.single n (1 : Oscillator D)) =
        Finsupp.single n (shiftedCurrentPolynomial D 0 1 i n m 1) := by
    rw [current, currentState_single, sectorModule_mode, action_current_coefficients]
  have ho : Finsupp.single n (1 : Oscillator D) ∈ Omega (I D) := by
    apply (mem_Omega _ _).mpr
    intro i r
    rw [hc]
    simp [shiftedCurrentPolynomial, show ¬ ((r : ℤ)+1<0) by omega,
      show (r : ℤ)+1≠0 by omega]
  refine ⟨⟨Finsupp.single n 1, ho⟩, (mem_jointWeight_iff _ _ _).mpr ?_⟩
  intro i
  change current (I D) i 0 (Finsupp.single n (1 : Oscillator D)) = _
  rw [hc]
  have hn : bilinear D (unitCharge D i) n = representative D 0 i := by
    rw [← gram_mulVec_unit, representative_zero D hD]
  simp [shiftedCurrentPolynomial, hn, Finsupp.smul_single]

@[simp] theorem eta0_val : (eta0 hD).val.val =
    Finsupp.single (zeroCarry D hD) (1 : Oscillator D) := rfl

/-- The scalar coordinate is an actual charge/constant coefficient. -/
def etaCoefficient : Multiplicity (I D) 0 →ₗ[ℂ] ℂ :=
  (coordinate D (zeroCarry D hD,0)).comp
    ((Omega (I D)).subtype.comp (jointWeight (I D) (representative D 0)).subtype)

@[simp] theorem etaCoefficient_eta0 : etaCoefficient hD (eta0 hD) = 1 := by
  simp [etaCoefficient, coordinate, eta0_val]

/-- Wrong classes vanish by the arbitrary-W exhaustion theorem at W=ℂ. -/
theorem unit_multiplicity_wrong (c : Discriminant D) (hc : c ≠ 0)
    (w : Multiplicity (I D) c) : w = 0 := by
  let z := jointWeightMap (tensorOneHom (D := D) 0) (representative D c) w
  have impossible (l : Charge D) : (0 : Charge D) + gramMap D l ≠ representative D c := by
    intro he
    have h := congrArg (classOf D) he
    have hc0 : c = 0 := by simpa only [zero_add, class_gram, class_representative] using h.symm
    exact hc hc0
  apply Subtype.ext; apply Subtype.ext
  apply Finsupp.ext
  intro l
  apply MvPolynomial.ext
  intro d
  have hz := ActualWeakModuleProductMultiplicity.joint_coordinate_exhaustion hD 0
    (representative D c) z (l,d) (Or.inr (impossible l))
  change tensorCoordinates (w.val.val ⊗ₜ[ℂ] (1 : ℂ)) (l,d) = 0 at hz
  simpa [ActualWeakModuleScalarProbes.tensorCoordinates_tmul,
    ActualWeakModuleScalarProbes.coordinate_apply] using hz

/-- No assumed ground basis: G-injectivity leaves exactly the n_0 coordinate. -/
theorem unit_multiplicity_coefficient (w : Multiplicity (I D) 0) :
    w.val.val = etaCoefficient hD w • (eta0 hD).val.val := by
  let z := jointWeightMap (tensorOneHom (D := D) 0) (representative D 0) w
  have unique (l : Charge D) : (0 : Charge D) + gramMap D l = representative D 0 ↔
      l = zeroCarry D hD := by
    rw [zero_add, representative_zero D hD]
    exact ⟨fun h => gramMap_injective D hD h, fun h => congrArg (gramMap D) h⟩
  have hs := ActualWeakModuleProductMultiplicity.joint_single_charge hD 0
    (representative D 0) (zeroCarry D hD) unique z
  change w.val.val ⊗ₜ[ℂ] (1 : ℂ) =
    Finsupp.single (zeroCarry D hD) (1 : Oscillator D) ⊗ₜ[ℂ]
      tensorCoordinates (w.val.val ⊗ₜ[ℂ] (1 : ℂ)) (zeroCarry D hD,0) at hs
  have hr := congrArg (fun t : Carrier D ⊗[ℂ] ℂ => TensorProduct.rid ℂ (Carrier D) t) hs
  simpa [etaCoefficient, ActualWeakModuleScalarProbes.tensorCoordinates_tmul,
    ActualWeakModuleScalarProbes.coordinate_apply, TensorProduct.rid_tmul] using hr

@[simp] theorem etaCoefficient_inverse (w : Multiplicity (I D) 0) :
    etaCoefficient hD w • eta0 hD = w := by
  apply Subtype.ext; apply Subtype.ext
  exact (unit_multiplicity_coefficient hD w).symm

/-- The actual coefficient and actual nested-subtype inverse. -/
def unitMultiplicityEquiv : Multiplicity (I D) 0 ≃ₗ[ℂ] ℂ where
  toLinearMap := etaCoefficient hD
  invFun t := t • eta0 hD
  left_inv := etaCoefficient_inverse hD
  right_inv t := by simp

private theorem zero_shift : shiftedCharge D 0 (zeroCarry D hD) = representative D 0 := by
  simp only [shiftedCharge, zero_add, representative_zero D hD]

/-- Accepted vacuum cyclicity determines the ORIGINAL classification inclusion. -/
theorem unit_classified (v : Carrier D) :
    classified hD (I D) 0 (eta0 hD) v = transport D 0 (zeroCarry D hD) v := by
  have he : classified hD (I D) 0 (eta0 hD) = transport D 0 (zeroCarry D hD) := by
    apply modeHom_ext_of_vacuum D (representative D 0)
      (fun a m => mode (I D) a m)
    · exact classified_modes hD (I D) 0 (eta0 hD)
    · intro a m x
      simpa only [zero_shift hD, sectorModule_mode] using
        transport_all_modes D 0 (zeroCarry D hD) a x m
    · rw [classified, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.flip_apply, TensorProduct.mk_apply, classification_normalization,
        transport_vacuum]
      rfl
  exact LinearMap.congr_fun he v

/-- All original unit vectors, including the actual (unnormalized) vacuum. -/
theorem unit_classification_inverse (v : Carrier D) :
    (classificationEquiv (I D) hD).symm v =
      elementary (I D) 0 (transportInverse D 0 (zeroCarry D hD) v) (eta0 hD) := by
  apply (classificationEquiv (I D) hD).injective
  rw [LinearEquiv.apply_symm_apply]
  change v = classified hD (I D) 0 (eta0 hD) _
  rw [unit_classified]
  exact ((transportLinearEquiv D 0 (zeroCarry D hD)).apply_symm_apply v).symm

theorem unit_vacuum_inverse :
    transportInverse D 0 (zeroCarry D hD) (vacuum D) =
      (epsilon D (-zeroCarry D hD) (zeroCarry D hD))⁻¹ •
        Finsupp.single (-zeroCarry D hD) (1 : Oscillator D) := by
  simp [vacuum, transportInverse_single]

section ArbitraryModule
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)

private def leftContraction (c : Discriminant D) :
    Multiplicity (I D) 0 ⊗[ℂ] Multiplicity A c →ₗ[ℂ] Multiplicity A c :=
  (TensorProduct.lid ℂ (Multiplicity A c)).toLinearMap.comp
    (TensorProduct.map (etaCoefficient hD) LinearMap.id)

private def rightContraction (c : Discriminant D) :
    Multiplicity A c ⊗[ℂ] Multiplicity (I D) 0 →ₗ[ℂ] Multiplicity A c :=
  (TensorProduct.rid ℂ (Multiplicity A c)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (etaCoefficient hD))

private def leftInsert (c : Discriminant D) :
    Multiplicity A c →ₗ[ℂ] Multiplicity (I D) 0 ⊗[ℂ] Multiplicity A c :=
  TensorProduct.mk ℂ _ _ (eta0 hD)

private def rightInsert (c : Discriminant D) :
    Multiplicity A c →ₗ[ℂ] Multiplicity A c ⊗[ℂ] Multiplicity (I D) 0 :=
  (TensorProduct.mk ℂ _ _).flip (eta0 hD)

private def leftBlock (cd : Discriminant D × Discriminant D) :
    PairSector (I D) A cd →ₗ[ℂ] Model A := by
  rcases cd with ⟨c,d⟩
  by_cases hc : c = 0
  · subst c
    exact (DirectSum.lof ℂ _ (Sector A) d).comp
      (TensorProduct.map (transport D (representative D d) (zeroCarry D hD))
        (leftContraction hD A d))
  · exact 0

private def rightBlock (cd : Discriminant D × Discriminant D) :
    PairSector A (I D) cd →ₗ[ℂ] Model A := by
  rcases cd with ⟨c,d⟩
  by_cases hd : d = 0
  · subst d
    exact unitCharacter D hD c • (DirectSum.lof ℂ _ (Sector A) c).comp
      (TensorProduct.map (transport D (representative D c) (zeroCarry D hD))
        (rightContraction hD A c))
  · exact 0

/-- Forward maps into the ORIGINAL classification model of A. -/
def leftModel : P (I D) A →ₗ[ℂ] Model A :=
  DirectSum.toModule ℂ _ _ (leftBlock hD A)
def rightModel : P A (I D) →ₗ[ℂ] Model A :=
  DirectSum.toModule ℂ _ _ (rightBlock hD A)

/-- Full inverse maps before applying the original classification inverse. -/
def leftUnmodel : Model A →ₗ[ℂ] P (I D) A :=
  DirectSum.toModule ℂ _ _ (fun c =>
    (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)).comp
      (TensorProduct.map (transportInverse D (representative D c) (zeroCarry D hD))
        (leftInsert hD A c)))
def rightUnmodel : Model A →ₗ[ℂ] P A (I D) :=
  DirectSum.toModule ℂ _ _ (fun c =>
    (unitCharacter D hD c)⁻¹ •
      (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)).comp
        (TensorProduct.map (transportInverse D (representative D c) (zeroCarry D hD))
          (rightInsert hD A c)))

@[simp] theorem leftModel_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    leftModel hD A (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x))) =
      elementary A c (transport D (representative D c) (zeroCarry D hD) v) x := by
  simp [leftModel, leftBlock, leftContraction, elementary]

@[simp] theorem rightModel_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightModel hD A (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD))) =
      unitCharacter D hD c •
        elementary A c (transport D (representative D c) (zeroCarry D hD) v) x := by
  simp [rightModel, rightBlock, rightContraction, elementary]

@[simp] theorem leftUnmodel_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    leftUnmodel hD A (elementary A c v x) =
      DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
        (transportInverse D (representative D c) (zeroCarry D hD) v ⊗ₜ[ℂ]
          (eta0 hD ⊗ₜ[ℂ] x)) := by
  simp [leftUnmodel, leftInsert, elementary]

@[simp] theorem rightUnmodel_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightUnmodel hD A (elementary A c v x) =
      (unitCharacter D hD c)⁻¹ • DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
        (transportInverse D (representative D c) (zeroCarry D hD) v ⊗ₜ[ℂ]
          (x ⊗ₜ[ℂ] eta0 hD)) := by
  simp [rightUnmodel, rightInsert, elementary]

/- These are finite elimination principles for the ORIGINAL P, justified by
   the just-proved actual ground multiplicities. No basis of X is selected. -/
private theorem left_ext {Z : Type v} [AddCommGroup Z] [Module ℂ Z]
    (f g : P (I D) A →ₗ[ℂ] Z)
    (he : ∀ c v x, f (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
        (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x))) =
      g (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
        (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x)))) : f = g := by
  apply DirectSum.linearMap_ext
  rintro ⟨c,d⟩
  apply TensorProduct.ext
  intro v w
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
  | tmul n x =>
    by_cases hc : c = 0
    · subst c
      rw [← etaCoefficient_inverse hD n]
      simpa only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul]
        using congrArg (fun z : Z => etaCoefficient hD n • z) (he d v x)
    · rw [unit_multiplicity_wrong hD c hc n]
      simp

private theorem right_ext {Z : Type v} [AddCommGroup Z] [Module ℂ Z]
    (f g : P A (I D) →ₗ[ℂ] Z)
    (he : ∀ c v x, f (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
        (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD))) =
      g (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
        (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD)))) : f = g := by
  apply DirectSum.linearMap_ext
  rintro ⟨c,d⟩
  apply TensorProduct.ext
  intro v w
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
  | tmul x n =>
    by_cases hd : d = 0
    · subst d
      rw [← etaCoefficient_inverse hD n]
      simpa only [TensorProduct.tmul_smul, map_smul]
        using congrArg (fun z : Z => etaCoefficient hD n • z) (he c v x)
    · rw [unit_multiplicity_wrong hD d hd n]
      simp

private theorem leftUnmodel_leftModel :
    (leftUnmodel hD A).comp (leftModel hD A) = LinearMap.id := by
  apply left_ext hD A
  intro c v x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, leftModel_elementary,
    leftUnmodel_elementary]
  congr 2
  exact (transportLinearEquiv D _ _).symm_apply_apply v

private theorem rightUnmodel_rightModel :
    (rightUnmodel hD A).comp (rightModel hD A) = LinearMap.id := by
  apply right_ext hD A
  intro c v x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, rightModel_elementary,
    map_smul, rightUnmodel_elementary, smul_smul]
  rw [mul_inv_cancel₀ (unitCharacter_nonzero D hD c), one_smul]
  congr 2
  exact (transportLinearEquiv D _ _).symm_apply_apply v

private theorem leftModel_leftUnmodel :
    (leftModel hD A).comp (leftUnmodel hD A) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro c
  apply TensorProduct.ext
  intro v x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, leftUnmodel_elementary,
    leftModel_elementary]
  congr 2
  exact (transportLinearEquiv D _ _).apply_symm_apply v

private theorem rightModel_rightUnmodel :
    (rightModel hD A).comp (rightUnmodel hD A) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro c
  apply TensorProduct.ext
  intro v x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, rightUnmodel_elementary,
    map_smul, rightModel_elementary, smul_smul]
  rw [inv_mul_cancel₀ (unitCharacter_nonzero D hD c), one_smul]
  congr 2
  exact (transportLinearEquiv D _ _).apply_symm_apply v

/-- Genuine units, with explicit functions on every original vector. -/
def leftUnit : P (I D) A ≃ₗ[ℂ] X where
  toLinearMap := (classificationEquiv A hD).toLinearMap.comp (leftModel hD A)
  invFun x := leftUnmodel hD A ((classificationEquiv A hD).symm x)
  left_inv p := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (leftUnmodel_leftModel hD A) p
  right_inv x := by
    change classificationEquiv A hD ((leftModel hD A).comp (leftUnmodel hD A)
      ((classificationEquiv A hD).symm x)) = x
    rw [leftModel_leftUnmodel, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

def rightUnit : P A (I D) ≃ₗ[ℂ] X where
  toLinearMap := (classificationEquiv A hD).toLinearMap.comp (rightModel hD A)
  invFun x := rightUnmodel hD A ((classificationEquiv A hD).symm x)
  left_inv p := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (rightUnmodel_rightModel hD A) p
  right_inv x := by
    change classificationEquiv A hD ((rightModel hD A).comp (rightUnmodel hD A)
      ((classificationEquiv A hD).symm x)) = x
    rw [rightModel_rightUnmodel, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

@[simp] theorem leftUnit_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    leftUnit hD A (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x))) =
      classified hD A c x (transport D (representative D c) (zeroCarry D hD) v) := by
  change classificationEquiv A hD (leftModel hD A _) = _
  rw [leftModel_elementary]
  rfl

@[simp] theorem rightUnit_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightUnit hD A (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD))) =
      chi D (representative D c) (zeroCarry D hD) •
        classified hD A c x (transport D (representative D c) (zeroCarry D hD) v) := by
  change classificationEquiv A hD (rightModel hD A _) = _
  rw [rightModel_elementary, map_smul]
  rfl

@[simp] theorem leftUnit_inverse_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    (leftUnit hD A).symm (classified hD A c x v) =
      DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
        (transportInverse D (representative D c) (zeroCarry D hD) v ⊗ₜ[ℂ]
          (eta0 hD ⊗ₜ[ℂ] x)) := by
  change leftUnmodel hD A ((classificationEquiv A hD).symm
    (classificationEquiv A hD (elementary A c v x))) = _
  rw [LinearEquiv.symm_apply_apply, leftUnmodel_elementary]

@[simp] theorem rightUnit_inverse_elementary (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    (rightUnit hD A).symm (classified hD A c x v) =
      (unitCharacter D hD c)⁻¹ • DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
        (transportInverse D (representative D c) (zeroCarry D hD) v ⊗ₜ[ℂ]
          (x ⊗ₜ[ℂ] eta0 hD)) := by
  change rightUnmodel hD A ((classificationEquiv A hD).symm
    (classificationEquiv A hD (elementary A c v x))) = _
  rw [LinearEquiv.symm_apply_apply, rightUnmodel_elementary]

private theorem left_shift (c : Discriminant D) :
    representative D 0 + representative D c =
      shiftedCharge D (representative D c) (zeroCarry D hD) := by
  rw [representative_zero D hD, shiftedCharge]
  abel
private theorem right_shift (c : Discriminant D) :
    representative D c + representative D 0 =
      shiftedCharge D (representative D c) (zeroCarry D hD) := by
  rw [representative_zero D hD, shiftedCharge]

theorem leftUnit_modes (a : Carrier D) (m : ℤ) (p : P (I D) A) :
    leftUnit hD A (mode (targetModule (I D) A) a m p) =
      mode A a m (leftUnit hD A p) := by
  have he : (leftUnit hD A).toLinearMap.comp (mode (targetModule (I D) A) a m) =
      (mode A a m).comp (leftUnit hD A).toLinearMap := by
    apply left_ext hD A
    intro c v x
    simp only [LinearMap.comp_apply]
    rw [targetModule, directSumModule_mode, DirectSum.lmap_lof,
      tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply,
      sectorModule_mode, leftUnit_elementary, leftUnit_elementary,
      left_shift, transport_all_modes]
    exact classified_modes hD A c x a _ m
  exact LinearMap.congr_fun he p

theorem rightUnit_modes (a : Carrier D) (m : ℤ) (p : P A (I D)) :
    rightUnit hD A (mode (targetModule A (I D)) a m p) =
      mode A a m (rightUnit hD A p) := by
  have he : (rightUnit hD A).toLinearMap.comp (mode (targetModule A (I D)) a m) =
      (mode A a m).comp (rightUnit hD A).toLinearMap := by
    apply right_ext hD A
    intro c v x
    simp only [LinearMap.comp_apply]
    rw [targetModule, directSumModule_mode, DirectSum.lmap_lof,
      tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply,
      sectorModule_mode, rightUnit_elementary, rightUnit_elementary,
      right_shift, transport_all_modes, map_smul]
    congr 1
    exact classified_modes hD A c x a _ m
  exact LinearMap.congr_fun he p

def leftUnitIso : ModuleIso (targetModule (I D) A) A where
  linearEquiv := leftUnit hD A
  intertwines := leftUnit_modes hD A

def rightUnitIso : ModuleIso (targetModule A (I D)) A where
  linearEquiv := rightUnit hD A
  intertwines := rightUnit_modes hD A

/-- This is the supplier j/classification readback on the actual product,
    specialized to the unit. It also fixes the inverse transport normalization. -/
theorem leftUnit_classification_j (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    leftUnit hD A (classificationEquiv (targetModule (I D) A) hD
      (DirectSum.lof ℂ _ _ (0+c)
        (v ⊗ₜ[ℂ] ActualWeakModuleProductMultiplicity.j (I D) A hD 0 c
          (eta0 hD ⊗ₜ[ℂ] x)))) = classified hD A c x v := by
  rw [ActualWeakModuleProductMultiplicity.classification_j, leftUnit_elementary]
  simp only [zero_add, LatticeChargedQuotientScalar.carry_zero_left]
  congr 1
  exact (transportLinearEquiv D _ _).apply_symm_apply v

theorem rightUnit_classification_j (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightUnit hD A (classificationEquiv (targetModule A (I D)) hD
      (DirectSum.lof ℂ _ _ (c+0)
        (v ⊗ₜ[ℂ] ActualWeakModuleProductMultiplicity.j A (I D) hD c 0
          (x ⊗ₜ[ℂ] eta0 hD)))) = unitCharacter D hD c • classified hD A c x v := by
  rw [ActualWeakModuleProductMultiplicity.classification_j, rightUnit_elementary]
  simp only [add_zero, LatticeChargedQuotientScalar.carry_zero_right]
  congr 2
  exact (transportLinearEquiv D _ _).apply_symm_apply v

private theorem leftUnit_j0 (c : Discriminant D)
    (z : Multiplicity (I D) 0 ⊗[ℂ] Multiplicity A c) :
    leftUnit hD A (ActualWeakModuleProductMultiplicity.j (I D) A hD 0 c z).val.val =
      (leftContraction hD A c z).val.val := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, Submodule.coe_add, hz, hw]
  | tmul n x =>
    have hh := leftUnit_classification_j hD A c (vacuum D) x
    have hbase : leftUnit hD A
        (ActualWeakModuleProductMultiplicity.j (I D) A hD 0 c
          (eta0 hD ⊗ₜ[ℂ] x)).val.val = x.val.val := by
      simpa only [classified, LinearMap.comp_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply, classification_normalization] using hh
    rw [← etaCoefficient_inverse hD n]
    simpa [leftContraction, ← TensorProduct.smul_tmul', Submodule.coe_smul,
      map_smul] using congrArg (fun z : X => etaCoefficient hD n • z) hbase

private theorem rightUnit_j0 (c : Discriminant D)
    (z : Multiplicity A c ⊗[ℂ] Multiplicity (I D) 0) :
    rightUnit hD A (ActualWeakModuleProductMultiplicity.j A (I D) hD c 0 z).val.val =
      unitCharacter D hD c • (rightContraction hD A c z).val.val := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, Submodule.coe_add, hz, hw, smul_add]
  | tmul x n =>
    have hh := rightUnit_classification_j hD A c (vacuum D) x
    have hbase : rightUnit hD A
        (ActualWeakModuleProductMultiplicity.j A (I D) hD c 0
          (x ⊗ₜ[ℂ] eta0 hD)).val.val = unitCharacter D hD c • x.val.val := by
      simpa only [classified, LinearMap.comp_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply, classification_normalization] using hh
    rw [← etaCoefficient_inverse hD n]
    simpa [rightContraction, TensorProduct.tmul_smul, Submodule.coe_smul,
      map_smul, smul_smul, mul_comm] using
        congrArg (fun z : X => etaCoefficient hD n • z) hbase

/-- Actual ground readback through the supplier mu, with nu_mu exhausting the
    original nested subtype. All wrong fiber components vanish, including zero X. -/
theorem leftUnit_ground_mu (e : Discriminant D)
    (w : Multiplicity (targetModule (I D) A) e) :
    leftUnit hD A w.val.val =
      (leftContraction hD A e
        (ActualWeakModuleProductMultiplicity.mu (I D) A hD e w
          (⟨(0,e), zero_add e⟩ : ActualWeakModuleProductMultiplicity.Fiber e))).val.val := by
  have hf : ∀ z : ActualWeakModuleProductMultiplicity.FiberSum (I D) A e,
      leftUnit hD A (ActualWeakModuleProductMultiplicity.nu (I D) A hD e z).val.val =
        (leftContraction hD A e
          (z (⟨(0,e), zero_add e⟩ : ActualWeakModuleProductMultiplicity.Fiber e))).val.val := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simp only [map_add, Submodule.coe_add, DFinsupp.add_apply, hz, hz']
    | of i z =>
      rcases i with ⟨⟨c,d⟩,hi⟩
      by_cases hc : c = 0
      · subst c
        have hd : d = e := by simpa only [zero_add] using hi
        subst d
        simpa [ActualWeakModuleProductMultiplicity.nu_lof,
          ActualWeakModuleProductMultiplicity.jAt, DirectSum.lof_eq_of] using leftUnit_j0 hD A e z
      · have hz : z = 0 := by
          induction z using TensorProduct.inductionOn with
          | tmul n x => rw [unit_multiplicity_wrong hD c hc n]; simp
          | add z z' hz hz' => simp only [hz,hz',add_zero]
        subst z
        simp
  have hh := hf (ActualWeakModuleProductMultiplicity.mu (I D) A hD e w)
  rw [ActualWeakModuleProductMultiplicity.nu_mu] at hh
  exact hh

/-- The right readback retains the nonnormalized character after the same
    ORIGINAL mu/nu exhaustion; no replacement multiplicity is introduced. -/
theorem rightUnit_ground_mu (e : Discriminant D)
    (w : Multiplicity (targetModule A (I D)) e) :
    rightUnit hD A w.val.val = unitCharacter D hD e •
      (rightContraction hD A e
        (ActualWeakModuleProductMultiplicity.mu A (I D) hD e w
          (⟨(e,0), add_zero e⟩ : ActualWeakModuleProductMultiplicity.Fiber e))).val.val := by
  have hf : ∀ z : ActualWeakModuleProductMultiplicity.FiberSum A (I D) e,
      rightUnit hD A (ActualWeakModuleProductMultiplicity.nu A (I D) hD e z).val.val =
        unitCharacter D hD e • (rightContraction hD A e
          (z (⟨(e,0), add_zero e⟩ : ActualWeakModuleProductMultiplicity.Fiber e))).val.val := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simp only [map_add, Submodule.coe_add, DFinsupp.add_apply, hz, hz', smul_add]
    | of i z =>
      rcases i with ⟨⟨c,d⟩,hi⟩
      by_cases hd : d = 0
      · subst d
        have hc : c = e := by simpa only [add_zero] using hi
        subst c
        simpa [ActualWeakModuleProductMultiplicity.nu_lof,
          ActualWeakModuleProductMultiplicity.jAt, DirectSum.lof_eq_of] using rightUnit_j0 hD A e z
      · have hz : z = 0 := by
          induction z using TensorProduct.inductionOn with
          | tmul x n => rw [unit_multiplicity_wrong hD d hd n]; simp
          | add z z' hz hz' => simp only [hz,hz',add_zero]
        subst z
        simp
  have hh := hf (ActualWeakModuleProductMultiplicity.mu A (I D) hD e w)
  rw [ActualWeakModuleProductMultiplicity.nu_mu] at hh
  exact hh

/-- These inverse expansions use the actual vector's finite classification
    support; the tensor factors remain arbitrary algebraic tensors. -/
theorem leftUnit_inverse_finite (x : X) :
    let s := (classificationEquiv A hD).symm x
    (leftUnit hD A).symm x = ∑ c ∈ s.support,
      DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
        (TensorProduct.map (transportInverse D (representative D c) (zeroCarry D hD))
          (leftInsert hD A c) (s c)) := by
  classical
  dsimp only
  let s := (classificationEquiv A hD).symm x
  have hs : (∑ c ∈ s.support, DirectSum.lof ℂ _ (Sector A) c (s c)) = s := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of s
  change leftUnmodel hD A s = _
  conv_lhs => rw [← hs]
  simp only [map_sum, leftUnmodel, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem rightUnit_inverse_finite (x : X) :
    let s := (classificationEquiv A hD).symm x
    (rightUnit hD A).symm x = ∑ c ∈ s.support,
      (unitCharacter D hD c)⁻¹ • DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
        (TensorProduct.map (transportInverse D (representative D c) (zeroCarry D hD))
          (rightInsert hD A c) (s c)) := by
  classical
  dsimp only
  let s := (classificationEquiv A hD).symm x
  have hs : (∑ c ∈ s.support, DirectSum.lof ℂ _ (Sector A) c (s c)) = s := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of s
  change rightUnmodel hD A s = _
  conv_lhs => rw [← hs]
  simp only [map_sum, rightUnmodel, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearMap.smul_apply]

private theorem left_two_leg (c : Discriminant D) (u v : Carrier D) (q : ℚ) :
    transport D (representative D c) (zeroCarry D hD)
      ((LatticeCosetCanonicalUnits.C D (representative D 0) (representative D c)
        (transportInverse D 0 (zeroCarry D hD) u)).coeff q v) =
      (LatticeCosetCanonicalUnits.C D 0 (representative D c) u).coeff q v := by
  have hh := two_leg_coeff D hD 0 (representative D c) (zeroCarry D hD) 0
    (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
    (transportInverse D 0 (zeroCarry D hD) u) v q
  have hi : transport D 0 (zeroCarry D hD)
      (transportInverse D 0 (zeroCarry D hD) u) = u :=
    (transportLinearEquiv D _ _).apply_symm_apply u
  simpa [LatticeCosetCanonicalUnits.C, hi, shiftedCharge, representative_zero D hD,
    chi, paritySign] using hh.symm

private theorem right_two_leg (c : Discriminant D) (u v : Carrier D) (q : ℚ) :
    unitCharacter D hD c • transport D (representative D c) (zeroCarry D hD)
      ((LatticeCosetCanonicalUnits.C D (representative D c) (representative D 0) u).coeff q
        (transportInverse D 0 (zeroCarry D hD) v)) =
      (LatticeCosetCanonicalUnits.C D (representative D c) 0 u).coeff q v := by
  have hh := two_leg_coeff D hD (representative D c) 0 0 (zeroCarry D hD)
    (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
    u (transportInverse D 0 (zeroCarry D hD) v) q
  have hi : transport D 0 (zeroCarry D hD)
      (transportInverse D 0 (zeroCarry D hD) v) = v :=
    (transportLinearEquiv D _ _).apply_symm_apply v
  simpa [LatticeCosetCanonicalUnits.C, hi, shiftedCharge, representative_zero D hD,
    unitCharacter] using hh.symm

/-- The actual raw rational coefficient, with the full unnormalized unit slot. -/
theorem leftUnit_U_elementary (c : Discriminant D) (u v : Carrier D)
    (x : Multiplicity A c) (q : ℚ) :
    leftUnit hD A ((U (I D) A hD u).coeff q (classified hD A c x v)) =
      classified hD A c x
        ((LatticeCosetCanonicalUnits.C D 0 (representative D c) u).coeff q v) := by
  have hu : classified hD (I D) 0 (eta0 hD)
      (transportInverse D 0 (zeroCarry D hD) u) = u := by
    rw [unit_classified]
    exact (transportLinearEquiv D _ _).apply_symm_apply u
  conv_lhs => rw [← hu]
  change leftUnit hD A ((U (I D) A hD
    (classificationEquiv (I D) hD (elementary (I D) 0 _ (eta0 hD)))).coeff q
      (classificationEquiv A hD (elementary A c v x))) = _
  rw [ActualWeakModuleUniversalField.U_elementary_coeff, leftUnit_elementary,
    left_two_leg]

theorem rightUnit_U_elementary (c : Discriminant D) (u v : Carrier D)
    (x : Multiplicity A c) (q : ℚ) :
    rightUnit hD A ((U A (I D) hD (classified hD A c x u)).coeff q v) =
      classified hD A c x
        ((LatticeCosetCanonicalUnits.C D (representative D c) 0 u).coeff q v) := by
  have hv : classified hD (I D) 0 (eta0 hD)
      (transportInverse D 0 (zeroCarry D hD) v) = v := by
    rw [unit_classified]
    exact (transportLinearEquiv D _ _).apply_symm_apply v
  conv_lhs => rw [← hv]
  change rightUnit hD A ((U A (I D) hD
    (classificationEquiv A hD (elementary A c u x))).coeff q
      (classificationEquiv (I D) hD (elementary (I D) 0 _ (eta0 hD)))) = _
  rw [ActualWeakModuleUniversalField.U_elementary_coeff, rightUnit_elementary]
  change unitCharacter D hD c • classified hD A c x _ = _
  rw [← map_smul, right_two_leg]

private theorem classified_induction (Q : X → Prop) (h0 : Q 0)
    (hadd : ∀ x y, Q x → Q y → Q (x+y))
    (he : ∀ c v x, Q (classified hD A c x v)) (x : X) : Q x := by
  have hh := model_induction A (fun s => Q (classificationEquiv A hD s))
    (by simpa only [map_zero] using h0)
    (fun s t hs ht => by simpa only [map_add] using hadd _ _ hs ht)
    (fun c v n => he c v n) ((classificationEquiv A hD).symm x)
  simpa only [LinearEquiv.apply_symm_apply] using hh

/-- Every original source state, integer raw exponent, and original input. -/
theorem leftUnit_U_integer (v : Carrier D) (x : X) (k : ℤ) :
    leftUnit hD A ((U (I D) A hD v).coeff (k : ℚ) x) =
      mode A v (-k-1) x := by
  apply classified_induction hD A
    (fun x => leftUnit hD A ((U (I D) A hD v).coeff (k : ℚ) x) = mode A v (-k-1) x)
    (by simp) (fun x y hx hy => by simpa only [map_add, Pi.add_apply, LinearMap.add_apply, hx,hy]) ?_ x
  intro c u n
  rw [leftUnit_U_elementary, LatticeCosetCanonicalUnits.canonical_zero_left_integer]
  exact classified_modes hD A c n v u (-k-1)

theorem leftUnit_U_off (v : Carrier D) (x : X) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℤ => (k : ℚ))) :
    leftUnit hD A ((U (I D) A hD v).coeff q x) = 0 := by
  apply classified_induction hD A
    (fun x => leftUnit hD A ((U (I D) A hD v).coeff q x) = 0)
    (by simp) (fun x y hx hy => by simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx,hy,add_zero]) ?_ x
  intro c u n
  rw [leftUnit_U_elementary, LatticeCosetCanonicalUnits.canonical_zero_left_off D _ _ _ q hq,
    map_zero]

theorem rightUnit_U_off (x : X) (v : Carrier D) (q : ℚ)
    (hq : q ∉ Set.range (fun k : ℤ => (k : ℚ))) :
    rightUnit hD A ((U A (I D) hD x).coeff q v) = 0 := by
  apply classified_induction hD A
    (fun x => rightUnit hD A ((U A (I D) hD x).coeff q v) = 0)
    (by simp) (fun x y hx hy => by
      simpa only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hy, add_zero]) ?_ x
  intro c u n
  rw [rightUnit_U_elementary, LatticeCosetCanonicalUnits.canonical_right_off D _ _ _ q hq,
    map_zero]

private theorem classified_translation (c : Discriminant D) (n : Multiplicity A c)
    (u : Carrier D) :
    classified hD A c n (LatticeCosetCanonicalUnits.sectorTranslation D hD (representative D c) u) =
      translation A hD (classified hD A c n u) :=
  classified_modes hD A c n (LatticeActualConformalState.omega D (inverseGram hD)) u 0

private theorem classified_translation_pow (c : Discriminant D) (n : Multiplicity A c)
    (r : ℕ) (u : Carrier D) :
    classified hD A c n (((LatticeCosetCanonicalUnits.sectorTranslation D hD (representative D c))^r) u) =
      ((translation A hD)^r) (classified hD A c n u) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, classified_translation, ih,
      pow_succ', Module.End.mul_apply]

theorem rightUnit_U_vacuum_nat (x : X) (r : ℕ) :
    rightUnit hD A ((U A (I D) hD x).coeff (r : ℚ) (vacuum D)) =
      (r.factorial : ℂ)⁻¹ • ((translation A hD)^r) x := by
  apply classified_induction hD A
    (fun x => rightUnit hD A ((U A (I D) hD x).coeff (r : ℚ) (vacuum D)) =
      (r.factorial : ℂ)⁻¹ • ((translation A hD)^r) x)
    (by simp) (fun x y hx hy => by
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hy, smul_add]) ?_ x
  intro c u n
  rw [rightUnit_U_elementary, LatticeCosetCanonicalUnits.canonical_right_creation_nat,
    map_smul, classified_translation_pow]

theorem rightUnit_U_vacuum_support (x : X) (q : ℚ)
    (hq : q ∉ Set.range (fun r : ℕ => (r : ℚ))) :
    rightUnit hD A ((U A (I D) hD x).coeff q (vacuum D)) = 0 := by
  apply classified_induction hD A
    (fun x => rightUnit hD A ((U A (I D) hD x).coeff q (vacuum D)) = 0)
    (by simp) (fun x y hx hy => by
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hy, add_zero]) ?_ x
  intro c u n
  rw [rightUnit_U_elementary,
    LatticeCosetCanonicalUnits.canonical_right_creation_support D _ _ q hq, map_zero]

/- The finite translated reversed coefficient is a linear map for EACH N,k.
   T here is literally the original target omega-zero, not a new translation. -/
private def reversedCoefficient (v : Carrier D) (k : ℤ) (N : ℕ) : Module.End ℂ X :=
  ∑ i ∈ Finset.range (((N : ℤ)+k+1).toNat),
    (((-1 : ℂ)^(k-(i : ℤ))) / (i.factorial : ℂ)) •
      (((translation A hD)^i).comp (mode A v ((i : ℤ)-k-1)))

private theorem reversedCoefficient_apply (v : Carrier D) (k : ℤ) (N : ℕ) (x : X) :
    reversedCoefficient hD A v k N x =
      ∑ i ∈ Finset.range (((N : ℤ)+k+1).toNat),
        (((-1 : ℂ)^(k-(i : ℤ))) / (i.factorial : ℂ)) •
          ((translation A hD)^i) (mode A v ((i : ℤ)-k-1) x) := by
  simp only [reversedCoefficient, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]

private def rightCoefficient (q : ℚ) (v : Carrier D) : X →ₗ[ℂ] X where
  toFun x := rightUnit hD A ((U A (I D) hD x).coeff q v)
  map_add' x y := by
    change rightUnit hD A (((HahnModule.of ℂ).symm (U A (I D) hD (x+y) v)).coeff q) = _
    simp only [map_add, LinearMap.add_apply, HahnModule.of_symm_add, HahnSeries.coeff_add]
  map_smul' a x := by
    change rightUnit hD A (((HahnModule.of ℂ).symm (U A (I D) hD (a • x) v)).coeff q) = _
    simp only [map_smul, LinearMap.smul_apply, HahnModule.of_symm_smul,
      HahnSeries.coeff_smul, RingHom.id_apply]

private theorem rightCoefficient_elementary (c : Discriminant D) (u v : Carrier D)
    (n : Multiplicity A c) (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → ((action D (representative D c) v)[[m]]) u = 0) :
    rightCoefficient hD A (k : ℚ) v (classified hD A c n u) =
      reversedCoefficient hD A v k N (classified hD A c n u) := by
  change rightUnit hD A ((U A (I D) hD (classified hD A c n u)).coeff (k : ℚ) v) = _
  rw [rightUnit_U_elementary,
    LatticeCosetCanonicalUnits.canonical_right_general_integer D hD _ u v k N hN,
    map_sum, reversedCoefficient_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, classified_translation_pow, classified_modes]

/-- A finite classified presentation supplies a bound; addition takes maxima.
    No cutoff over translated/intermediate states is used. -/
private theorem rightCoefficient_eventually (v : Carrier D) (x : X) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      (∀ m : ℤ, (M : ℤ) ≤ m → mode A v m x = 0) ∧
      (∀ k : ℤ, rightCoefficient hD A (k : ℚ) v x = reversedCoefficient hD A v k M x) := by
  refine classified_induction hD A (fun x => ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      (∀ m : ℤ, (M : ℤ) ≤ m → mode A v m x = 0) ∧
      (∀ k : ℤ, rightCoefficient hD A (k : ℚ) v x = reversedCoefficient hD A v k M x))
    ?_ ?_ ?_ x
  · exact ⟨0, fun M hM => ⟨by simp, by simp⟩⟩
  · intro x y hx hy
    obtain ⟨N,hN⟩ := hx
    obtain ⟨L,hL⟩ := hy
    refine ⟨max N L, ?_⟩
    intro M hM
    obtain ⟨hx0,hxk⟩ := hN M (le_trans (le_max_left _ _) hM)
    obtain ⟨hy0,hyk⟩ := hL M (le_trans (le_max_right _ _) hM)
    constructor
    · intro m hm
      rw [map_add, hx0 m hm, hy0 m hm, add_zero]
    · intro k
      rw [map_add, map_add, hxk k, hyk k]
  · intro c u n
    obtain ⟨N,hN⟩ := LatticeCosetCanonicalUnits.original_pair_cutoff D (representative D c) u v
    refine ⟨N, ?_⟩
    intro M hM
    have hMN : ∀ m : ℤ, (M : ℤ) ≤ m →
        ((action D (representative D c) v)[[m]]) u = 0 := by
      intro m hm
      exact hN m (by omega)
    constructor
    · intro m hm
      rw [← classified_modes hD A c n v u m, sectorModule_mode, hMN m hm, map_zero]
    · intro k
      exact rightCoefficient_elementary hD A c u v n k M hMN

/-- Any bound for the ORIGINAL pair works, even if that bound uses cancellation
    between terms in a classified presentation. Its whole tail is literally zero. -/
private theorem reversedCoefficient_cutoff (v : Carrier D) (x : X) (k : ℤ) (N M : ℕ)
    (hNM : N ≤ M)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → mode A v m x = 0) :
    reversedCoefficient hD A v k M x = reversedCoefficient hD A v k N x := by
  classical
  rw [reversedCoefficient_apply, reversedCoefficient_apply]
  symm
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i hi hin
    have hiN : (((N : ℤ)+k+1).toNat) ≤ i := by
      simpa only [Finset.mem_range, not_lt] using hin
    rw [hN ((i : ℤ)-k-1) (by omega), map_zero, smul_zero]

/-- Full original right field diagram, with the exact requested fixed-pair N.
    Negative N+k gives the empty sum. Off-integer coefficients are above. -/
theorem rightUnit_U_general_integer (x : X) (v : Carrier D) (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → mode A v m x = 0) :
    rightUnit hD A ((U A (I D) hD x).coeff (k : ℚ) v) =
      ∑ i ∈ Finset.range (((N : ℤ)+k+1).toNat),
        (((-1 : ℂ)^(k-(i : ℤ))) / (i.factorial : ℂ)) •
          ((translation A hD)^i) (mode A v ((i : ℤ)-k-1) x) := by
  obtain ⟨L,hL⟩ := rightCoefficient_eventually hD A v x
  have hk := (hL (max L N) (le_max_left _ _)).2 k
  exact hk.trans ((reversedCoefficient_cutoff hD A v x k N (max L N)
    (le_max_right _ _) hN).trans (reversedCoefficient_apply hD A v k N x))

/-- Pairwise support of the actual right-unit U diagram. -/
theorem rightUnit_U_below_cutoff (x : X) (v : Carrier D) (k : ℤ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → mode A v m x = 0)
    (hk : k < -(N : ℤ)) :
    rightUnit hD A ((U A (I D) hD x).coeff (k : ℚ) v) = 0 := by
  rw [rightUnit_U_general_integer hD A x v k N hN]
  have he : ((N : ℤ)+k+1).toNat = 0 := by omega
  simp only [he, Finset.range_zero, Finset.sum_empty]

/-- Each original pair has a finite cutoff; it is not an extra module premise. -/
theorem module_pair_cutoff (v : Carrier D) (x : X) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → mode A v m x = 0 := by
  obtain ⟨L,hL⟩ := module_truncation A v x
  refine ⟨L.toNat, ?_⟩
  intro m hm
  exact hL m (by omega)

end ArbitraryModule
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
