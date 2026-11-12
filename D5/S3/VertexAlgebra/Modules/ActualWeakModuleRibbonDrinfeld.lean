/- GID: D5/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonDrinfeld
   mirror-B: D5/B/S3/VertexAlgebra/Modules/ActualWeakModuleRibbonDrinfeld
   status: source-only proposed proof bodies; native/kernel false. -/
/- SOURCE ONLY. The five arrows below are literal original module arrows.
No hexagon source is reconstructed and no native acceptance is asserted. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotalMonoidality

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
open ActualWeakModuleUnitCoherence
open ActualWeakModuleBalancing (theta thetaScalar restrict_theta)

open private restrict_extend from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private restrict_identity from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private pairAt hom_ext_classified chosen_contract_dual from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualitySnakes
open private carry_symm from D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
open private restrict_comp pivotal_classified bidualIota from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality

universe u
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Head
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- The actual forward braided cap, consumed by the Drinfeld composite. -/
private def braidedCap : ModuleHom (targetModule A (dualModule A)) (I D) :=
  (evaluation A hD).comp (ActualWeakModuleBraiding.braidIso A (dualModule A)).hom

private theorem braidedCap_wrong (e : Discriminant D) (he : e ≠ 0)
    (z : Multiplicity (targetModule A (dualModule A)) e) :
    restrict (braidedCap A hD) e z = 0 := by
  rw [braidedCap, restrict_comp, evaluation_wrong A hD e he]

/-- The original normalized ground is symmetric in its two labels, because
carry is symmetric. No epsilon arguments are exchanged. -/
private theorem braidedCap_jAt (c : Discriminant D) (x : Multiplicity A c)
    (z : Multiplicity (dualModule A) (-c)) :
    restrict (braidedCap A hD) 0
      (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩ (x ⊗ₜ[ℂ] z)) =
      (unitCharacter D hD (-c) * ActualWeakModuleBraiding.phase c (-c) *
        dualMultiplicityEquiv A hD c z x) • eta0 hD := by
  obtain ⟨φ,rfl⟩ := (dualMultiplicityEquiv A hD c).symm.surjective z
  have hb : restrict (ActualWeakModuleBraiding.braidIso A (dualModule A)).hom 0
      (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (x ⊗ₜ[ℂ] (dualMultiplicityEquiv A hD c).symm φ)) =
      ActualWeakModuleBraiding.phase c (-c) •
        jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
          ((dualMultiplicityEquiv A hD c).symm φ ⊗ₜ[ℂ] x) := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [jAt_val, Submodule.coe_smul]
    change ActualWeakModuleBraiding.braid A (dualModule A)
      (tag A (dualModule A) c (-c) x _ (ground hD c (-c))) = _
    rw [ActualWeakModuleBraiding.braid_tag]
    simp only [ground, carry_symm hD c (-c)]
    rfl
  rw [braidedCap, restrict_comp, hb, map_smul]
  have he := evaluation_jAt A hD c φ x
  simp only [dualMultiplicityEquiv_symm_apply, dualIota, neg_neg] at he ⊢
  rw [he]
  simp only [LinearEquiv.apply_symm_apply, smul_smul]
  congr 1
  ring

/-- Every wrong cup summand is killed at the actual cap. -/
private theorem drinfeld_tail_wrong (c d : Discriminant D) (hd : c+d ≠ 0)
    (x : Multiplicity A c) (m : Multiplicity (dualModule A) d)
    (φ : Module.Dual ℂ (Multiplicity (dualModule A) d)) (v : Carrier D) :
    leftUnit hD (dualModule (dualModule A))
      ((productHom hD (braidedCap A hD) (ModuleHom.id (dualModule (dualModule A)))).linearMap
        (alphaInverse A (dualModule A) (dualModule (dualModule A)) hD
          (normalizedPair A (targetModule (dualModule A) (dualModule (dualModule A))) hD c 0
            (x ⊗ₜ[ℂ] jAt (dualModule A) (dualModule (dualModule A)) hD 0
              ⟨(d,-d),add_neg_cancel d⟩ (m ⊗ₜ[ℂ] dualIota (dualModule A) d φ)) v))) = 0 := by
  rw [alphaInverse_normalized_fibers A (dualModule A) (dualModule (dualModule A)) hD
    c d (-d) (c+d) 0 rfl (add_neg_cancel d), map_smul, map_smul,
    normalizedPair_input, TensorProduct.map_tmul,
    braidedCap_wrong A hD (c+d) hd, restrict_identity]
  simp [normalizedPair]

/-- The surviving summand retains the inverse original associator and the
forward braid. Its later cup coefficient cancels that inverse F. -/
private theorem drinfeld_tail_matching (c : Discriminant D) (x : Multiplicity A c)
    (m : Multiplicity (dualModule A) (-c))
    (φ : Module.Dual ℂ (Multiplicity (dualModule A) (-c))) (v : Carrier D) :
    leftUnit hD (dualModule (dualModule A))
      ((productHom hD (braidedCap A hD) (ModuleHom.id (dualModule (dualModule A)))).linearMap
        (alphaInverse A (dualModule A) (dualModule (dualModule A)) hD
          (normalizedPair A (targetModule (dualModule A) (dualModule (dualModule A))) hD c 0
            (x ⊗ₜ[ℂ] jAt (dualModule A) (dualModule (dualModule A)) hD 0
              ⟨(-c,c),neg_add_cancel c⟩ (m ⊗ₜ[ℂ] bidualIota A c φ)) v))) =
      ((F hD c (-c) c)⁻¹ * unitCharacter D hD (-c) *
        ActualWeakModuleBraiding.phase c (-c)) •
        (dualMultiplicityEquiv A hD c m x •
          classified hD (dualModule (dualModule A)) c (bidualIota A c φ) v) := by
  rw [alphaInverse_normalized_fibers A (dualModule A) (dualModule (dualModule A)) hD
    c (-c) c 0 0 (add_neg_cancel c) (neg_add_cancel c), map_smul, map_smul,
    normalizedPair_input, TensorProduct.map_tmul, braidedCap_jAt, restrict_identity,
    TensorProduct.smul_tmul', normalizedPair_smul, map_smul, leftUnit_normalized]
  simp only [smul_smul]
  congr 1
  ring

end Head

section Finite
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- Literal right-unitor inverse, cup of DA, inverse associator, braided cap,
and left unitor. This is a map on the original carrier. -/
def drinfeldHom : ModuleHom A (dualModule (dualModule A)) := by
  letI : ∀ c : Discriminant D, Module.Finite ℂ (Multiplicity (dualModule A) c) :=
    fun c => Module.Finite.equiv
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD c).symm
  exact (leftUnitIso hD (dualModule (dualModule A))).hom.comp
    ((productHom hD (braidedCap A hD) (ModuleHom.id (dualModule (dualModule A)))).comp
      ((associatorIso A (dualModule A) (dualModule (dualModule A)) hD).inv.comp
        ((productHom hD (ModuleHom.id A) (coevaluation (dualModule A) hD)).comp
          (rightUnitIso hD A).inv)))

def drinfeldScalar (c : Discriminant D) : ℂ :=
  unitCharacter D hD (-c) * ActualWeakModuleBraiding.phase c (-c) / unitCharacter D hD c

/-- The finite cup sum is evaluated on EVERY dual multiplicity test. All
summands d != -c vanish; the surviving algebraic dual contraction is supplied
by the original finite snake, rather than by a finite oscillator assumption. -/
private theorem drinfeld_classified (c : Discriminant D) (x : Multiplicity A c)
    (v : Carrier D) :
    (drinfeldHom A hD).linearMap (classified hD A c x v) =
      drinfeldScalar hD c •
        classified hD (dualModule (dualModule A)) c (bidualFamily A hD c x) v := by
  letI : ∀ c : Discriminant D, Module.Finite ℂ (Multiplicity (dualModule A) c) :=
    fun c => Module.Finite.equiv
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD c).symm
  let T : Multiplicity
      (targetModule (dualModule A) (dualModule (dualModule A))) 0 →ₗ[ℂ]
        DualCarrier (dualModule A) :=
    (leftUnit hD (dualModule (dualModule A))).toLinearMap.comp
      ((productHom hD (braidedCap A hD) (ModuleHom.id (dualModule (dualModule A)))).linearMap.comp
        ((alphaInverse A (dualModule A) (dualModule (dualModule A)) hD).comp
          ((pairAt A (targetModule (dualModule A) (dualModule (dualModule A))) hD c 0 v).comp
            ((TensorProduct.mk ℂ _ _) x))))
  have hi : (rightUnit hD A).symm (classified hD A c x v) =
      (unitCharacter D hD c)⁻¹ •
        normalizedPair A (I D) hD c 0 (x ⊗ₜ[ℂ] eta0 hD) v := by
    apply (rightUnit hD A).injective
    rw [LinearEquiv.apply_symm_apply, map_smul, rightUnit_normalized, smul_smul,
      inv_mul_cancel₀ (unitCharacter_nonzero D hD c), one_smul]
  change leftUnit hD (dualModule (dualModule A))
    ((productHom hD (braidedCap A hD) (ModuleHom.id (dualModule (dualModule A)))).linearMap
      (alphaInverse A (dualModule A) (dualModule (dualModule A)) hD
        ((productHom hD (ModuleHom.id A) (coevaluation (dualModule A) hD)).linearMap
          ((rightUnit hD A).symm (classified hD A c x v))))) = _
  rw [hi]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity, coevaluation_eta0]
  change (unitCharacter D hD c)⁻¹ • T (cupVector (dualModule A) hD) = _
  rw [cupVector_expansion, map_sum]
  have hw (d : Discriminant D) (hd : d ≠ -c) :
      T (F hD (-d) d (-d) •
        jAt (dualModule A) (dualModule (dualModule A)) hD 0
          ⟨(d,-d),add_neg_cancel d⟩ (cupTensor (dualModule A) d)) = 0 := by
    have he : c+d ≠ 0 := by
      intro h
      apply hd
      calc d = -c+(c+d) := by abel
           _ = -c := by rw [h, add_zero]
    rw [map_smul, cupTensor_basis, map_sum, map_sum]
    have hz : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity (dualModule A) d),
      T (jAt (dualModule A) (dualModule (dualModule A)) hD 0
        ⟨(d,-d),add_neg_cancel d⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) d) i ⊗ₜ[ℂ]
          dualIota (dualModule A) d
            ((Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) d)).coord i)))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact drinfeld_tail_wrong A hD c d he x _ _ v
    rw [hz, smul_zero]
  rw [Finset.sum_eq_single (-c) (fun d hd hdc => hw d hdc) (by simp)]
  rw [map_smul, cupTensor_basis, map_sum, map_sum]
  let e : Module.Dual ℂ (Multiplicity (dualModule A) (-c)) :=
    (dualMultiplicityEquiv A hD c).dualMap (Module.Dual.eval ℂ (Multiplicity A c) x)
  have hb : bidualIota A c e = bidualFamily A hD c x := by
    simp only [bidualIota, bidualFamily, LinearMap.comp_apply, e]
  have hs : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity (dualModule A) (-c)),
      T (jAt (dualModule A) (dualModule (dualModule A)) hD 0
        ⟨(-c,c),neg_add_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c)) i ⊗ₜ[ℂ]
          bidualIota A c
            ((Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c))).coord i)))) =
      ((F hD c (-c) c)⁻¹ * unitCharacter D hD (-c) *
        ActualWeakModuleBraiding.phase c (-c)) •
          classified hD (dualModule (dualModule A)) c (bidualFamily A hD c x) v := by
    simp_rw [show ∀ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity (dualModule A) (-c)),
      T (jAt (dualModule A) (dualModule (dualModule A)) hD 0
        ⟨(-c,c),neg_add_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c)) i ⊗ₜ[ℂ]
          bidualIota A c
            ((Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c))).coord i))) =
        ((F hD c (-c) c)⁻¹ * unitCharacter D hD (-c) *
          ActualWeakModuleBraiding.phase c (-c)) •
          (e (Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c)) i) •
            classified hD (dualModule (dualModule A)) c
              (bidualIota A c
                ((Module.Basis.ofVectorSpace ℂ (Multiplicity (dualModule A) (-c))).coord i)) v)
      from fun i => drinfeld_tail_matching A hD c x _ _ v]
    rw [← Finset.smul_sum]
    congr 1
    rw [← hb]
    conv_rhs => rw [← chosen_contract_dual e]
    simp only [classified, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      map_sum, map_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  simp only [bidualIota] at hs
  simp only [dualIota, neg_neg] at ⊢
  rw [hs]
  simp only [smul_smul]
  congr 1
  unfold drinfeldScalar
  have hf := LatticeChargedQuotientScalar.associator_nonzero D hD c (-c) c
  field_simp [hf, unitCharacter_nonzero D hD c] <;> ring

/-- Full original module readback, with coefficient d(c)=u(-c)R(c,-c)/u(c).
The actual finite cup and all oscillator vectors were consumed above. -/
theorem drinfeldHom_eq_extend :
    drinfeldHom A hD = extend hD (fun c => drinfeldScalar hD c • bidualFamily A hD c) := by
  apply hom_ext_classified A (dualModule (dualModule A)) hD
  intro c v x
  rw [drinfeld_classified, classified_natural]
  simp only [restrict_extend, LinearMap.smul_apply, classified, TensorProduct.tmul_smul,
      map_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]

/-- The direction is forward theta, on the complete original carrier. -/
theorem drinfeldHom_theta : (drinfeldHom A hD).comp (theta A hD).hom = pivotalHom A hD := by
  apply hom_ext_classified A (dualModule (dualModule A)) hD
  intro c v x
  change (drinfeldHom A hD).linearMap
    ((theta A hD).hom.linearMap (classified hD A c x v)) = _
  rw [classified_natural, restrict_theta]
  simp only [classified, TensorProduct.tmul_smul, map_smul,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  change thetaScalar c • (drinfeldHom A hD).linearMap (classified hD A c x v) = _
  rw [drinfeld_classified, pivotal_classified, smul_smul]
  congr 1
  rw [pivotalScalar_ribbon]
  unfold drinfeldScalar
  ring

end Finite
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonPivotality
