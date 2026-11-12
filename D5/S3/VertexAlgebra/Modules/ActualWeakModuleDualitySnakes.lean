/- Source only: native elaboration and kernel acceptance have not been run. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport
open LatticeChargedQuotientScalar (unitCharacter unitCharacter_nonzero)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleRealization
open ActualWeakModuleUniversalField (P PairSector targetModule elementary)
open ActualWeakModuleProductMultiplicity ActualWeakModuleProductNaturality
open ActualWeakModuleAssociator ActualWeakModulePentagon ActualWeakModuleUnits
open ActualWeakModuleUnitCoherence

open private model_induction from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
open private restrict_identity from D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section FiniteContractions
variable {V : Type w} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- This contraction is obtained from Mathlib's PRIME full tensor snake. -/
private theorem chosen_contract_vector (x : V) :
    (∑ i : Module.Basis.ofVectorSpaceIndex ℂ V,
      (Module.Basis.ofVectorSpace ℂ V).coord i x • Module.Basis.ofVectorSpace ℂ V i) = x := by
  have h := LinearMap.congr_fun (contractLeft_assoc_coevaluation' ℂ V) ((1 : ℂ) ⊗ₜ[ℂ] x)
  have hh := congrArg (TensorProduct.rid ℂ V) h
  simpa [coevaluation_apply_one, TensorProduct.sum_tmul, TensorProduct.tmul_sum] using hh

/-- This contraction is obtained from Mathlib's OTHER full tensor snake. -/
private theorem chosen_contract_dual (φ : Module.Dual ℂ V) :
    (∑ i : Module.Basis.ofVectorSpaceIndex ℂ V,
      φ (Module.Basis.ofVectorSpace ℂ V i) • (Module.Basis.ofVectorSpace ℂ V).coord i) = φ := by
  have h := LinearMap.congr_fun (contractLeft_assoc_coevaluation ℂ V) (φ ⊗ₜ[ℂ] (1 : ℂ))
  have hh := congrArg (TensorProduct.lid ℂ (Module.Dual ℂ V)) h
  simpa [coevaluation_apply_one, TensorProduct.sum_tmul, TensorProduct.tmul_sum] using hh

end FiniteContractions

section CarrierTools
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

/-- Linearity in the actual multiplicity tensor, for finite cup expansion. -/
private def pairAt (c d : Discriminant D) (v : Carrier D) :
    PairMultiplicity A B (c,d) →ₗ[ℂ] P A B where
  toFun w := normalizedPair A B hD c d w v
  map_add' x y := by
    simp only [normalizedPair, LinearMap.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, TensorProduct.tmul_add, map_add]
  map_smul' a x := normalizedPair_smul A B hD c d a x v

/-- The inverse associator readback is derived from the supplied forward
readback and actual inverse cancellation, with both original jAt casts. -/
theorem alphaInverse_normalized_fibers (a b c ab bc : Discriminant D)
    (hab : a+b=ab) (hbc : b+c=bc) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    alphaInverse A B C hD
      (normalizedPair A (targetModule B C) hD a bc
        (x ⊗ₜ[ℂ] jAt B C hD bc ⟨(b,c),hbc⟩ (y ⊗ₜ[ℂ] z)) v) =
      (F hD a b c)⁻¹ • normalizedPair (targetModule A B) C hD ab c
        (jAt A B hD ab ⟨(a,b),hab⟩ (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v := by
  apply (associatorEquiv A B C hD).injective
  change alpha A B C hD (alphaInverse A B C hD _) = alpha A B C hD (_ • _)
  rw [alpha_alphaInverse, map_smul, alpha_normalized_fibers, smul_smul,
    inv_mul_cancel₀ (LatticeChargedQuotientScalar.associator_nonzero D hD a b c), one_smul]

/-- Direct-sum and tensor generation of the complete classified carrier,
followed by the faithful record equivalence. -/
private theorem hom_ext_classified (f g : ModuleHom A B)
    (he : ∀ c v x, f.linearMap (classified hD A c x v) =
      g.linearMap (classified hD A c x v)) : f = g := by
  apply (recordEquiv A B).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨s,rfl⟩ := (classificationEquiv A hD).surjective x
  apply model_induction A (fun s => f.linearMap (classificationEquiv A hD s) =
    g.linearMap (classificationEquiv A hD s))
  · simp
  · intro s t hs ht
    simp only [map_add, hs, ht]
  · intro c v z
    exact he c v z

end CarrierTools

section Snakes
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- Evaluation kills the genuinely wrong inner total class. -/
private theorem left_tail_wrong (c d : Discriminant D) (hc : -d+c ≠ 0)
    (v : Carrier D) (x : Multiplicity A c) (m : Multiplicity A d)
    (φ : Module.Dual ℂ (Multiplicity A d)) :
    rightUnit hD A
      ((productHom hD (ModuleHom.id A) (evaluation A hD)).linearMap
        (alpha A (dualModule A) A hD
          (normalizedPair (targetModule A (dualModule A)) A hD 0 c
            (jAt A (dualModule A) hD 0 ⟨(d,-d),add_neg_cancel d⟩
              (m ⊗ₜ[ℂ] dualIota A d φ) ⊗ₜ[ℂ] x) v))) = 0 := by
  rw [alpha_normalized_fibers A (dualModule A) A hD d (-d) c 0 (-d+c)
    (add_neg_cancel d) rfl, map_smul, map_smul, normalizedPair_input,
    TensorProduct.map_tmul, restrict_identity,
    evaluation_wrong A hD (-d+c) hc]
  simp [normalizedPair]

private theorem left_tail_matching (c : Discriminant D) (v : Carrier D)
    (x m : Multiplicity A c) (φ : Module.Dual ℂ (Multiplicity A c)) :
    rightUnit hD A
      ((productHom hD (ModuleHom.id A) (evaluation A hD)).linearMap
        (alpha A (dualModule A) A hD
          (normalizedPair (targetModule A (dualModule A)) A hD 0 c
            (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
              (m ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] x) v))) =
      (unitCharacter D hD (-c) * F hD c (-c) c * unitCharacter D hD c) •
        (φ x • classified hD A c m v) := by
  rw [alpha_normalized_fibers A (dualModule A) A hD c (-c) c 0 0
    (add_neg_cancel c) (neg_add_cancel c), map_smul, map_smul,
    normalizedPair_input, TensorProduct.map_tmul, restrict_identity, evaluation_jAt,
    TensorProduct.tmul_smul, normalizedPair_smul, map_smul, rightUnit_normalized]
  simp only [smul_smul]
  congr 1
  ring

private theorem right_tail_wrong (c d : Discriminant D) (hc : -c+d ≠ 0)
    (v : Carrier D) (φ : Module.Dual ℂ (Multiplicity A c))
    (m : Multiplicity A d) (ψ : Module.Dual ℂ (Multiplicity A d)) :
    leftUnit hD (dualModule A)
      ((productHom hD (evaluation A hD) (ModuleHom.id (dualModule A))).linearMap
        (alphaInverse (dualModule A) A (dualModule A) hD
          (normalizedPair (dualModule A) (targetModule A (dualModule A)) hD (-c) 0
            (dualIota A c φ ⊗ₜ[ℂ] jAt A (dualModule A) hD 0
              ⟨(d,-d),add_neg_cancel d⟩ (m ⊗ₜ[ℂ] dualIota A d ψ)) v))) = 0 := by
  rw [alphaInverse_normalized_fibers (dualModule A) A (dualModule A) hD
    (-c) d (-d) (-c+d) 0 rfl (add_neg_cancel d), map_smul, map_smul,
    normalizedPair_input, TensorProduct.map_tmul,
    evaluation_wrong A hD (-c+d) hc, restrict_identity]
  simp [normalizedPair]

private theorem right_tail_matching (c : Discriminant D) (v : Carrier D)
    (φ ψ : Module.Dual ℂ (Multiplicity A c)) (m : Multiplicity A c) :
    leftUnit hD (dualModule A)
      ((productHom hD (evaluation A hD) (ModuleHom.id (dualModule A))).linearMap
        (alphaInverse (dualModule A) A (dualModule A) hD
          (normalizedPair (dualModule A) (targetModule A (dualModule A)) hD (-c) 0
            (dualIota A c φ ⊗ₜ[ℂ] jAt A (dualModule A) hD 0
              ⟨(c,-c),add_neg_cancel c⟩ (m ⊗ₜ[ℂ] dualIota A c ψ)) v))) =
      ((F hD (-c) c (-c))⁻¹ * unitCharacter D hD (-c)) •
        (φ m • classified hD (dualModule A) (-c) (dualIota A c ψ) v) := by
  rw [alphaInverse_normalized_fibers (dualModule A) A (dualModule A) hD
    (-c) c (-c) 0 0 (neg_add_cancel c) (add_neg_cancel c), map_smul, map_smul,
    normalizedPair_input, TensorProduct.map_tmul, evaluation_jAt, restrict_identity,
    TensorProduct.smul_tmul', normalizedPair_smul, map_smul, leftUnit_normalized]
  simp only [smul_smul]
  congr 1
  ring

variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- First snake on an arbitrary full carrier generator, before using extensionality. -/
private theorem snake_left_classified (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightUnit hD A
      ((productHom hD (ModuleHom.id A) (evaluation A hD)).linearMap
        (alpha A (dualModule A) A hD
          ((productHom hD (coevaluation A hD) (ModuleHom.id A)).linearMap
            ((leftUnit hD A).symm (classified hD A c x v))))) =
      classified hD A c x v := by
  let T : Multiplicity (targetModule A (dualModule A)) 0 →ₗ[ℂ] X :=
    (rightUnit hD A).toLinearMap.comp
      ((productHom hD (ModuleHom.id A) (evaluation A hD)).linearMap.comp
        ((alpha A (dualModule A) A hD).comp
          ((pairAt (targetModule A (dualModule A)) A hD 0 c v).comp
            ((TensorProduct.mk ℂ _ _).flip x))))
  have hi : (leftUnit hD A).symm (classified hD A c x v) =
      normalizedPair (I D) A hD 0 c (eta0 hD ⊗ₜ[ℂ] x) v := by
    apply (leftUnit hD A).injective
    rw [LinearEquiv.apply_symm_apply, leftUnit_normalized]
  rw [hi, normalizedPair_input, TensorProduct.map_tmul, coevaluation_eta0, restrict_identity]
  change T (cupVector A hD) = _
  rw [cupVector_expansion, map_sum]
  have hw (d : Discriminant D) (hd : d ≠ c) :
      T (F hD (-d) d (-d) •
        jAt A (dualModule A) hD 0 ⟨(d,-d),add_neg_cancel d⟩ (cupTensor A d)) = 0 := by
    rw [map_smul, cupTensor_basis, map_sum, map_sum]
    have he : -d+c ≠ 0 := by
      intro h
      apply hd
      have hh := congrArg (fun z => d+z) h
      simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh.symm
    have hs : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A d),
        T (jAt A (dualModule A) hD 0 ⟨(d,-d),add_neg_cancel d⟩
          (Module.Basis.ofVectorSpace ℂ (Multiplicity A d) i ⊗ₜ[ℂ]
            dualIota A d ((Module.Basis.ofVectorSpace ℂ (Multiplicity A d)).coord i)))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact left_tail_wrong A hD c d he v x _ _
    rw [hs, smul_zero]
  rw [Finset.sum_eq_single c (fun d hd hdc => hw d hdc) (by simp)]
  rw [map_smul, cupTensor_basis, map_sum, map_sum]
  have hs : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
      T (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i ⊗ₜ[ℂ]
          dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i)))) =
      (unitCharacter D hD (-c) * F hD c (-c) c * unitCharacter D hD c) •
        classified hD A c x v := by
    simp_rw [show ∀ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
      T (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i ⊗ₜ[ℂ]
          dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i))) =
      (unitCharacter D hD (-c) * F hD c (-c) c * unitCharacter D hD c) •
        (((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i x) •
          classified hD A c (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i) v)
      from fun i => left_tail_matching A hD c v x _ _]
    rw [← Finset.smul_sum]
    congr 1
    conv_rhs => rw [← chosen_contract_vector x]
    simp only [classified, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      map_sum, map_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  rw [hs, smul_smul]
  have hn : F hD (-c) c (-c) *
      (unitCharacter D hD (-c) * F hD c (-c) c * unitCharacter D hD c) = 1 := by
    calc
      _ = unitCharacter D hD (-c) * F hD (-c) c (-c) *
          F hD c (-c) c * unitCharacter D hD c := by ring
      _ = 1 := cap_cup_left_normalization hD c
  rw [hn, one_smul]

/-- The literal five-arrow first snake, as an equality of original ModuleHom records. -/
theorem snake_left :
    (rightUnitIso hD A).hom.comp
      ((productHom hD (ModuleHom.id A) (evaluation A hD)).comp
        ((associatorIso A (dualModule A) A hD).hom.comp
          ((productHom hD (coevaluation A hD) (ModuleHom.id A)).comp
            (leftUnitIso hD A).inv))) = ModuleHom.id A := by
  apply hom_ext_classified A A hD
  intro c v x
  exact snake_left_classified A hD c v x

/-- Second snake on arbitrary full dual-sector generators. -/
private theorem snake_right_classified (c : Discriminant D) (v : Carrier D)
    (φ : Module.Dual ℂ (Multiplicity A c)) :
    leftUnit hD (dualModule A)
      ((productHom hD (evaluation A hD) (ModuleHom.id (dualModule A))).linearMap
        (alphaInverse (dualModule A) A (dualModule A) hD
          ((productHom hD (ModuleHom.id (dualModule A)) (coevaluation A hD)).linearMap
            ((rightUnit hD (dualModule A)).symm
              (classified hD (dualModule A) (-c) (dualIota A c φ) v))))) =
      classified hD (dualModule A) (-c) (dualIota A c φ) v := by
  let T : Multiplicity (targetModule A (dualModule A)) 0 →ₗ[ℂ] DualCarrier A :=
    (leftUnit hD (dualModule A)).toLinearMap.comp
      ((productHom hD (evaluation A hD) (ModuleHom.id (dualModule A))).linearMap.comp
        ((alphaInverse (dualModule A) A (dualModule A) hD).comp
          ((pairAt (dualModule A) (targetModule A (dualModule A)) hD (-c) 0 v).comp
            ((TensorProduct.mk ℂ _ _) (dualIota A c φ)))))
  have hi : (rightUnit hD (dualModule A)).symm
      (classified hD (dualModule A) (-c) (dualIota A c φ) v) =
      (unitCharacter D hD (-c))⁻¹ •
        normalizedPair (dualModule A) (I D) hD (-c) 0
          (dualIota A c φ ⊗ₜ[ℂ] eta0 hD) v := by
    apply (rightUnit hD (dualModule A)).injective
    rw [LinearEquiv.apply_symm_apply, map_smul, rightUnit_normalized, smul_smul,
      inv_mul_cancel₀ (unitCharacter_nonzero D hD (-c)), one_smul]
  rw [hi]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity, coevaluation_eta0]
  change (unitCharacter D hD (-c))⁻¹ • T (cupVector A hD) = _
  rw [cupVector_expansion, map_sum]
  have hw (d : Discriminant D) (hd : d ≠ c) :
      T (F hD (-d) d (-d) •
        jAt A (dualModule A) hD 0 ⟨(d,-d),add_neg_cancel d⟩ (cupTensor A d)) = 0 := by
    rw [map_smul, cupTensor_basis, map_sum, map_sum]
    have he : -c+d ≠ 0 := by
      intro h
      apply hd
      have hh := congrArg (fun z => c+z) h
      simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh
    have hs : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A d),
        T (jAt A (dualModule A) hD 0 ⟨(d,-d),add_neg_cancel d⟩
          (Module.Basis.ofVectorSpace ℂ (Multiplicity A d) i ⊗ₜ[ℂ]
            dualIota A d ((Module.Basis.ofVectorSpace ℂ (Multiplicity A d)).coord i)))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact right_tail_wrong A hD c d he v φ _ _
    rw [hs, smul_zero]
  rw [Finset.sum_eq_single c (fun d hd hdc => hw d hdc) (by simp)]
  rw [map_smul, cupTensor_basis, map_sum, map_sum]
  have hs : (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
      T (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i ⊗ₜ[ℂ]
          dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i)))) =
      ((F hD (-c) c (-c))⁻¹ * unitCharacter D hD (-c)) •
        classified hD (dualModule A) (-c) (dualIota A c φ) v := by
    simp_rw [show ∀ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
      T (jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i ⊗ₜ[ℂ]
          dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i))) =
      ((F hD (-c) c (-c))⁻¹ * unitCharacter D hD (-c)) •
        (φ (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i) •
          classified hD (dualModule A) (-c)
            (dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i)) v)
      from fun i => right_tail_matching A hD c v φ _ _]
    rw [← Finset.smul_sum]
    congr 1
    conv_rhs => rw [← chosen_contract_dual φ]
    simp only [classified, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      map_sum, map_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  rw [hs]
  simp only [smul_smul, mul_assoc]
  have hn : (unitCharacter D hD (-c))⁻¹ *
      (F hD (-c) c (-c) * ((F hD (-c) c (-c))⁻¹ * unitCharacter D hD (-c))) = 1 := by
    simpa only [mul_assoc] using cap_cup_right_normalization hD c
  rw [hn, one_smul]

/-- The literal five-arrow second snake, as an equality of original ModuleHom records. -/
theorem snake_right :
    (leftUnitIso hD (dualModule A)).hom.comp
      ((productHom hD (evaluation A hD) (ModuleHom.id (dualModule A))).comp
        ((associatorIso (dualModule A) A (dualModule A) hD).inv.comp
          ((productHom hD (ModuleHom.id (dualModule A)) (coevaluation A hD)).comp
            (rightUnitIso hD (dualModule A)).inv))) = ModuleHom.id (dualModule A) := by
  apply hom_ext_classified (dualModule A) (dualModule A) hD
  intro c v z
  have hz : iota (DualMultiplicity A) c (kappa (DualMultiplicity A) c z) = z :=
    (multiplicityEquiv (DualMultiplicity A) hD c).symm_apply_apply z
  have h := snake_right_classified A hD (-c) v (kappa (DualMultiplicity A) c z)
  simpa only [dualIota, neg_neg, hz] using h

end Snakes

section EvaluationNaturality
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

private theorem pair_hom_ext
    (J : FullJacobiLatticeModule D X) (K : FullJacobiLatticeModule D Y)
    (L : FullJacobiLatticeModule D Z) (f g : ModuleHom (targetModule J K) L)
    (he : ∀ c d v x y,
      f.linearMap (DirectSum.lof ℂ _ (PairSector J K) (c,d)
        (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y))) =
      g.linearMap (DirectSum.lof ℂ _ (PairSector J K) (c,d)
        (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y)))) : f = g := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply DirectSum.linearMap_ext
  rintro ⟨c,d⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact he c d v x y

/-- The naturality of the actual cap for the constructed algebraic transpose.
The maps are those of the duality whose two full snakes were proved above. -/
theorem evaluation_natural (f : ModuleHom A B) :
    (evaluation A hD).comp (productHom hD (dualHom hD f) (ModuleHom.id A)) =
      (evaluation B hD).comp (productHom hD (ModuleHom.id (dualModule B)) f) := by
  apply pair_hom_ext (dualModule B) A (I D)
  intro r s v z x
  change (evaluation A hD).linearMap
    ((productHom hD (dualHom hD f) (ModuleHom.id A)).linearMap _) =
    (evaluation B hD).linearMap
      ((productHom hD (ModuleHom.id (dualModule B)) f).linearMap _)
  rw [productHom_pair, productHom_pair, TensorProduct.map_tmul, TensorProduct.map_tmul,
    restrict_identity, restrict_identity]
  by_cases he : r+s=0
  · have hs : s = -r := by
      calc
        s = -r+(r+s) := by abel
        _ = -r := by rw [he, add_zero]
    subst s
    obtain ⟨φ,hφ⟩ := (multiplicityEquiv (DualMultiplicity B) hD r).symm.surjective z
    change iota (DualMultiplicity B) r φ = z at hφ
    subst z
    have hm (c : Discriminant D) (ψ : Module.Dual ℂ (Multiplicity B c))
        (y : Multiplicity A c) :
        (evaluation A hD).linearMap
          (DirectSum.lof ℂ _ (PairSector (dualModule A) A) (-c,c)
            (v ⊗ₜ[ℂ] (restrict (dualHom hD f) (-c) (dualIota B c ψ) ⊗ₜ[ℂ] y))) =
        (evaluation B hD).linearMap
          (DirectSum.lof ℂ _ (PairSector (dualModule B) B) (-c,c)
            (v ⊗ₜ[ℂ] (dualIota B c ψ ⊗ₜ[ℂ] restrict f c y))) := by
      rw [dualHom_dualIota, evaluation_pair, evaluation_pair]
      rfl
    simpa only [dualIota, neg_neg] using hm (-r) φ x
  · rw [evaluation_pair_wrong A hD r s he, evaluation_pair_wrong B hD r s he]

end EvaluationNaturality
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality
