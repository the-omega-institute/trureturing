/-
SOURCE ONLY. Neither elaboration nor kernel/official acceptance has been run.

Concrete open ribbon partial trace and Fourier charge projection for the
original arbitrary full weak lattice module. Only the multiplicities of the
closed color B are finite. The spectator, its oscillator carrier, and both
nested product carriers have no finiteness hypothesis.

The mathematics is the standard ribbon partial trace and finite character
projection. The contribution proposed here is its calculation in the original
weak-module realization, retaining its section, carries, inverse transports,
unitCharacter, and all original field/mode/Jacobi data. This is a gluing
ingredient, not surgery invariance or a completed TQFT/CFT/string/AdS theory.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualitySnakes
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleHopfTrace
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleOpenKirbyProjector

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom (homSpace recordEquiv restrict extend homMultiplicityEquiv)
open ActualWeakModuleScalarProbes (sectorModule)
open ActualWeakModuleUniversalField (P PairSector targetModule)
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleProductNaturality (productHom productHom_pair)
open ActualWeakModuleAssociator (F alpha alphaInverse associatorEquiv associatorIso
  alphaInverse_alpha alpha_alphaInverse)
open ActualWeakModulePentagon (normalizedPair normalizedPair_smul normalizedPair_input)
open ActualWeakModuleUnitCoherence (rightUnit_normalized alpha_normalized_fibers)
open ActualWeakModuleUnits (I eta0 rightUnit rightUnitIso rightUnit_inverse_elementary
  unit_classified)
open ActualWeakModuleDuality (dualModule dualIota evaluation coevaluation
  discriminantSupport mem_discriminantSupport cupVector cupVector_expansion
  cupTensor_basis coevaluation_eta0)
open ActualWeakModuleBalancing (theta)
open ActualWeakModuleBraiding (braid braidIso)
open ActualWeakModuleHopfTrace (sectorMultiplicity_finite sectorMultiplicity_finrank)

open private restrict_identity from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private ribbon_summand from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
open private double_braid_pair from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHopfTrace
open private restrict_extend from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open LatticeChargedQuotientScalar (carry_zero_right)
open private pairing_add pairing_neg pairing_symm character_orthogonality
  discriminant_card from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section OpenDiagram
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- The literal two FORWARD braids. No identity product map is inserted. -/
private def doubleForward : ModuleHom (targetModule A B) (targetModule A B) :=
  (braidIso B A).hom.comp (braidIso A B).hom

private theorem doubleForward_jAt (e : Discriminant D) (i : Fiber (D := D) e)
    (z : PairMultiplicity A B i.val) :
    restrict (doubleForward A B) e (jAt A B hD e i z) =
      phase (pairing D i.val.1 i.val.2) • jAt A B hD e i z := by
  apply Subtype.ext
  apply Subtype.ext
  change braid B A (braid A B (jAt A B hD e i z).val.val) = _
  rw [jAt_val, double_braid_pair]
  simp only [Submodule.coe_smul, jAt_val]

/-- The original right ribbon cap, with forward twist and forward braid. -/
def ribbonCap : ModuleHom (targetModule B (dualModule B)) (I D) :=
  (evaluation B hD).comp
    ((braidIso B (dualModule B)).hom.comp
      (productHom hD (theta B hD).hom (ModuleHom.id (dualModule B))))

private def openMonodromy :
    ModuleHom (targetModule A (targetModule B (dualModule B)))
      (targetModule A (targetModule B (dualModule B))) :=
  (associatorIso A B (dualModule B) hD).hom.comp
    ((productHom hD (doubleForward A B) (ModuleHom.id (dualModule B))).comp
      (associatorIso A B (dualModule B) hD).inv)

/-- The seven-arrow open loop, on the original full weak modules.
The only finite instance is the closed color's actual multiplicity family. -/
def openPartialTrace [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity B c)] :
    ModuleHom A A :=
  (rightUnitIso hD A).hom.comp
    ((productHom hD (ModuleHom.id A) (ribbonCap B hD)).comp
      ((openMonodromy A B hD).comp
        ((productHom hD (ModuleHom.id A) (coevaluation B hD)).comp
          (rightUnitIso hD A).inv)))

/-- Both actual nested associators are checked on a normalized right generator.
The inner jAt normalization is consumed by doubleForward_jAt; the outer
transport is the one in alpha_normalized, not an assumed coherence law. -/
private theorem openMonodromy_normalized (a c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B c)
    (z : Multiplicity (dualModule B) (-c)) (v : Carrier D) :
    (openMonodromy A B hD).linearMap
      (normalizedPair A (targetModule B (dualModule B)) hD a 0
        (x ⊗ₜ[ℂ] jAt B (dualModule B) hD 0
          ⟨(c,-c),add_neg_cancel c⟩ (y ⊗ₜ[ℂ] z)) v) =
      phase (pairing D a c) •
        normalizedPair A (targetModule B (dualModule B)) hD a 0
          (x ⊗ₜ[ℂ] jAt B (dualModule B) hD 0
            ⟨(c,-c),add_neg_cancel c⟩ (y ⊗ₜ[ℂ] z)) v := by
  let l := normalizedPair (targetModule A B) (dualModule B) hD (a+c) (-c)
    (j A B hD a c (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v
  let r := normalizedPair A (targetModule B (dualModule B)) hD a 0
    (x ⊗ₜ[ℂ] jAt B (dualModule B) hD 0
      ⟨(c,-c),add_neg_cancel c⟩ (y ⊗ₜ[ℂ] z)) v
  have hf : F hD a c (-c) ≠ 0 :=
    LatticeChargedQuotientScalar.associator_nonzero D hD a c (-c)
  have halpha : alpha A B (dualModule B) hD l = F hD a c (-c) • r := by
    exact alpha_normalized_fibers A B (dualModule B) hD a c (-c) (a+c) 0
      rfl (add_neg_cancel c) v x y z
  have hinverse : alphaInverse A B (dualModule B) hD r =
      (F hD a c (-c))⁻¹ • l := by
    exact ActualWeakModuleDuality.alphaInverse_normalized_fibers
      A B (dualModule B) hD a c (-c) (a+c) 0 rfl (add_neg_cancel c) v x y z
  have hmiddle :
      (productHom hD (doubleForward A B) (ModuleHom.id (dualModule B))).linearMap l =
        phase (pairing D a c) • l := by
    dsimp only [l]
    rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity]
    have hj := doubleForward_jAt A B hD (a+c)
      (⟨(a,c),rfl⟩ : Fiber (D := D) (a+c)) (x ⊗ₜ[ℂ] y)
    dsimp only [jAt] at hj
    rw [hj, ← TensorProduct.smul_tmul', normalizedPair_smul]
  have hcalc {L R : Type (max u v)} [AddCommGroup L] [Module ℂ L]
      [AddCommGroup R] [Module ℂ R]
      (f : L →ₗ[ℂ] R) (g : R →ₗ[ℂ] L) (m : L →ₗ[ℂ] L)
      (l : L) (r : R) (a q : ℂ) (ha : a ≠ 0)
      (h1 : g r = a⁻¹ • l) (h2 : m l = q • l) (h3 : f l = a • r) :
      f (m (g r)) = q • r := by
    rw [h1, map_smul, h2, map_smul, map_smul, h3]
    simp only [smul_smul]
    apply congrArg (fun z : ℂ => z • r)
    calc
      _ = (a⁻¹ * a) * q := by ring
      _ = q := by rw [inv_mul_cancel₀ ha, one_mul]
  exact hcalc (alpha A B (dualModule B) hD)
    (alphaInverse A B (dualModule B) hD)
    (productHom hD (doubleForward A B) (ModuleHom.id (dualModule B))).linearMap
    l r (F hD a c (-c)) (phase (pairing D a c)) hf hinverse hmiddle halpha

/-- The existing ribbon calculation is consumed at the ACTUAL unit ground,
which is T_zeroCarry([0]1), not the literal original vacuum. -/
private theorem ribbonCap_jAt (c : Discriminant D) (y : Multiplicity B c)
    (φ : Module.Dual ℂ (Multiplicity B c)) :
    restrict (ribbonCap B hD) 0
      (jAt B (dualModule B) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (y ⊗ₜ[ℂ] dualIota B c φ)) =
      ((F hD (-c) c (-c))⁻¹ * φ y) • eta0 hD := by
  have hf : F hD (-c) c (-c) ≠ 0 :=
    LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c (-c)
  have hunit : (eta0 hD).val.val =
      transport D 0 (LatticeChargedQuotientScalar.zeroCarry D hD)
        (Finsupp.single 0 (1 : Oscillator D)) := by
    rw [← unit_classified hD]
    exact (classification_normalization (I D) hD 0 (eta0 hD)).symm
  have hinv : transportInverse D 0 (LatticeChargedQuotientScalar.zeroCarry D hD)
      (eta0 hD).val.val = Finsupp.single 0 (1 : Oscillator D) := by
    rw [hunit]
    exact (transportLinearEquiv D 0
      (LatticeChargedQuotientScalar.zeroCarry D hD)).symm_apply_apply _
  have h := ribbon_summand B hD (ModuleHom.id B) c y φ (eta0 hD).val.val
  rw [restrict_identity, hinv] at h
  have hw : F hD (-c) c (-c) •
      restrict (ribbonCap B hD) 0
        (jAt B (dualModule B) hD 0 ⟨(c,-c),add_neg_cancel c⟩
          (y ⊗ₜ[ℂ] dualIota B c φ)) = φ y • eta0 hD := by
    apply Subtype.ext
    apply Subtype.ext
    change F hD (-c) c (-c) • (ribbonCap B hD).linearMap
      (jAt B (dualModule B) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (y ⊗ₜ[ℂ] dualIota B c φ)).val.val = φ y • (eta0 hD).val.val
    rw [jAt_val]
    simpa only [ribbonCap, ModuleHom.comp, ModuleIso.hom, LinearMap.comp_apply,
      ground, add_neg_cancel, ModuleHom.id, LinearMap.comp_id,
      LinearMap.id_apply, braidIso, ActualWeakModuleBraiding.braidEquiv] using h
  have hh := congrArg (fun q => (F hD (-c) c (-c))⁻¹ • q) hw
  simpa only [smul_smul, inv_mul_cancel₀ hf, one_smul] using hh

private theorem open_summand (a c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B c)
    (φ : Module.Dual ℂ (Multiplicity B c)) (v : Carrier D) :
    F hD (-c) c (-c) • rightUnit hD A
      ((productHom hD (ModuleHom.id A) (ribbonCap B hD)).linearMap
        ((openMonodromy A B hD).linearMap
          (normalizedPair A (targetModule B (dualModule B)) hD a 0
            (x ⊗ₜ[ℂ] jAt B (dualModule B) hD 0 ⟨(c,-c),add_neg_cancel c⟩
              (y ⊗ₜ[ℂ] dualIota B c φ)) v))) =
      (phase (pairing D a c) * φ y *
        LatticeChargedQuotientScalar.unitCharacter D hD a) • classified hD A a x v := by
  have hf : F hD (-c) c (-c) ≠ 0 :=
    LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c (-c)
  let L := (rightUnit hD A).toLinearMap.comp
    (productHom hD (ModuleHom.id A) (ribbonCap B hD)).linearMap
  let J : Multiplicity (I D) 0 →ₗ[ℂ] X :=
    (rightUnit hD A).toLinearMap.comp
      ((DirectSum.lof ℂ _ (PairSector A (I D)) (a,0)).comp
        ((TensorProduct.mk ℂ (Carrier D) (PairMultiplicity A (I D) (a,0))
          (transportInverse D (representative D (a+0)) (LatticeChargedQuotientScalar.carry D hD a 0) v)).comp
            (TensorProduct.mk ℂ (Multiplicity A a) (Multiplicity (I D) 0) x)))
  have hm := congrArg L.toAddHom.toFun
    (openMonodromy_normalized A B hD a c x y (dualIota B c φ) v)
  have hp := congrArg (rightUnit hD A).toAddHom.toFun
    (normalizedPair_input hD (ModuleHom.id A) (ribbonCap B hD) a 0
      (x ⊗ₜ[ℂ] jAt B (dualModule B) hD 0 ⟨(c,-c),add_neg_cancel c⟩
        (y ⊗ₜ[ℂ] dualIota B c φ)) v)
  simp only [TensorProduct.map_tmul, restrict_identity] at hp
  have hc := (hp.trans (congrArg J.toAddHom.toFun (ribbonCap_jAt B hD c y φ))).trans
    (J.map_smul ((F hD (-c) c (-c))⁻¹ * φ y) (eta0 hD))
  have hu := hc.trans (congrArg
    (fun z : X => ((F hD (-c) c (-c))⁻¹ * φ y) • z)
    (rightUnit_normalized (A := A) (hD := hD) a v x))
  have htotal := (hm.trans (L.map_smul (phase (pairing D a c)) _)).trans
    (congrArg (fun z : X => phase (pairing D a c) • z) hu)
  refine (congrArg (fun z : X => F hD (-c) c (-c) • z) htotal).trans ?_
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => z • classified hD A a x v)
  calc
    _ = (F hD (-c) c (-c) * (F hD (-c) c (-c))⁻¹) *
        (phase (pairing D a c) * φ y *
          LatticeChargedQuotientScalar.unitCharacter D hD a) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hf, one_mul]

variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity B c)]

/-- Actual open partial trace, including arbitrary original oscillator vectors.
The finite basis is contracted only in Multiplicity B c. No dimension or
trace of A, P(A,B), or their oscillator factors occurs. -/
theorem openPartialTrace_classified (a : Discriminant D) (x : Multiplicity A a)
    (v : Carrier D) :
    (openPartialTrace A B hD).linearMap (classified hD A a x v) =
      (∑ c ∈ discriminantSupport hD,
        phase (pairing D a c) * (Module.finrank ℂ (Multiplicity B c) : ℂ)) •
          classified hD A a x v := by
  classical
  let γ := LatticeChargedQuotientScalar.unitCharacter D hD a
  have hγ : γ ≠ 0 := LatticeChargedQuotientScalar.unitCharacter_nonzero D hD a
  let input : Multiplicity (targetModule B (dualModule B)) 0 →ₗ[ℂ]
      P A (targetModule B (dualModule B)) :=
    (DirectSum.lof ℂ _ (PairSector A (targetModule B (dualModule B))) (a,0)).comp
      ((TensorProduct.mk ℂ (Carrier D)
          (PairMultiplicity A (targetModule B (dualModule B)) (a,0))
        (transportInverse D (representative D (a+0))
          (LatticeChargedQuotientScalar.carry D hD a 0) v)).comp
        (TensorProduct.mk ℂ (Multiplicity A a)
          (Multiplicity (targetModule B (dualModule B)) 0) x))
  let q : Multiplicity (targetModule B (dualModule B)) 0 →ₗ[ℂ] X :=
    (rightUnit hD A).toLinearMap.comp
      ((productHom hD (ModuleHom.id A) (ribbonCap B hD)).linearMap.comp
        ((openMonodromy A B hD).linearMap.comp input))
  have hstart : (openPartialTrace A B hD).linearMap (classified hD A a x v) =
      γ⁻¹ • q (cupVector B hD) := by
    have hforward (z : P A (I D)) :
        (rightUnitIso hD A).hom.linearMap z = rightUnit hD A z := by
      rfl
    have hinverse (z : X) :
        (rightUnitIso hD A).inv.linearMap z = (rightUnit hD A).symm z := by
      rfl
    have hcompose
        {M₀ : Type _} {M₁ : Type _} {M₂ : Type _}
        {M₃ : Type _} {M₄ : Type _} {M₅ : Type _}
        [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
        [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
        [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
        {J₀ : FullJacobiLatticeModule D M₀} {J₁ : FullJacobiLatticeModule D M₁}
        {J₂ : FullJacobiLatticeModule D M₂} {J₃ : FullJacobiLatticeModule D M₃}
        {J₄ : FullJacobiLatticeModule D M₄} {J₅ : FullJacobiLatticeModule D M₅}
        (f₀ : ModuleHom J₀ J₁) (f₁ : ModuleHom J₁ J₂) (f₂ : ModuleHom J₂ J₃)
        (f₃ : ModuleHom J₃ J₄) (f₄ : ModuleHom J₄ J₅) (z : M₀) :
        (f₄.comp (f₃.comp (f₂.comp (f₁.comp f₀)))).linearMap z =
          f₄.linearMap (f₃.linearMap (f₂.linearMap (f₁.linearMap (f₀.linearMap z)))) := by
      rfl
    have hcomposition := hcompose (rightUnitIso hD A).inv
      (productHom hD (ModuleHom.id A) (coevaluation B hD)) (openMonodromy A B hD)
      (productHom hD (ModuleHom.id A) (ribbonCap B hD)) (rightUnitIso hD A).hom
      (classified hD A a x v)
    refine hcomposition.trans ?_
    refine (hforward
      ((productHom hD (ModuleHom.id A) (ribbonCap B hD)).linearMap
        ((openMonodromy A B hD).linearMap
          ((productHom hD (ModuleHom.id A) (coevaluation B hD)).linearMap
            ((rightUnitIso hD A).inv.linearMap (classified hD A a x v)))))).trans ?_
    have hbegin := congrArg
      (fun z : P A (I D) => rightUnit hD A
        ((productHom hD (ModuleHom.id A) (ribbonCap B hD)).linearMap
          ((openMonodromy A B hD).linearMap
            ((productHom hD (ModuleHom.id A) (coevaluation B hD)).linearMap z))))
      ((hinverse (classified hD A a x v)).trans
        (rightUnit_inverse_elementary (hD := hD) (A := A) a v x))
    refine hbegin.trans ?_
    have hp : DirectSum.lof ℂ _ (PairSector A (I D)) (a,0)
        (transportInverse D (representative D a)
          (LatticeChargedQuotientScalar.zeroCarry D hD) v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD)) =
        normalizedPair A (I D) hD a 0 (x ⊗ₜ[ℂ] eta0 hD) v := by
      simp only [normalizedPair, LinearMap.comp_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply, add_zero, carry_zero_right]
    rw [hp, map_smul, map_smul, map_smul, map_smul, normalizedPair_input,
      TensorProduct.map_tmul, restrict_identity, coevaluation_eta0]
    rfl
  have hdim (c : Discriminant D) :
      (∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity B c),
        (Module.Basis.ofVectorSpace ℂ (Multiplicity B c)).coord i
          (Module.Basis.ofVectorSpace ℂ (Multiplicity B c) i)) =
        (Module.finrank ℂ (Multiplicity B c) : ℂ) := by
    rw [← LinearMap.trace_id]
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Basis.ofVectorSpace ℂ (Multiplicity B c))]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearMap.id_apply, Module.Basis.coord_apply]
  rw [hstart, cupVector_expansion]
  simp only [map_sum, map_smul]
  calc
    _ = γ⁻¹ • ∑ c ∈ discriminantSupport hD,
        ∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity B c),
          (phase (pairing D a c) *
            (Module.Basis.ofVectorSpace ℂ (Multiplicity B c)).coord i
              (Module.Basis.ofVectorSpace ℂ (Multiplicity B c) i) * γ) •
                classified hD A a x v := by
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [cupTensor_basis]
      simp only [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact open_summand A B hD a c x _ _ v
    _ = γ⁻¹ • ∑ c ∈ discriminantSupport hD,
        (phase (pairing D a c) * (Module.finrank ℂ (Multiplicity B c) : ℂ) * γ) •
          classified hD A a x v := by
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_smul, ← Finset.sum_mul, ← Finset.mul_sum, hdim]
    _ = _ := by
      rw [Finset.smul_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro c hc
      rw [smul_smul]
      congr 1
      calc
        _ = (γ⁻¹ * γ) * (phase (pairing D a c) *
            (Module.finrank ℂ (Multiplicity B c) : ℂ)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hγ, one_mul]

end OpenDiagram

section CanonicalColor
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- L_b(A): the literal open loop colored by the ORIGINAL representative sector.
Finiteness is derived for that sector alone, in its original ground subtypes. -/
def loop (b : Discriminant D) : ModuleHom A A := by
  letI : ∀ c, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D b)) c) :=
    sectorMultiplicity_finite hD b
  exact openPartialTrace A (sectorModule D (representative D b)) hD

/-- Full original carrier formula, with v arbitrary, not only its vacuum. -/
theorem loop_classified (b a : Discriminant D) (x : Multiplicity A a)
    (v : Carrier D) :
    (loop A hD b).linearMap (classified hD A a x v) =
      phase (pairing D a b) • classified hD A a x v := by
  letI : ∀ c, Module.Finite ℂ
      (Multiplicity (sectorModule D (representative D b)) c) :=
    sectorMultiplicity_finite hD b
  unfold loop
  rw [openPartialTrace_classified]
  simp [sectorMultiplicity_finrank hD, mul_ite, mem_discriminantSupport]

/-- Equality of actual linear endomorphisms of the original joint-weight space. -/
theorem loop_restrict (b a : Discriminant D) :
    restrict (loop A hD b) a =
      phase (pairing D a b) • (LinearMap.id : Multiplicity A a →ₗ[ℂ] Multiplicity A a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change (loop A hD b).linearMap x.val.val = phase (pairing D a b) • x.val.val
  have h := loop_classified A hD b a x (Finsupp.single 0 (1 : Oscillator D))
  simpa only [classified, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, classification_normalization] using h

/-- The weighted finite sum is formed from the actual loop LINEAR MAPS.
The original all-state/all-integer-mode intertwining is proved directly;
no additive or scalar typeclass on ModuleHom is assumed. -/
def kirbyProjector (t : Discriminant D) : ModuleHom A A where
  linearMap := (Nat.card (Discriminant D) : ℂ)⁻¹ •
    ∑ b ∈ discriminantSupport hD, phase (-pairing D t b) • (loop A hD b).linearMap
  intertwines := by
    intro s m x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    rw [(loop A hD b).intertwines]

/-- The literal loop sum is exactly the full original charge-component map.
This is the Fourier calculation's consumer, not a new named character identity. -/
theorem kirbyProjector_eq_extend (t : Discriminant D) :
    kirbyProjector A hD t = extend hD
      (fun a => if a = t then (LinearMap.id : Multiplicity A a →ₗ[ℂ] Multiplicity A a)
        else 0) := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI := Fintype.ofFinite (Discriminant D)
  have hN : 0 < Nat.card (Discriminant D) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.pos_of_ne_zero Fintype.card_ne_zero
  have hn : (Nat.card (Discriminant D) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  apply (recordEquiv A A).injective
  apply (homMultiplicityEquiv A A hD).injective
  change restrict (kirbyProjector A hD t) = restrict (extend hD _)
  rw [restrict_extend]
  funext a
  have hs : (∑ b ∈ discriminantSupport hD,
      phase (-pairing D t b) * phase (pairing D a b)) =
      if a = t then (Nat.card (Discriminant D) : ℂ) else 0 := by
    have he (b : Discriminant D) :
        phase (-pairing D t b) * phase (pairing D a b) =
          pairingCharacter D hD b (a-t) := by
      change _ = phase (pairing D b (a-t))
      rw [pairing_symm D b (a-t), sub_eq_add_neg, pairing_add D hD,
        pairing_neg D hD, phase.map_add_eq_mul]
      ring
    simp_rw [he]
    simpa only [discriminantSupport, ← discriminant_card D hD, sub_eq_zero] using
      character_orthogonality D hD (a-t)
  apply LinearMap.ext
  intro x
  have hl (b : Discriminant D) :
      (loop A hD b).linearMap x.val.val = phase (pairing D a b) • x.val.val := by
    exact congrArg (fun z : Multiplicity A a => z.val.val)
      (LinearMap.congr_fun (loop_restrict A hD b a) x)
  apply Subtype.ext
  apply Subtype.ext
  change ((Nat.card (Discriminant D) : ℂ)⁻¹ •
      ∑ b ∈ discriminantSupport hD, phase (-pairing D t b) • (loop A hD b).linearMap)
        x.val.val = ((if a = t then
          (LinearMap.id : Multiplicity A a →ₗ[ℂ] Multiplicity A a) else 0) x).val.val
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, hl, smul_smul]
  rw [← Finset.sum_smul, hs]
  by_cases hat : a = t
  · simp only [if_pos hat, LinearMap.id_apply, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · simp only [if_neg hat, zero_smul, LinearMap.zero_apply, Submodule.coe_zero]

/-- Orthogonal composition of the ACTUAL ModuleHoms; s=t is idempotence.
No nonzero-fiber or faithful-action premise is introduced. -/
theorem kirbyProjector_comp (s t : Discriminant D) :
    (kirbyProjector A hD s).comp (kirbyProjector A hD t) =
      if s = t then kirbyProjector A hD t else ModuleHom.zero A A := by
  classical
  have hk (r a : Discriminant D) (x : Multiplicity A a) :
      restrict (kirbyProjector A hD r) a x = if a = r then x else 0 := by
    rw [kirbyProjector_eq_extend, restrict_extend]
    by_cases h : a = r <;> simp [h]
  have hz (a : Discriminant D) (x : Multiplicity A a) :
      restrict (ModuleHom.zero A A) a x = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  apply (recordEquiv A A).injective
  apply (homMultiplicityEquiv A A hD).injective
  change restrict ((kirbyProjector A hD s).comp (kirbyProjector A hD t)) = restrict _
  funext a
  apply LinearMap.ext
  intro x
  have hc : restrict ((kirbyProjector A hD s).comp (kirbyProjector A hD t)) a x =
      restrict (kirbyProjector A hD s) a (restrict (kirbyProjector A hD t) a x) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hc, hk, hk]
  by_cases hst : s = t
  · subst s
    simp only [if_pos rfl, hk]
    split_ifs <;> simp
  · rw [if_neg hst, hz]
    by_cases hat : a = t
    · subst a
      simp [Ne.symm hst]
    · simp [hat]

/-- The sum is in the actual Hom submodule, canonically equivalent to the
original ModuleHom record. Thus this resolves id_A on the entire carrier. -/
theorem kirbyProjector_resolution :
    (∑ t ∈ discriminantSupport hD, recordEquiv A A (kirbyProjector A hD t)) =
      recordEquiv A A (ModuleHom.id A) := by
  classical
  apply (homMultiplicityEquiv A A hD).injective
  rw [map_sum]
  have hk (t : Discriminant D) :
      homMultiplicityEquiv A A hD (recordEquiv A A (kirbyProjector A hD t)) =
        (fun a => if a = t then
          (LinearMap.id : Multiplicity A a →ₗ[ℂ] Multiplicity A a) else 0) := by
    change restrict (kirbyProjector A hD t) = _
    rw [kirbyProjector_eq_extend, restrict_extend]
  simp_rw [hk]
  funext a
  apply LinearMap.ext
  intro x
  change (∑ t ∈ discriminantSupport hD,
    (fun a => if a = t then
      (LinearMap.id : Multiplicity A a →ₗ[ℂ] Multiplicity A a) else 0)) a x =
        restrict (ModuleHom.id A) a x
  rw [restrict_identity]
  simp [Finset.sum_apply, LinearMap.sum_apply, mem_discriminantSupport]

/- In particular t=0 in kirbyProjector_eq_extend selects the whole original
zero-discriminant-charge summand, with every oscillator and multiplicity vector.
Rank zero has Nat.card=1; zero multiplicities use their empty actual basis sum.
These are instances of the displayed formulas, not extra normalized models. -/

end CanonicalColor
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleOpenKirbyProjector
