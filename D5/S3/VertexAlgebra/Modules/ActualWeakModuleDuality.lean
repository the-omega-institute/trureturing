/- Source only: native elaboration and kernel acceptance have not been run. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleRealization
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
import Mathlib.LinearAlgebra.Coevaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (unitCharacter unitCharacter_nonzero zeroCarry carry)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleScalarProbes ActualWeakModuleRealization
open ActualWeakModuleUniversalField (P PairSector targetModule elementary)
open ActualWeakModuleProductMultiplicity ActualWeakModuleProductNaturality
open ActualWeakModuleAssociator ActualWeakModulePentagon ActualWeakModuleUnits
open ActualWeakModuleUnitCoherence

open private restrict_extend from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private unitCharacter_square from D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Scalars
variable (hD : (gramReal D).PosDef)

/-- The exact pentagon specialization; the original nonnormalized units remain. -/
theorem dual_pentagon (c : Discriminant D) :
    F hD c (-c) c * unitCharacter D hD c * F hD (-c) c (-c) =
      unitCharacter D hD (-c) := by
  have hp := LatticeChargedQuotientScalar.scalar_pentagon D hD c (-c) c (-c)
  simpa only [neg_add_cancel, add_neg_cancel,
    LatticeChargedQuotientScalar.associator_zero_middle,
    LatticeChargedQuotientScalar.associator_zero_left,
    LatticeChargedQuotientScalar.associator_zero_right,
    LatticeChargedQuotientScalar.unitCharacter_zero, div_one, one_mul] using hp

theorem cap_cup_left_normalization (c : Discriminant D) :
    unitCharacter D hD (-c) * F hD (-c) c (-c) *
      F hD c (-c) c * unitCharacter D hD c = 1 := by
  calc
    _ = unitCharacter D hD (-c) *
        (F hD c (-c) c * unitCharacter D hD c * F hD (-c) c (-c)) := by ring
    _ = unitCharacter D hD (-c) * unitCharacter D hD (-c) := by rw [dual_pentagon]
    _ = 1 := unitCharacter_square D hD (-c)

theorem cap_cup_right_normalization (c : Discriminant D) :
    (unitCharacter D hD (-c))⁻¹ * F hD (-c) c (-c) *
      (F hD (-c) c (-c))⁻¹ * unitCharacter D hD (-c) = 1 := by
  have hF := LatticeChargedQuotientScalar.associator_nonzero D hD (-c) c (-c)
  have hu := unitCharacter_nonzero D hD (-c)
  calc
    _ = ((unitCharacter D hD (-c))⁻¹ * unitCharacter D hD (-c)) *
        (F hD (-c) c (-c) * (F hD (-c) c (-c))⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hu, mul_inv_cancel₀ hF, mul_one]

theorem cap_cup_compatibility (c : Discriminant D) :
    unitCharacter D hD (-c) * F hD (-c) c (-c) =
      (F hD c (-c) c * unitCharacter D hD c)⁻¹ := by
  have hn := mul_ne_zero
    (LatticeChargedQuotientScalar.associator_nonzero D hD c (-c) c)
    (unitCharacter_nonzero D hD c)
  apply mul_left_cancel₀ hn
  calc
    _ = unitCharacter D hD (-c) * F hD (-c) c (-c) *
        F hD c (-c) c * unitCharacter D hD c := by ring
    _ = 1 := cap_cup_left_normalization hD c
    _ = _ := (mul_inv_cancel₀ hn).symm

end Scalars

section Dual
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)

abbrev DualMultiplicity (c : Discriminant D) := Module.Dual ℂ (Multiplicity A (-c))
abbrev DualCarrier := RealizationCarrier (DualMultiplicity A)

/-- This full weak module exists for arbitrary multiplicities. -/
def dualModule : FullJacobiLatticeModule D (DualCarrier A) :=
  realization (DualMultiplicity A)

theorem dualModule_mode (c : Discriminant D) (v : Carrier D)
    (φ : DualMultiplicity A c) (a : Carrier D) (m : ℤ) :
    mode (dualModule A) a m
      (DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] DualMultiplicity A d) c (v ⊗ₜ[ℂ] φ)) =
    DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] DualMultiplicity A d) c
      (mode (sectorModule D (representative D c)) a m v ⊗ₜ[ℂ] φ) := by
  rw [dualModule, realization, FullJacobiDirectSum.directSumModule_mode,
    DirectSum.lmap_lof, FullJacobiTensorModule.tensorModule_mode,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- The neg_neg transport needed at the (c,-c) cup and (-c,c) cap. -/
def dualIota (c : Discriminant D) :
    Module.Dual ℂ (Multiplicity A c) →ₗ[ℂ] Multiplicity (dualModule A) (-c) := by
  simpa only [neg_neg] using iota (DualMultiplicity A) (-c)

variable (hD : (gramReal D).PosDef)

/-- A cap block uses the actual kappa and algebraic evaluation. -/
private def capBlock (i : Fiber (D := D) 0) :
    PairMultiplicity (dualModule A) A i.val →ₗ[ℂ] Multiplicity (I D) 0 := by
  rcases i with ⟨⟨r,s⟩,hi⟩
  have hs : s = -r := by
    calc
      s = -r + (r+s) := by abel
      _ = -r := by rw [hi, add_zero]
  subst s
  exact unitCharacter D hD r •
    ((LinearMap.toSpanSingleton ℂ (Multiplicity (I D) 0) (eta0 hD)).comp
      ((TensorProduct.contractLeft ℂ (Multiplicity A (-r))).comp
        (TensorProduct.map (kappa (DualMultiplicity A) r) LinearMap.id)))

def evaluationFamily : Families (targetModule (dualModule A) A) (I D) := fun e => by
  by_cases he : e = 0
  · subst e
    exact (DirectSum.toModule ℂ _ _ (capBlock A hD)).comp (mu (dualModule A) A hD 0)
  · exact 0

/-- Hom.extend has the original E_target * familyMap * E_source.symm orientation. -/
def evaluation : ModuleHom (targetModule (dualModule A) A) (I D) :=
  extend hD (evaluationFamily A hD)

theorem evaluation_jAt (c : Discriminant D) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A c) :
    restrict (evaluation A hD) 0
      (jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
        (dualIota A c φ ⊗ₜ[ℂ] x)) =
      (unitCharacter D hD (-c) * φ x) • eta0 hD := by
  rw [evaluation, restrict_extend]
  simp [evaluationFamily, mu_jAt, DirectSum.toModule_lof, capBlock,
    dualIota, DualMultiplicity, kappa_iota, LinearMap.toSpanSingleton_apply, smul_smul]

theorem evaluation_wrong (e : Discriminant D) (he : e ≠ 0)
    (z : Multiplicity (targetModule (dualModule A) A) e) :
    restrict (evaluation A hD) e z = 0 := by
  rw [evaluation, restrict_extend]
  simp [evaluationFamily, he]

/-- Full raw-pair readback; the transport from beta_-c+beta_c is not suppressed. -/
theorem evaluation_pair (c : Discriminant D) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A c) (v : Carrier D) :
    (evaluation A hD).linearMap
      (DirectSum.lof ℂ _ (PairSector (dualModule A) A) (-c,c)
        (v ⊗ₜ[ℂ] (dualIota A c φ ⊗ₜ[ℂ] x))) =
      (unitCharacter D hD (-c) * φ x) •
        transport D 0 (zeroCarry D hD)
          (transport D (representative D 0) (carry D hD (-c) c) v) := by
  have hj := classification_j (dualModule A) A hD (-c) c
    (dualIota A c φ ⊗ₜ[ℂ] x)
    (transport D (representative D 0) (carry D hD (-c) c) v)
  simp only [neg_add_cancel] at hj
  rw [(transportLinearEquiv D _ _).symm_apply_apply] at hj
  rw [← hj]
  change (evaluation A hD).linearMap
    (classified hD (targetModule (dualModule A) A) 0
      (jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
        (dualIota A c φ ⊗ₜ[ℂ] x)) _) = _
  rw [classified_natural, evaluation_jAt]
  simp only [classified, TensorProduct.tmul_smul, map_smul,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  change _ = (unitCharacter D hD (-c) * φ x) • _
  rw [← unit_classified]
  rfl

theorem evaluation_single (c : Discriminant D) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A c) (l : Charge D) (p : Oscillator D) :
    (evaluation A hD).linearMap
      (DirectSum.lof ℂ _ (PairSector (dualModule A) A) (-c,c)
        (Finsupp.single l p ⊗ₜ[ℂ] (dualIota A c φ ⊗ₜ[ℂ] x))) =
      (unitCharacter D hD (-c) * φ x * epsilon D l (carry D hD (-c) c) *
        epsilon D (l+carry D hD (-c) c) (zeroCarry D hD)) •
        Finsupp.single (l+carry D hD (-c) c+zeroCarry D hD) p := by
  rw [evaluation_pair]
  simp only [transport_single, map_smul, smul_smul]
  congr 1
  ring

theorem evaluation_pair_wrong (c d : Discriminant D) (hc : c+d ≠ 0)
    (v : Carrier D) (w : PairMultiplicity (dualModule A) A (c,d)) :
    (evaluation A hD).linearMap
      (DirectSum.lof ℂ _ (PairSector (dualModule A) A) (c,d) (v ⊗ₜ[ℂ] w)) = 0 := by
  have hj := classification_j (dualModule A) A hD c d w
    (transport D (representative D (c+d)) (carry D hD c d) v)
  rw [(transportLinearEquiv D _ _).symm_apply_apply] at hj
  rw [← hj]
  change (evaluation A hD).linearMap
    (classified hD (targetModule (dualModule A) A) (c+d) (j (dualModule A) A hD c d w) _) = 0
  rw [classified_natural, evaluation_wrong A hD (c+d) hc]
  simp [classified]

/-- A finite sum over the complete original discriminant, derived from hD. -/
def discriminantSupport : Finset (Discriminant D) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI := Fintype.ofFinite (Discriminant D)
  exact Finset.univ

@[simp] theorem mem_discriminantSupport (c : Discriminant D) :
    c ∈ discriminantSupport hD := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI := Fintype.ofFinite (Discriminant D)
  simp [discriminantSupport]

variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- The chosen Mathlib coevaluation, transported by the proved actual iota.
No additional assertion of basis independence is made. -/
def cupTensor (c : Discriminant D) : PairMultiplicity A (dualModule A) (c,-c) :=
  TensorProduct.map LinearMap.id (dualIota A c)
    (coevaluation ℂ (Multiplicity A c) 1)

theorem cupTensor_basis (c : Discriminant D) :
    cupTensor A c = ∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
      Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i ⊗ₜ[ℂ]
        dualIota A c ((Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i) := by
  simp only [cupTensor, coevaluation_apply_one, map_sum,
    TensorProduct.map_tmul, LinearMap.id_apply]

def cupVector : Multiplicity (targetModule A (dualModule A)) 0 :=
  nu A (dualModule A) hD 0
    (∑ c ∈ discriminantSupport hD, F hD (-c) c (-c) •
      DirectSum.lof ℂ _ _ (⟨(c,-c),add_neg_cancel c⟩ : Fiber (D := D) 0)
        (cupTensor A c))

theorem cupVector_expansion :
    cupVector A hD = ∑ c ∈ discriminantSupport hD, F hD (-c) c (-c) •
      jAt A (dualModule A) hD 0 ⟨(c,-c),add_neg_cancel c⟩ (cupTensor A c) := by
  simp only [cupVector, map_sum, map_smul, nu_lof]

def coevaluationFamily : Families (I D) (targetModule A (dualModule A)) := fun e => by
  by_cases he : e = 0
  · subst e
    exact (etaCoefficient hD).smulRight (cupVector A hD)
  · exact 0

def coevaluation : ModuleHom (I D) (targetModule A (dualModule A)) :=
  extend hD (coevaluationFamily A hD)

theorem coevaluation_eta0 :
    restrict (coevaluation A hD) 0 (eta0 hD) = cupVector A hD := by
  rw [coevaluation, restrict_extend]
  simp [coevaluationFamily, etaCoefficient_eta0]

/-- Every original unit vector, with BOTH inverse transports still literal. -/
theorem coevaluation_carrier (v : Carrier D) :
    (coevaluation A hD).linearMap v =
      ∑ c ∈ discriminantSupport hD, F hD (-c) c (-c) •
        DirectSum.lof ℂ _ (PairSector A (dualModule A)) (c,-c)
          (transportInverse D (representative D 0) (carry D hD c (-c))
            (transportInverse D 0 (zeroCarry D hD) v) ⊗ₜ[ℂ] cupTensor A c) := by
  have hv : v = classified hD (I D) 0 (eta0 hD)
      (transportInverse D 0 (zeroCarry D hD) v) := by
    rw [unit_classified, (transportLinearEquiv D _ _).apply_symm_apply]
  conv_lhs => rw [hv]
  rw [classified_natural, coevaluation_eta0, cupVector_expansion]
  simp only [classified, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
    map_sum, map_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  simpa only [add_neg_cancel] using
    classification_j A (dualModule A) hD c (-c) (cupTensor A c)
      (transportInverse D 0 (zeroCarry D hD) v)

/-- Original single-charge coefficients, including both reciprocal epsilon factors. -/
theorem coevaluation_single (l : Charge D) (p : Oscillator D) :
    (coevaluation A hD).linearMap (Finsupp.single l p) =
      ∑ c ∈ discriminantSupport hD,
        (F hD (-c) c (-c) *
          ((epsilon D (-zeroCarry D hD) (zeroCarry D hD))⁻¹ *
            epsilon D l (-zeroCarry D hD)) *
          ((epsilon D (-carry D hD c (-c)) (carry D hD c (-c)))⁻¹ *
            epsilon D (l-zeroCarry D hD) (-carry D hD c (-c)))) •
        DirectSum.lof ℂ _ (PairSector A (dualModule A)) (c,-c)
          (Finsupp.single (l-zeroCarry D hD-carry D hD c (-c)) p ⊗ₜ[ℂ] cupTensor A c) := by
  rw [coevaluation_carrier]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [transportInverse_single, map_smul, ← TensorProduct.smul_tmul', smul_smul]
  congr 1
  ring

end Dual

section Transpose
variable {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℂ X]
variable [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

/-- Ordinary complex-linear algebraic precomposition, with independent universes. -/
def dualHom (f : ModuleHom A B) : ModuleHom (dualModule B) (dualModule A) :=
  extend hD (fun c => (iota (DualMultiplicity A) c).comp
    (((restrict f (-c)).dualMap).comp (kappa (DualMultiplicity B) c)))

theorem dualHom_restrict (f : ModuleHom A B) (c : Discriminant D)
    (φ : DualMultiplicity B c) :
    kappa (DualMultiplicity A) c
      (restrict (dualHom hD f) c (iota (DualMultiplicity B) c φ)) =
      φ.comp (restrict f (-c)) := by
  rw [dualHom, restrict_extend]
  simp only [LinearMap.comp_apply, kappa_iota]
  rfl

theorem dualHom_dualIota (f : ModuleHom A B) (c : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity B c)) :
    restrict (dualHom hD f) (-c) (dualIota B c φ) =
      dualIota A c (φ.comp (restrict f c)) := by
  rw [dualHom, restrict_extend]
  simpa only [dualIota, neg_neg, LinearMap.comp_apply, kappa_iota]

/-- All-carrier transpose readback, not just a statement about sector labels. -/
theorem dualHom_carrier (f : ModuleHom A B) (c : Discriminant D)
    (v : Carrier D) (φ : DualMultiplicity B c) :
    (dualHom hD f).linearMap
      (DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] DualMultiplicity B d) c (v ⊗ₜ[ℂ] φ)) =
      DirectSum.lof ℂ _ (fun d => Carrier D ⊗[ℂ] DualMultiplicity A d) c
        (v ⊗ₜ[ℂ] φ.comp (restrict f (-c))) := by
  rw [← classification_iota (DualMultiplicity B) hD c φ v, classified_natural]
  rw [dualHom, restrict_extend]
  simp only [LinearMap.comp_apply, kappa_iota]
  exact classification_iota (DualMultiplicity A) hD c _ v

end Transpose
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality
