/- Source-only candidate. No elaboration/kernel acceptance is asserted.
Finite algebraic spectral rotation of the ORIGINAL omega zero mode on ORIGINAL
arbitrary full weak modules. No analytic operator exponential is defined.
The original even-lattice energy, concrete sector diagonalization, generic
arbitrary-multiplicity tensor coefficients and full classification are reused.
The full VOA/CFT/anomaly/fusion/string/AdS goal remains active and incomplete. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBalancing
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetPositiveEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleConformalMonodromy

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticePositiveEnergy
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetConformal
open LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeActualConformalState (omega)
open FullJacobiCurrentTransport FullJacobiIntertwiner FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleBalancing
open private rat_unit qmod_integer from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private inverseGram_left inverseGram_right from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

/-- Actual inverse-rational-Gram duality, also for the empty matrix. -/
theorem dualVector_duality (hD : (gramReal D).PosDef) (β : Charge D) (i : Fin D.rank) :
    ∑ j, (D.G i j : ℚ) * dualVector D β j = (β i : ℚ) := by
  have h : gramRat D *ᵥ dualVector D β = (fun i => (β i : ℚ)) := by
    rw [dualVector, inverseRat, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (rat_unit D hD), Matrix.one_mulVec]
  exact congrFun h i

/-- The concrete zero-charge energy is the original discriminant half norm. -/
theorem chargeWeight_dual_zero (hD : (gramReal D).PosDef) (β : Charge D) :
    LatticeDualCosetEnergy.chargeWeight D (dualVector D β) 0 = pairRaw D β β / 2 := by
  have hp : LatticeDualCosetEnergy.pairing D (dualVector D β) (dualVector D β) =
      pairRaw D β β := by
    calc
      _ = ∑ i, dualVector D β i * (∑ j, (D.G i j : ℚ) * dualVector D β j) := by
        simp only [LatticeDualCosetEnergy.pairing, Finset.mul_sum, mul_assoc]
      _ = ∑ i, dualVector D β i * (β i : ℚ) := by
        simp only [dualVector_duality hD β]
      _ = _ := rfl
  simpa only [LatticeDualCosetEnergy.chargeWeight, Pi.zero_apply, Int.cast_zero,
    zero_add, hp] using congrArg (fun t : ℚ => t / 2) hp

/-- The rational grade of an ORIGINAL charge/oscillator label. -/
def degree (c : Discriminant D) (a : Label D) : ℚ :=
  LatticeDualCosetEnergy.weight D (dualVector D (representative D c)) a

/-- Integer oscillator energy, original lattice evenness and G mu = beta give
the exact residue. No new quadratic refinement or spectrum premise is imposed. -/
theorem degree_class (hD : (gramReal D).PosDef) (c : Discriminant D) (a : Label D) :
    (degree c a : QmodZ) = quadraticClass D c := by
  let z : ℤ := (oscillatorEnergy a.2 : ℤ) + chargeEnergy D a.1 +
    ∑ i, a.1 i * representative D c i
  have hw : degree c a = pairRaw D (representative D c) (representative D c) / 2 + (z : ℚ) := by
    rw [degree, LatticeDualCosetEnergy.weight,
      LatticeDualCosetEnergy.chargeWeight_expansion D (representative D c)
        (dualVector D (representative D c)) (dualVector_duality hD _) a.1,
      chargeWeight_dual_zero hD]
    simp only [z, Int.cast_add, Int.cast_natCast]
    ring
  rw [hw, AddCircle.coe_add, qmod_integer, add_zero]

/-- An actual diagonal map on FINITELY SUPPORTED, vector-valued coefficients.
The multiplicity module is arbitrary; no basis of it is selected. -/
private def coefficientScale {I : Type v} {W : Type w} [AddCommGroup W] [Module ℂ W]
    (s : I → ℂ) : (I →₀ W) →ₗ[ℂ] (I →₀ W) :=
  Finsupp.lsum ℂ (fun a => s a • (Finsupp.lsingle a : W →ₗ[ℂ] (I →₀ W)))

private theorem coefficientScale_apply {I : Type v} {W : Type w}
    [AddCommGroup W] [Module ℂ W] (s : I → ℂ) (f : I →₀ W) (a : I) :
    coefficientScale s f a = s a • f a := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, smul_add]
  | single b z =>
    simp only [coefficientScale, Finsupp.lsum_single, LinearMap.smul_apply,
      Finsupp.lsingle_apply, Finsupp.smul_apply]
    by_cases h : b = a
    · subst b; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]

section Original
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (J : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- Literal original conformal L0, namely the original omega's integer mode 1. -/
def L0 : Module.End ℂ X := mode J (omega D (inverseGram hD)) 1

/-- Actual algebraic tensor coefficients in the existing CARRIER basis. -/
def tensorCoeff (c : Discriminant D) : Sector J c ≃ₗ[ℂ] (Label D →₀ Multiplicity J c) :=
  D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeffEquiv (carrierBasis D)

/-- Rational eigengenerators, transported in the correct E : Model J -> X direction. -/
theorem L0_classified_basis (c : Discriminant D) (a : Label D) (w : Multiplicity J c) :
    L0 J hD
      (classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (carrierBasis D a ⊗ₜ[ℂ] w))) =
      (degree c a : ℂ) •
        classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (carrierBasis D a ⊗ₜ[ℂ] w)) := by
  change mode J (omega D (inverseGram hD)) 1 (classificationEquiv J hD _) = _
  rw [← classification]
  simp only [canonicalModule, directSumModule_mode, DirectSum.lmap_lof, tensorModule_mode]
  change classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c
    (TensorProduct.map (moduleL D (representative D c) (inverseGram hD) 0) LinearMap.id
      (carrierBasis D a ⊗ₜ[ℂ] w))) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply,
    LatticeDualCosetEnergy.moduleL_basis_zero D (representative D c)
      (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
      (dualVector D (representative D c)) (dualVector_duality hD _),
    ← TensorProduct.smul_tmul', map_smul, map_smul]

/-- Coefficients of actual L0 on arbitrary original vectors and multiplicities. -/
theorem L0_coeff (x : X) (c : Discriminant D) (a : Label D) :
    tensorCoeff J c (((classificationEquiv J hD).symm (L0 J hD x)) c) a =
      (degree c a : ℂ) • tensorCoeff J c (((classificationEquiv J hD).symm x) c) a := by
  have hmodel := classification_inverse J hD (omega D (inverseGram hD)) 1 x
  simp only [canonicalModule, directSumModule_mode, tensorModule_mode] at hmodel
  change (classificationEquiv J hD).symm (L0 J hD x) =
    DirectSum.lmap (fun c : Discriminant D =>
      TensorProduct.map (moduleL D (representative D c) (inverseGram hD) 0)
        (LinearMap.id : Module.End ℂ (Multiplicity J c)))
      ((classificationEquiv J hD).symm x) at hmodel
  rw [hmodel, DirectSum.lmap_apply]
  exact D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeff_action
    (carrierBasis D) (moduleL D (representative D c) (inverseGram hD) 0)
    (fun a => (degree c a : ℂ))
    (LatticeDualCosetEnergy.moduleL_basis_zero D (representative D c)
      (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
      (dualVector D (representative D c)) (dualVector_duality hD _)) _ a

/-- Both directions, for every rational eigenvalue and every original vector.
This includes zero vectors and arbitrary infinite-dimensional multiplicities. -/
theorem L0_eigen_iff (e : ℚ) (x : X) :
    L0 J hD x = (e : ℂ) • x ↔
      ∀ c : Discriminant D,
        tensorCoeff J c (((classificationEquiv J hD).symm x) c) ∈
          Finsupp.supported (Multiplicity J c) ℂ {a : Label D | degree c a = e} := by
  have hs (c : Discriminant D) (z : Sector J c) :
      TensorProduct.map (moduleL D (representative D c) (inverseGram hD) 0)
          (LinearMap.id : Module.End ℂ (Multiplicity J c)) z = (e : ℂ) • z ↔
        tensorCoeff J c z ∈
          Finsupp.supported (Multiplicity J c) ℂ {a : Label D | degree c a = e} := by
    have h := D5.S1.Eigenstructure.DiagonalTensorEigenspace.eigen_iff_supported
      (carrierBasis D) (moduleL D (representative D c) (inverseGram hD) 0)
      (fun a => (degree c a : ℂ))
      (LatticeDualCosetEnergy.moduleL_basis_zero D (representative D c)
        (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
        (dualVector D (representative D c)) (dualVector_duality hD _)) (e : ℂ) z
    have he : {a : Label D | (degree c a : ℂ) = (e : ℂ)} =
        {a : Label D | degree c a = e} := by
      ext a
      exact Rat.cast_inj
    simpa only [he] using h
  have hmodel := classification_inverse J hD (omega D (inverseGram hD)) 1 x
  simp only [canonicalModule, directSumModule_mode, tensorModule_mode] at hmodel
  change (classificationEquiv J hD).symm (L0 J hD x) =
    DirectSum.lmap (fun c : Discriminant D =>
      TensorProduct.map (moduleL D (representative D c) (inverseGram hD) 0)
        (LinearMap.id : Module.End ℂ (Multiplicity J c)))
      ((classificationEquiv J hD).symm x) at hmodel
  constructor
  · intro hx c
    apply (hs c _).mp
    have h := congrArg (fun y : X => ((classificationEquiv J hD).symm y) c) hx
    rw [hmodel, DirectSum.lmap_apply] at h
    simpa only [map_smul, DFinsupp.smul_apply] using h
  · intro hx
    apply (classificationEquiv J hD).symm.injective
    rw [hmodel, map_smul]
    apply DFinsupp.ext
    intro c
    rw [DirectSum.lmap_apply]
    exact (hs c _).mpr (hx c)

/-- Inverting one finitely supported tensor coordinate is an ACTUAL basis tensor. -/
private theorem tensorCoeff_single (c : Discriminant D) (a : Label D)
    (w : Multiplicity J c) :
    (tensorCoeff J c).symm (Finsupp.single a w) = carrierBasis D a ⊗ₜ[ℂ] w := by
  apply (tensorCoeff J c).injective
  rw [LinearEquiv.apply_symm_apply]
  ext b
  simp [tensorCoeff, D5.S1.Eigenstructure.DiagonalTensorEigenspace.coeffEquiv,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

/-- Explicit finite algebraic expansion; no basis of a multiplicity space occurs. -/
theorem tensor_expansion (c : Discriminant D) (z : Sector J c) :
    z = ∑ a ∈ (tensorCoeff J c z).support,
      carrierBasis D a ⊗ₜ[ℂ] tensorCoeff J c z a := by
  let f := tensorCoeff J c z
  have hf : (∑ a ∈ f.support, Finsupp.single a (f a)) = f := by
    ext b
    change (Finsupp.lapply b : (Label D →₀ Multiplicity J c) →ₗ[ℂ] Multiplicity J c)
      (∑ a ∈ f.support, Finsupp.single a (f a)) = f b
    rw [map_sum]
    change (∑ a ∈ f.support, Finsupp.single a (f a) b) = f b
    rw [Finset.sum_eq_single b]
    · simp
    · intro a ha hab
      simp [Finsupp.single_apply, hab]
    · intro hb
      simp [Finsupp.notMem_support_iff.mp hb]
  calc
    z = (tensorCoeff J c).symm f := ((tensorCoeff J c).symm_apply_apply z).symm
    _ = (tensorCoeff J c).symm (∑ a ∈ f.support, Finsupp.single a (f a)) := by rw [hf]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      exact tensorCoeff_single J c a (f a)

/-- A finite sum of the displayed rational L0 eigenvectors for EVERY original x.
Supports are those of this vector; no uniform cutoff or spectral premise is used. -/
theorem finite_spectral_expansion (x : X) :
    let z := (classificationEquiv J hD).symm x
    x = ∑ c ∈ z.support, ∑ a ∈ (tensorCoeff J c (z c)).support,
      classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c
        (carrierBasis D a ⊗ₜ[ℂ] tensorCoeff J c (z c) a)) := by
  dsimp only
  let z := (classificationEquiv J hD).symm x
  have hz : (∑ c ∈ z.support, DirectSum.lof ℂ _ (Sector J) c (z c)) = z := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of z
  calc
    x = classificationEquiv J hD z := ((classificationEquiv J hD).apply_symm_apply x).symm
    _ = ∑ c ∈ z.support, classificationEquiv J hD
        (DirectSum.lof ℂ _ (Sector J) c (z c)) := by rw [← map_sum, hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      conv_lhs => rw [tensor_expansion J c (z c)]
      rw [map_sum, map_sum]

/-- Finite coefficient scaling by the phase of the ACTUAL rational eigenvalue. -/
def sectorRotation (c : Discriminant D) : Sector J c →ₗ[ℂ] Sector J c :=
  (tensorCoeff J c).symm.toLinearMap.comp
    ((coefficientScale (fun a : Label D => LatticeDiscriminantTheta.phase (degree c a : QmodZ))).comp
      (tensorCoeff J c).toLinearMap)

/-- Definition-level spectral readback on every vector-valued coefficient. -/
theorem sectorRotation_coeff (c : Discriminant D) (z : Sector J c) (a : Label D) :
    tensorCoeff J c (sectorRotation J c z) a =
      LatticeDiscriminantTheta.phase (degree c a : QmodZ) • tensorCoeff J c z a := by
  change tensorCoeff J c ((tensorCoeff J c).symm (coefficientScale _ (tensorCoeff J c z))) a = _
  rw [LinearEquiv.apply_symm_apply, coefficientScale_apply]

include hD in
/-- The substantive mod-Z identification makes spectral rotation scalar in
EACH actual sector tensor, with no condition on its multiplicity module. -/
theorem sectorRotation_eq (c : Discriminant D) (z : Sector J c) :
    sectorRotation J c z = thetaScalar c • z := by
  apply (tensorCoeff J c).injective
  ext a
  rw [sectorRotation_coeff, degree_class hD]
  simp only [map_smul, Finsupp.smul_apply, thetaScalar]

/-- An honest finite algebraic spectral-rotation endomorphism of the ORIGINAL
module. Finsupp.lsum and the algebraic direct sum guarantee finite evaluation. -/
def spectralRotation : Module.End ℂ X :=
  (classificationEquiv J hD).toLinearMap.comp
    ((DirectSum.lmap (sectorRotation J)).comp (classificationEquiv J hD).symm.toLinearMap)

/-- Exact equality with the actual natural balancing twist, in the correct
conjugation direction. This is NOT an assertion about analytic exponentiation. -/
theorem spectralRotation_eq_theta :
    spectralRotation J hD = (theta J hD).linearEquiv.toLinearMap := by
  have hm : DirectSum.lmap (sectorRotation J) = modelScale J (thetaScalar (D := D)) := by
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro z
    simp only [DirectSum.lmap_lof, modelScale, LinearMap.smul_apply,
      LinearMap.id_apply, sectorRotation_eq J hD]
  apply LinearMap.ext
  intro x
  change classificationEquiv J hD (DirectSum.lmap (sectorRotation J)
    ((classificationEquiv J hD).symm x)) =
    classificationEquiv J hD (modelScale J _ ((classificationEquiv J hD).symm x))
  rw [hm]

/-- Eigenvector readback of the finite algebraic rotation for arbitrary x.
The eigenspace description, rather than an assumed sector label for x, is used. -/
theorem spectralRotation_eigen (e : ℚ) (x : X) (hx : L0 J hD x = (e : ℂ) • x) :
    spectralRotation J hD x = LatticeDiscriminantTheta.phase (e : QmodZ) • x := by
  have hs := (L0_eigen_iff J hD e x).mp hx
  have hm : DirectSum.lmap (sectorRotation J) ((classificationEquiv J hD).symm x) =
      LatticeDiscriminantTheta.phase (e : QmodZ) • ((classificationEquiv J hD).symm x) := by
    apply DFinsupp.ext
    intro c
    rw [DirectSum.lmap_apply]
    change sectorRotation J c (((classificationEquiv J hD).symm x) c) =
      LatticeDiscriminantTheta.phase (e : QmodZ) • (((classificationEquiv J hD).symm x) c)
    apply (tensorCoeff J c).injective
    ext a
    rw [sectorRotation_coeff]
    simp only [map_smul, Finsupp.smul_apply]
    by_cases ha : degree c a = e
    · rw [ha]
    · have hz := (Finsupp.mem_supported' ℂ
        (tensorCoeff J c (((classificationEquiv J hD).symm x) c))).mp (hs c) a ha
      rw [hz, smul_zero, smul_zero]
  change classificationEquiv J hD (DirectSum.lmap (sectorRotation J)
    ((classificationEquiv J hD).symm x)) = _
  rw [hm, map_smul, LinearEquiv.apply_symm_apply]

end Original
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleConformalMonodromy
