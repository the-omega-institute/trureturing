/-
SOURCE_ONLY_UNCOMPILED. Explicit original-module coordinates, not a
classification or kernel receipt in the absence of native checking.

The only choices are the existing integral discriminant representative,
its existing cosetEquiv, and the actual finite joint-weight decomposition.
The inverse is a finite Taylor-coefficient sum followed by a finite
joint-weight sum. Its charged return is exactly epsilon(-n,n)^-1 S_-n.
Neither invertibility of Phi nor a charged field formula is assumed.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundFieldReconstruction
import D5.S3.VertexAlgebra.Modules.FullJacobiTensorModule
import D5.S3.VertexAlgebra.Modules.FullJacobiDirectSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleSectorCoordinates

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundTaylorCoefficients
open ActualGroundJointWeights ActualGroundChargedSelection ActualGroundChargedTranslations
open ActualGroundFieldReconstruction
open LatticeSugawaraCurrents (gramComplex)
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

attribute [local instance] Classical.propDecidable

local instance jointWeightFamilyCoe {ι : Type} {N : Type u}
    [AddCommGroup N] [Module ℂ N] :
    CoeOut (ι → Submodule ℂ N) (ι → Type u) :=
  ⟨fun A b => A b⟩

abbrev Multiplicity (c : Discriminant D) := jointWeight J (representative D c)
abbrev Sector (c : Discriminant D) := Carrier D ⊗[ℂ] Multiplicity J c
abbrev Model := ⨁ c : Discriminant D, Sector J c

/-- c,n are INTEGRAL coordinates of b. The physical vector is G_Q^-1 b. -/
def weightIndex (b : Charge D) : Discriminant D × Charge D :=
  (cosetEquiv D hD).symm b

theorem weightIndex_spec (b : Charge D) :
    shiftWeight (representative D (weightIndex hD b).1) (weightIndex hD b).2 = b := by
  have he := (cosetEquiv D hD).apply_symm_apply b
  change representative D (weightIndex hD b).1 + gramMap D (weightIndex hD b).2 = b at he
  simpa only [shiftWeight, gramMap, Matrix.toLin'_apply] using he

theorem weightIndex_shift (c : Discriminant D) (n : Charge D) :
    weightIndex hD (shiftWeight (representative D c) n) = (c,n) := by
  change (cosetEquiv D hD).symm _ = _
  apply (cosetEquiv D hD).injective
  rw [(cosetEquiv D hD).apply_symm_apply]
  rfl

/-- Actual S transport of a representative multiplicity into M. -/
def chargedGround (β n : Charge D) : jointWeight J β →ₗ[ℂ] M :=
  (Omega J).subtype.comp
    ((S J hNil H hHG hGH n β).comp (jointWeight J β).subtype)

@[simp] theorem chargedGround_apply (β n : Charge D) (w : jointWeight J β) :
    chargedGround J hNil H hHG hGH β n w =
      (S J hNil H hHG hGH n β w.val : M) := rfl

def polynomialGround (β n : Charge D) :
    Oscillator D →ₗ[ℂ] jointWeight J β →ₗ[ℂ] M where
  toFun P := (polynomialOperator J hNil H hHG P).comp
    (chargedGround J hNil H hHG hGH β n)
  map_add' P Q := by ext w; simp
  map_smul' a P := by ext w; simp

def sectorPhi (β : Charge D) : Carrier D ⊗[ℂ] jointWeight J β →ₗ[ℂ] M :=
  TensorProduct.lift (Finsupp.lsum ℂ (fun n => polynomialGround J hNil H hHG hGH β n))

@[simp] theorem sectorPhi_single (β n : Charge D) (P : Oscillator D)
    (w : jointWeight J β) :
    sectorPhi J hNil H hHG hGH β (Finsupp.single n P ⊗ₜ[ℂ] w) =
      polynomialOperator J hNil H hHG P
        (S J hNil H hHG hGH n β w.val : M) := by
  simp [sectorPhi, polynomialGround]

def Phi : Model J →ₗ[ℂ] M :=
  DirectSum.toModule ℂ (Discriminant D) M
    (fun c => sectorPhi J hNil H hHG hGH (representative D c))

@[simp] theorem Phi_single (c : Discriminant D) (n : Charge D) (P : Oscillator D)
    (w : Multiplicity J c) :
    Phi J hNil H hHG hGH
      (DirectSum.lof ℂ (Discriminant D) (Sector J) c (Finsupp.single n P ⊗ₜ[ℂ] w)) =
      polynomialOperator J hNil H hHG P
        (S J hNil H hHG hGH n (representative D c) w.val : M) := by
  rw [Phi, DirectSum.toModule_lof, sectorPhi_single]

/-- Normalize a component of weight b back to its representative weight.
The equality transport is between actual jointWeight submodules. -/
def returnWeight (b : Charge D) : jointWeight J b →ₗ[ℂ]
    Multiplicity J (weightIndex hD b).1 :=
  (inverseTranslation J hNil H hHG hGH (weightIndex hD b).2
    (representative D (weightIndex hD b).1)).comp
      (LinearEquiv.ofEq (jointWeight J b)
        (jointWeight J (shiftWeight (representative D (weightIndex hD b).1)
          (weightIndex hD b).2))
        (congrArg (jointWeight J) (weightIndex_spec hD b).symm)).toLinearMap

theorem returnWeight_coe (b : Charge D) (v : jointWeight J b) :
    ((returnWeight J hNil H hHG hGH hD b v).val : M) =
      (epsilon D (-(weightIndex hD b).2) (weightIndex hD b).2)⁻¹ •
        (S J hNil H hHG hGH (-(weightIndex hD b).2) b v.val : M) := by
  change (epsilon D (-(weightIndex hD b).2) (weightIndex hD b).2)⁻¹ •
    (S J hNil H hHG hGH (-(weightIndex hD b).2)
      (shiftWeight (representative D (weightIndex hD b).1) (weightIndex hD b).2)
      ((LinearEquiv.ofEq (jointWeight J b)
        (jointWeight J (shiftWeight (representative D (weightIndex hD b).1)
          (weightIndex hD b).2))
        (congrArg (jointWeight J) (weightIndex_spec hD b).symm)) v).val : M) = _
  rw [LinearEquiv.coe_ofEq_apply, weightIndex_spec]

private theorem S_returnWeight (b : Charge D) (v : jointWeight J b) :
    S J hNil H hHG hGH (weightIndex hD b).2
      (representative D (weightIndex hD b).1)
        (returnWeight J hNil H hHG hGH hD b v).val = v.val := by
  have hw : v.val ∈ jointWeight J
      (shiftWeight (representative D (weightIndex hD b).1) (weightIndex hD b).2) := by
    rw [weightIndex_spec]
    exact v.property
  have hraw : (returnWeight J hNil H hHG hGH hD b v).val =
      (epsilon D (-(weightIndex hD b).2) (weightIndex hD b).2)⁻¹ •
        S J hNil H hHG hGH (-(weightIndex hD b).2) b v.val := by
    apply Subtype.ext
    exact returnWeight_coe J hNil H hHG hGH hD b v
  rw [hraw]
  have he := S_Sinv J hNil H hHG hGH (weightIndex hD b).2
    (representative D (weightIndex hD b).1) v.val hw
  simpa only [Sinv, LinearMap.smul_apply, weightIndex_spec] using he

/-- The finite joint decomposition of an actual eigenvector is its one
inclusion, proved using the already supplied inverse, not assumed as a law. -/
private theorem jointDecomposition_weight (b : Charge D) (v : jointWeight J b) :
    jointDecomposition J hNil hD v.val =
      DirectSum.lof ℂ (Charge D) (jointWeight J) b v := by
  let e := jointDecomposition J hNil hD
  have he := e.apply_symm_apply (DirectSum.lof ℂ (Charge D) (jointWeight J) b v)
  have hv : e.symm (DirectSum.lof ℂ (Charge D) (jointWeight J) b v) = v.val := by
    change DirectSum.coeLinearMap (jointWeight J)
      (DirectSum.lof ℂ (Charge D) (jointWeight J) b v) = v.val
    exact DirectSum.coeLinearMap_of (jointWeight J) b v
  rw [hv] at he
  exact he

/-- One Taylor monomial, expanded over the actual finite joint-weight
support. This map is linear even though the individual supports vary. -/
def coefficientLift (d : Index D →₀ ℕ) : Omega J →ₗ[ℂ] Model J :=
  (DirectSum.toModule ℂ (Charge D) (Model J) (fun b =>
    (DirectSum.lof ℂ (Discriminant D) (Sector J) (weightIndex hD b).1).comp
      (((TensorProduct.mk ℂ (Carrier D) (Multiplicity J (weightIndex hD b).1))
        (Finsupp.single (weightIndex hD b).2 (MvPolynomial.monomial d 1))).comp
          (returnWeight J hNil H hHG hGH hD b)))).comp
            (jointDecomposition J hNil hD).toLinearMap

theorem coefficientLift_expansion (d : Index D →₀ ℕ) (v : Omega J) :
    coefficientLift J hNil H hHG hGH hD d v =
      ∑ b ∈ (jointDecomposition J hNil hD v).support,
        DirectSum.lof ℂ (Discriminant D) (Sector J) (weightIndex hD b).1
          (Finsupp.single (weightIndex hD b).2 (MvPolynomial.monomial d 1) ⊗ₜ[ℂ]
            returnWeight J hNil H hHG hGH hD b
              ((jointDecomposition J hNil hD v) b)) := by
  change DirectSum.toModule ℂ (Charge D) (Model J) _
    (jointDecomposition J hNil hD v) = _
  have hs := DirectSum.sum_support_of (jointDecomposition J hNil hD v)
  conv_lhs => rw [← hs, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  change DirectSum.toModule ℂ (Charge D) (Model J) _
    (DirectSum.lof ℂ (Charge D) (fun b => ↥(jointWeight J b)) b _) = _
  rw [DirectSum.toModule_lof]
  rfl

private theorem Phi_coefficientLift (d : Index D →₀ ℕ) (v : Omega J) :
    Phi J hNil H hHG hGH (coefficientLift J hNil H hHG hGH hD d v) =
      (W J hNil H hHG).creation d v.val := by
  rw [coefficientLift_expansion, map_sum]
  have hterms (b : Charge D) (w : jointWeight J b) :
      Phi J hNil H hHG hGH
        (DirectSum.lof ℂ (Discriminant D) (Sector J) (weightIndex hD b).1
          (Finsupp.single (weightIndex hD b).2 (MvPolynomial.monomial d 1) ⊗ₜ[ℂ]
            returnWeight J hNil H hHG hGH hD b w)) =
        (W J hNil H hHG).creation d (w.val : M) := by
    rw [Phi_single, polynomialOperator_monomial, one_smul,
      S_returnWeight J hNil H hHG hGH hD]
  simp_rw [hterms]
  rw [← map_sum]
  congr 1
  have he := (jointDecomposition J hNil hD).symm_apply_apply v
  change DirectSum.coeLinearMap (jointWeight J) (jointDecomposition J hNil hD v) = v at he
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum] at he
  simpa only [DFinsupp.sum, Submodule.coe_sum] using congrArg (fun x : Omega J => (x : M)) he

/-- Concrete inverse: finite Taylor support, then finite integral joint
weight support, with the original inverse charged normalization. -/
def Psi : M →ₗ[ℂ] Model J :=
  (Finsupp.lsum ℂ (fun d =>
    (coefficientLift J hNil H hHG hGH hD d).comp
      (vacuumToOmega J hNil H hHG hGH).toLinearMap)).comp
        (W J hNil H hHG).coefficients

theorem Psi_expansion (v : M) :
    Psi J hNil H hHG hGH hD v =
      ∑ d ∈ ((W J hNil H hHG).coefficients v).support,
        coefficientLift J hNil H hHG hGH hD d
          (vacuumToOmega J hNil H hHG hGH
            ((W J hNil H hHG).coefficient d v)) := by
  simp only [Psi, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum,
    WeylData.coefficients_apply, LinearEquiv.coe_coe]

theorem Phi_Psi (v : M) :
    Phi J hNil H hHG hGH (Psi J hNil H hHG hGH hD v) = v := by
  rw [Psi_expansion, map_sum]
  simp_rw [Phi_coefficientLift, vacuumToOmega_coe]
  simpa only [WeylData.evaluate, Finsupp.lsum_apply, Finsupp.sum,
    WeylData.coefficients_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      using (W J hNil H hHG).evaluate_coefficients v

private theorem coefficientLift_charged (c : Discriminant D) (n : Charge D)
    (d : Index D →₀ ℕ) (w : Multiplicity J c) :
    coefficientLift J hNil H hHG hGH hD d
      (S J hNil H hHG hGH n (representative D c) w.val) =
      DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single n (MvPolynomial.monomial d 1) ⊗ₜ[ℂ] w) := by
  let b := shiftWeight (representative D c) n
  let z : jointWeight J b :=
    ⟨S J hNil H hHG hGH n (representative D c) w.val,
      S_mem_jointWeight J hNil H hHG hGH n (representative D c) w.val w.property⟩
  have hi : weightIndex hD b = (c,n) := weightIndex_shift hD c n
  change DirectSum.toModule ℂ (Charge D) (Model J) _
    (jointDecomposition J hNil hD z.val) = _
  rw [jointDecomposition_weight, DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
  have hreturn : (returnWeight J hNil H hHG hGH hD b z).val = w.val := by
    apply Subtype.ext
    rw [returnWeight_coe J hNil H hHG hGH hD b z, hi]
    change (Sinv J hNil H hHG hGH n (representative D c)
      (S J hNil H hHG hGH n (representative D c) w.val) : M) = (w.val : M)
    exact congrArg (fun v : Omega J => (v : M))
      (Sinv_S J hNil H hHG hGH n (representative D c) w.val w.property)
  have hinsert (p : Discriminant D × Charge D) (hp : p = (c,n))
      (v : Multiplicity J p.1) (hv : v.val = w.val) :
      DirectSum.lof ℂ (Discriminant D) (Sector J) p.1
        (Finsupp.single p.2 (MvPolynomial.monomial d 1) ⊗ₜ[ℂ] v) =
      DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single n (MvPolynomial.monomial d 1) ⊗ₜ[ℂ] w) := by
    subst p
    have hv' : v = w := Subtype.ext hv
    subst v
    rfl
  exact hinsert (weightIndex hD b) hi _ hreturn

private theorem Psi_creation (d : Index D →₀ ℕ) (v : Omega J) :
    Psi J hNil H hHG hGH hD ((W J hNil H hHG).creation d v.val) =
      coefficientLift J hNil H hHG hGH hD d v := by
  let w := (vacuumToOmega J hNil H hHG hGH).symm v
  have he := (W J hNil H hHG).coefficients_evaluate (Finsupp.single d w)
  rw [WeylData.evaluate_single] at he
  change Finsupp.lsum ℂ _ ((W J hNil H hHG).coefficients
    ((W J hNil H hHG).creation d w.val)) = _
  rw [he, Finsupp.lsum_single]
  exact congrArg (coefficientLift J hNil H hHG hGH hD d)
    ((vacuumToOmega J hNil H hHG hGH).apply_symm_apply v)

theorem Psi_Phi (v : Model J) :
    Psi J hNil H hHG hGH hD (Phi J hNil H hHG hGH v) = v := by
  have h : (Psi J hNil H hHG hGH hD).comp (Phi J hNil H hHG hGH) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro c
    apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro n
    apply (MvPolynomial.basisMonomials (Index D) ℂ).ext
    intro d
    apply LinearMap.ext
    intro w
    change Psi J hNil H hHG hGH hD
      (Phi J hNil H hHG hGH
        (DirectSum.lof ℂ (Discriminant D) (Sector J) c
          (Finsupp.single n (MvPolynomial.monomial d 1) ⊗ₜ[ℂ] w))) = _
    rw [Phi_single, polynomialOperator_monomial, one_smul,
      Psi_creation, coefficientLift_charged]
    rfl
  exact LinearMap.congr_fun h v

def coordinateEquiv : Model J ≃ₗ[ℂ] M where
  toLinearMap := Phi J hNil H hHG hGH
  invFun := Psi J hNil H hHG hGH hD
  left_inv := Psi_Phi J hNil H hHG hGH hD
  right_inv := Phi_Psi J hNil H hHG hGH hD

/-- Exact original cocycle and actual E formula in sector coordinates.
The scalar is epsilon(alpha,n), and the frequency shift has the +j sign. -/
theorem E_sector (β n α : Charge D) (P : Oscillator D) (m : ℤ)
    (w : jointWeight J β) :
    E J α m (sectorPhi J hNil H hHG hGH β (Finsupp.single n P ⊗ₜ[ℂ] w)) =
      epsilon D α n •
        ∑ j ∈ (translatedPolynomial D α P).support,
          polynomialOperator J hNil H hHG
            ((translatedPolynomial D α P).coeff j *
              creationCoeff D α (-m - 1 - bilinear D α n - weightPairing α β + j))
            (S J hNil H hHG hGH (α+n) β w.val : M) := by
  rw [sectorPhi_single, E_polynomial_ground J hNil H hHG hGH α
    (shiftWeight β n) m P _ (S_mem_jointWeight J hNil H hHG hGH n β w.val w.property)]
  rw [S_comp J hNil H hHG hGH α n β w.val w.property, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Submodule.coe_smul, map_smul, weightPairing_shift]
  have hk : -m - 1 - (weightPairing α β + bilinear D α n) + j =
      -m - 1 - bilinear D α n - weightPairing α β + j := by omega
  simp only [hk]

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleSectorCoordinates
