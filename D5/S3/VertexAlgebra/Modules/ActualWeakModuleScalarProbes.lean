/-
SOURCE ONLY: UNCOMPILED / UNACCEPTED.

Full scalar probes for the ORIGINAL arbitrary weak lattice module. The sealed
generic tensor/direct-sum and classification conclusions are consumed as source
suppliers pending native verification 46811, not asserted to be kernel accepted.
Original positive-current nilpotence, Stage1 and Stage2 retain their separately
accepted status. The larger original goal remains active and incomplete.

The inverse below is literally classificationEquiv.symm. No decomposition,
naturality, joint separation, grading, dimension or nonzero-carrier hypothesis
is introduced. Every mode assertion quantifies over all source states and all
integer modes. The only basis used in the tensor argument is the EXPLICIT
source basis [k]monomial_e, never a basis of a multiplicity or of the target.
Mathlib's algebraic-dual separation may internally use classical choice.

Tensor coordinates have finite support for each single tensor. Classification
has its original vector-dependent finite Taylor/joint-weight supports. Neither
proof imposes a common support on different vectors, maps or coefficients.
There are no Hahn fields, Ward laws, normalized shifts, fusion endpoints or
duplicate Hom correspondences in this file.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleScalarProbes

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification

universe u v w
variable {D : LatticeData}

attribute [local instance] Classical.propDecidable

section Tensor

variable {W : Type v} [AddCommGroup W] [Module ℂ W]

/-- Balanced algebraic tensor contraction by an arbitrary algebraic functional. -/
def contract (ell : W →ₗ[ℂ] ℂ) : Carrier D ⊗[ℂ] W →ₗ[ℂ] Carrier D :=
  (TensorProduct.rid ℂ (Carrier D)).toLinearMap.comp
    (TensorProduct.map LinearMap.id ell)

@[simp] theorem contract_tmul (ell : W →ₗ[ℂ] ℂ) (v : Carrier D) (w : W) :
    contract ell (v ⊗ₜ[ℂ] w) = ell w • v := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

/-- Intertwining contraction with ANY actual source endomorphism; the proof
uses the balanced tensor coefficient formula and finite tensor induction. -/
theorem contract_map (ell : W →ₗ[ℂ] ℂ) (T : Module.End ℂ (Carrier D))
    (x : Carrier D ⊗[ℂ] W) :
    contract ell (TensorProduct.map T LinearMap.id x) = T (contract ell x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, contract_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The contraction is a full weak-module morphism, with every source state
and integer mode supplied by the actual tensorModule coefficient formula. -/
def contractHom (K : FullJacobiLatticeModule D (Carrier D)) (ell : W →ₗ[ℂ] ℂ) :
    ModuleHom (tensorModule K W) K where
  linearMap := contract ell
  intertwines a n x := by
    rw [tensorModule_mode]
    exact contract_map ell (mode K a n) x

/-- These are the literal charge/monomial indices of the actual Carrier. -/
abbrev Coordinate (D : LatticeData) := Charge D × (Index D →₀ ℕ)

/-- The source coordinate lambda_(k,e)(v) = coeff_e(v(k)). -/
def coordinate (D : LatticeData) (r : Coordinate D) : Carrier D →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ r.2).comp (Finsupp.lapply r.1)

@[simp] theorem coordinate_apply (r : Coordinate D) (v : Carrier D) :
    coordinate D r v = (v r.1).coeff r.2 := rfl

/-- Only the explicit source basis is used. Its indexing is a product of
charges and actual finite monomial exponents, including in rank zero. -/
def carrierBasis (D : LatticeData) : Module.Basis (Coordinate D) ℂ (Carrier D) :=
  (Finsupp.basis (fun _ : Charge D => MvPolynomial.basisMonomials (Index D) ℂ)).reindex
    (Equiv.sigmaEquivProd (Charge D) (Index D →₀ ℕ))

@[simp] theorem carrierBasis_apply (r : Coordinate D) :
    carrierBasis D r = Finsupp.single r.1 (MvPolynomial.monomial r.2 (1 : ℂ)) := by
  simp [carrierBasis, Module.Basis.reindex_apply, Finsupp.coe_basis,
    Equiv.sigmaEquivProd]

@[simp] theorem carrierBasis_repr (v : Carrier D) (r : Coordinate D) :
    (carrierBasis D).repr v r = coordinate D r v := by
  rw [carrierBasis, Module.Basis.repr_reindex_apply, Finsupp.basis_repr]
  rfl

/-- Mathlib's finite left-coordinate equivalence, specialized to the actual
source coordinates. No basis or finite-dimensionality of W is required. -/
def tensorCoordinates : Carrier D ⊗[ℂ] W ≃ₗ[ℂ] Coordinate D →₀ W := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D)

@[simp] theorem tensorCoordinates_tmul (v : Carrier D) (w : W) (r : Coordinate D) :
    tensorCoordinates (v ⊗ₜ[ℂ] w) r = coordinate D r v • w := by
  classical
  change TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D) (v ⊗ₜ[ℂ] w) r = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, carrierBasis_repr]

/-- An exact finite coordinate expansion of ONE tensor. This is the library
form of finite tensor induction followed by a finite union of source supports.
Its support belongs to x alone and can vary freely with x. -/
theorem tensorCoordinates_expansion (x : Carrier D ⊗[ℂ] W) :
    (∑ r ∈ (tensorCoordinates x).support,
      Finsupp.single r.1 (MvPolynomial.monomial r.2 (1 : ℂ)) ⊗ₜ[ℂ]
        tensorCoordinates x r) = x := by
  classical
  have h := (tensorCoordinates (D := D) (W := W)).symm_apply_apply x
  change (TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D)).symm
    (tensorCoordinates x) = x at h
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at h
  simpa only [Finsupp.sum, carrierBasis_apply] using h

/-- Apply one source coordinate to one contraction. Both sides are linear
in the tensor, so the simple-tensor identity suffices by finite induction. -/
theorem dual_tensorCoordinates (ell : W →ₗ[ℂ] ℂ)
    (x : Carrier D ⊗[ℂ] W) (r : Coordinate D) :
    ell (tensorCoordinates x r) = coordinate D r (contract ell x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    rw [tensorCoordinates_tmul, contract_tmul, map_smul, map_smul]
    exact mul_comm _ _
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Algebraic separation for EVERY complex vector space W, of arbitrary
universe and dimension, including zero. Dual separation is a proved Mathlib
theorem; it is not a premise. The finite source coordinates detect the tensor. -/
theorem tensor_eq_zero_of_contract_eq_zero (x : Carrier D ⊗[ℂ] W)
    (h : ∀ ell : W →ₗ[ℂ] ℂ, contract ell x = 0) : x = 0 := by
  classical
  have hc : tensorCoordinates x = 0 := by
    apply Finsupp.ext
    intro r
    apply (Module.forall_dual_apply_eq_zero_iff ℂ (tensorCoordinates x r)).mp
    intro ell
    rw [dual_tensorCoordinates, h ell, map_zero]
  apply (tensorCoordinates (D := D) (W := W)).injective
  rw [map_zero]
  exact hc

theorem tensor_contract_ext {x y : Carrier D ⊗[ℂ] W}
    (h : ∀ ell : W →ₗ[ℂ] ℂ, contract ell x = contract ell y) : x = y := by
  apply sub_eq_zero.mp
  apply tensor_eq_zero_of_contract_eq_zero
  intro ell
  rw [map_sub, h ell, sub_self]

end Tensor

/-- The actual full original sector module, with its literal action D beta,
vacuum theorem and full Borcherds theorem. It agrees with the record inside
canonicalModule by proof irrelevance, not by an assumed comparison map. -/
def sectorModule (D : LatticeData) (β : Charge D) :
    FullJacobiLatticeModule D (Carrier D) where
  stateField := action D β
  vacuum_field := module_vacuum D β
  borcherds := by
    intro a b x p q r
    change Function.HasFiniteSupport (moduleLeft D β p q r a b x) ∧
      Function.HasFiniteSupport (moduleFirst D β p q r a b x) ∧
      Function.HasFiniteSupport (moduleSecond D β p q r a b x) ∧ _
    exact module_borcherds D β a b x p q r

@[simp] theorem sectorModule_mode (β : Charge D) (a : Carrier D) (n : ℤ) :
    mode (sectorModule D β) a n = (action D β a)[[n]] := rfl

section Probes

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M)

/-- Literal dependent direct-sum component projection. -/
def component (c : Discriminant D) : Model J →ₗ[ℂ] Sector J c :=
  DirectSum.component ℂ (Discriminant D) (Sector J) c

@[simp] theorem component_apply (c : Discriminant D) (x : Model J) :
    component J c x = x c := rfl

/-- The ACTUAL direct-sum mode, followed by its ACTUAL tensor mode, on a
fixed component. The state and integer mode are completely arbitrary. -/
theorem component_canonical_mode (c : Discriminant D) (a : Carrier D) (n : ℤ)
    (x : Model J) :
    component J c (mode (canonicalModule J) a n x) =
      TensorProduct.map (mode (sectorModule D (representative D c)) a n)
        LinearMap.id (component J c x) := by
  change (mode (canonicalModule J) a n x) c = _
  rw [canonicalModule, directSumModule_mode]
  change mode (tensorModule (sectorModule D (representative D c)) (Multiplicity J c))
    a n (x c) = _
  rw [tensorModule_mode]
  rfl

def componentHom (c : Discriminant D) :
    ModuleHom (canonicalModule J)
      (tensorModule (sectorModule D (representative D c)) (Multiplicity J c)) where
  linearMap := component J c
  intertwines a n x := by
    rw [component_canonical_mode, tensorModule_mode]

variable (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- pi_(c,ell) = contract_ell composed component_c composed the LITERAL
classification inverse. Its only classification input is the supplier theorem
for original J and original positivity; no endpoint classifying hypothesis. -/
def scalarProbe (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ) :
    M →ₗ[ℂ] Carrier D :=
  (contract ell).comp ((component J c).comp
    (classificationEquiv J positiveG).symm.toLinearMap)

@[simp] theorem scalarProbe_apply (c : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (x : M) :
    scalarProbe J positiveG c ell x =
      contract ell (component J c ((classificationEquiv J positiveG).symm x)) := rfl

/-- The literal classification inverse-mode law and coefficient calculations,
without a naturality hypothesis or a restriction to generating current states. -/
theorem scalarProbe_modes (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ)
    (a : Carrier D) (n : ℤ) (x : M) :
    scalarProbe J positiveG c ell (mode J a n x) =
      mode (sectorModule D (representative D c)) a n (scalarProbe J positiveG c ell x) := by
  change contract ell (component J c
    ((classificationEquiv J positiveG).symm (mode J a n x))) =
      mode (sectorModule D (representative D c)) a n
        (contract ell (component J c ((classificationEquiv J positiveG).symm x)))
  rw [classification_inverse, component_canonical_mode, contract_map]

/-- Every scalar probe is a FULL original ModuleHom to the actual sector. -/
def scalarProbeHom (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ) :
    ModuleHom J (sectorModule D (representative D c)) where
  linearMap := scalarProbe J positiveG c ell
  intertwines := scalarProbe_modes J positiveG c ell

/-- Exact values on canonical coordinates, useful independently of any field. -/
theorem scalarProbe_classification (c : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (x : Model J) :
    scalarProbe J positiveG c ell (classificationEquiv J positiveG x) =
      contract ell (component J c x) := by
  rw [scalarProbe_apply, (classificationEquiv J positiveG).symm_apply_apply]

@[simp] theorem scalarProbe_classification_lof_same (c : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (x : Sector J c) :
    scalarProbe J positiveG c ell
      (classificationEquiv J positiveG (DirectSum.lof ℂ (Discriminant D) (Sector J) c x)) =
      contract ell x := by
  classical
  rw [scalarProbe_classification]
  change contract ell (DirectSum.component ℂ (Discriminant D) (Sector J) c
    (DirectSum.lof ℂ (Discriminant D) (Sector J) c x)) = _
  rw [DirectSum.component.lof_self]

@[simp] theorem scalarProbe_classification_lof_tmul (c : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (v : Carrier D) (w : Multiplicity J c) :
    scalarProbe J positiveG c ell
      (classificationEquiv J positiveG
        (DirectSum.lof ℂ (Discriminant D) (Sector J) c (v ⊗ₜ[ℂ] w))) = ell w • v := by
  rw [scalarProbe_classification_lof_same, contract_tmul]

theorem scalarProbe_classification_lof_ne (c d : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (hdc : d ≠ c) (x : Sector J d) :
    scalarProbe J positiveG c ell
      (classificationEquiv J positiveG (DirectSum.lof ℂ (Discriminant D) (Sector J) d x)) = 0 := by
  classical
  rw [scalarProbe_classification]
  have hc : component J c (DirectSum.lof ℂ (Discriminant D) (Sector J) d x) = 0 := by
    change DirectSum.component ℂ (Discriminant D) (Sector J) c
      (DirectSum.lof ℂ (Discriminant D) (Sector J) d x) = 0
    rw [DirectSum.component.of, dif_neg hdc]
  rw [hc, map_zero]

/-- Joint separation is PROVED for actual J. Apply tensor separation to each
component of its literal classification inverse, then dependent direct-sum
extensionality, then injectivity of that inverse. No support is compared with
the support of another vector or with a support of any family of coefficients. -/
theorem eq_zero_of_scalarProbe_eq_zero (x : M)
    (h : ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      scalarProbe J positiveG c ell x = 0) : x = 0 := by
  have hc : (classificationEquiv J positiveG).symm x = 0 := by
    apply DFinsupp.ext
    intro c
    change component J c ((classificationEquiv J positiveG).symm x) = 0
    apply tensor_eq_zero_of_contract_eq_zero
    intro ell
    exact h c ell
  apply (classificationEquiv J positiveG).symm.injective
  rw [map_zero]
  exact hc

theorem scalarProbe_eq_zero_iff (x : M) :
    (∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      scalarProbe J positiveG c ell x = 0) ↔ x = 0 := by
  refine ⟨eq_zero_of_scalarProbe_eq_zero J positiveG x, ?_⟩
  rintro rfl c ell
  exact map_zero (scalarProbe J positiveG c ell)

/-- Equality of two INDIVIDUAL vectors is detected by all scalar probes. -/
theorem scalarProbe_ext {x y : M}
    (h : ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      scalarProbe J positiveG c ell x = scalarProbe J positiveG c ell y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_scalarProbe_eq_zero J positiveG
  intro c ell
  rw [map_sub, h c ell, sub_self]

theorem scalarProbe_eq_iff (x y : M) :
    x = y ↔ ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      scalarProbe J positiveG c ell x = scalarProbe J positiveG c ell y := by
  refine ⟨?_, scalarProbe_ext J positiveG⟩
  rintro rfl c ell
  rfl

variable {N : Type w} [AddCommGroup N] [Module ℂ N]

/-- Extensionality on linear maps from ANY independent carrier universe.
The separation argument is applied separately at each input vector. -/
theorem scalarProbe_linearMap_ext {f g : N →ₗ[ℂ] M}
    (h : ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      (scalarProbe J positiveG c ell).comp f = (scalarProbe J positiveG c ell).comp g) :
    f = g := by
  apply LinearMap.ext
  intro x
  apply scalarProbe_ext J positiveG
  intro c ell
  exact LinearMap.congr_fun (h c ell) x

theorem scalarProbe_linearMap_eq_iff (f g : N →ₗ[ℂ] M) :
    f = g ↔ ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      (scalarProbe J positiveG c ell).comp f = (scalarProbe J positiveG c ell).comp g := by
  refine ⟨?_, scalarProbe_linearMap_ext J positiveG⟩
  rintro rfl c ell
  rfl

theorem scalarProbe_linearMap_eq_zero_iff (f : N →ₗ[ℂ] M) :
    f = 0 ↔ ∀ (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ),
      (scalarProbe J positiveG c ell).comp f = 0 := by
  simpa only [LinearMap.comp_zero] using
    (scalarProbe_linearMap_eq_iff J positiveG f (0 : N →ₗ[ℂ] M))

end Probes

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleScalarProbes
