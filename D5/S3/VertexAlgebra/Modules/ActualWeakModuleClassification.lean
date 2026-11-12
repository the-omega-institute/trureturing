/-
SOURCE_ONLY_UNCOMPILED. The full original target remains unaccepted.

The endpoint takes only the original FullJacobiLatticeModule and original
positive-definite Gram matrix. Positive-current nilpotence is consumed from
the sealed original-module nilpotence source; both inverse Gram orientations
are constructed from positivity. There is no spectral, tensor-module,
Fock-intertwining, charged-field, S-law or classification hypothesis.

The actual sector field is action D beta. Its internal compression level
is 1. The full original vacuum/Jacobi suppliers are used literally inside
the tensor/direct-sum construction. The all-state extension is the supplied
module_iterate/finite_negative_generation proof, not a new VOA axiom.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleSectorCoordinates
import D5.S3.VertexAlgebra.Modules.FullJacobiPositiveCurrentNilpotence
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticeAllStateField
open LatticeDiscriminantTheta LatticeDualCosetModule
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundTaylorCoefficients
open ActualGroundJointWeights ActualGroundChargedSelection ActualGroundChargedTranslations
open ActualGroundFieldReconstruction ActualWeakModuleSectorCoordinates
open FullJacobiIntertwiner FullJacobiTensorModule FullJacobiDirectSum
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

attribute [local instance] Classical.propDecidable

variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

private theorem annihilation_polynomial (x : Index D) (P : Oscillator D) (v : M) :
    (W J hNil H hHG).D x (polynomialOperator J hNil H hHG P v) =
      polynomialOperator J hNil H hHG P ((W J hNil H hHG).D x v) +
        polynomialOperator J hNil H hHG (MvPolynomial.pderiv x P) v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.C c : Oscillator D) = c • 1 := MvPolynomial.C_eq_smul_one
    simp [hc, polynomialOperator_one]
  | add P Q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
    abel
  | mul_X P y hp =>
    rw [mul_comm P (MvPolynomial.X y), polynomialOperator_X_mul,
      Module.End.mul_apply]
    change (W J hNil H hHG).D x ((W J hNil H hHG).X y
      (polynomialOperator J hNil H hHG P v)) = _
    rw [(W J hNil H hHG).dx, hp]
    by_cases hxy : x = y
    · subst y
      simp [MvPolynomial.pderiv_mul, polynomialOperator_X_mul,
        polynomialOperator_one, map_add, add_assoc, add_comm, add_left_comm]
      rfl
    · simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hxy, Ne.symm hxy,
        polynomialOperator_X_mul, polynomialOperator_one, map_add]
      rfl

private theorem zero_current_polynomial (i : Fin D.rank) (P : Oscillator D) (v : M) :
    current J i 0 (polynomialOperator J hNil H hHG P v) =
      polynomialOperator J hNil H hHG P (current J i 0 v) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.C c : Oscillator D) = c • 1 := MvPolynomial.C_eq_smul_one
    simp [hc, polynomialOperator_one]
  | add P Q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X P x hp =>
    rw [mul_comm P (MvPolynomial.X x), polynomialOperator_X_mul]
    simp only [Module.End.mul_apply]
    simp only [creation]
    rw [WeylData.commute_apply _ _ (zero_current_commutes_current J i x.1 _), hp]

/-- The literal shifted current polynomial, on the actual charged ground.
Negative, zero and strictly positive integer modes are handled separately. -/
private theorem current_sector (β n : Charge D) (i : Fin D.rank) (m : ℤ)
    (P : Oscillator D) (w : jointWeight J β) :
    current J i m (polynomialOperator J hNil H hHG P
      (S J hNil H hHG hGH n β w.val : M)) =
      polynomialOperator J hNil H hHG (shiftedCurrentPolynomial D β 1 i n m P)
        (S J hNil H hHG hGH n β w.val : M) := by
  classical
  let z := S J hNil H hHG hGH n β w.val
  have hz : z ∈ jointWeight J (shiftWeight β n) :=
    S_mem_jointWeight J hNil H hHG hGH n β w.val w.property
  by_cases hm : m < 0
  · have hi : -(((-m-1).toNat : ℕ) : ℤ)-1 = m := by omega
    simp only [shiftedCurrentPolynomial, if_pos hm, LinearMap.mulLeft_apply]
    rw [polynomialOperator_X_mul, Module.End.mul_apply]
    change _ = current J i (-(((-m-1).toNat : ℕ) : ℤ)-1) _
    rw [hi]
  · by_cases hzero : m = 0
    · subst m
      rw [zero_current_polynomial]
      have he := (mem_jointWeight_iff J (shiftWeight β n) z).mp hz i
      rw [he, map_smul]
      simp only [shiftedCurrentPolynomial, lt_self_iff_false, if_false,
        one_mul]
      change ((shiftWeight β n i : ℤ) : ℂ) •
          polynomialOperator J hNil H hHG P z.val =
        polynomialOperator J hNil H hHG
          (((bilinear D (unitCharge D i) n + β i : ℤ) : ℂ) • P) z.val
      rw [map_smul, LinearMap.smul_apply]
      congr 1
      simp only [shiftWeight, Pi.add_apply, gram_mulVec_unit, Int.cast_add]
      ring
    · let r : ℕ := (m-1).toNat
      have hi : m = (r : ℤ)+1 := by dsimp [r]; omega
      have hvac (j : Fin D.rank) : annihilation J H j r z.val = 0 := by
        simp [annihilation, rowMode, (mem_Omega J z.val).mp z.property]
      have hpos := positive_current_from_normalized J H hGH i r
      have hmode (v : M) : current J i ((r : ℤ)+1) v =
          (r+1 : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) • annihilation J H j r v := by
        simpa only [LinearMap.smul_apply, LinearMap.sum_apply, gramComplex,
          Matrix.map_apply] using (LinearMap.congr_fun hpos v).symm
      have hd (j : Fin D.rank) :
          annihilation J H j r (polynomialOperator J hNil H hHG P z.val) =
            polynomialOperator J hNil H hHG (MvPolynomial.pderiv (j,r) P) z.val := by
        have hd := annihilation_polynomial J hNil H hHG (j,r) P z.val
        simpa only [show (W J hNil H hHG).D (j,r) = annihilation J H j r from rfl,
          hvac, map_zero, zero_add] using hd
      rw [hi, hmode, shiftedCurrentPolynomial,
        if_neg (show ¬ (r : ℤ)+1 < 0 by omega),
        if_neg (show (r : ℤ)+1 ≠ 0 by omega),
        LinearMap.smul_apply, LinearMap.sum_apply,
        show ((r : ℤ)+1-1).toNat = r by omega]
      have hc : (((r : ℤ)+1 : ℤ) : ℂ) = (r+1 : ℂ) := by push_cast; rfl
      rw [hc, map_smul, LinearMap.smul_apply]
      congr 1
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hd j, LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
      rfl

/-- The original currentState is literally the neutral one-variable state. -/
private theorem currentState_single (i : Fin D.rank) :
    currentState D i = Finsupp.single (0 : Charge D) (MvPolynomial.X (i,0)) := by
  simp [currentState, neutralField_ncoeff, neutralMode, neutralPolynomialMode, vacuum]

/-- The exact existing sector vacuum and full Jacobi supplier are consumed
inside the actual tensor/direct-sum module, without a separate sector adapter. -/
def canonicalModule : FullJacobiLatticeModule D (Model J) :=
  directSumModule (fun c : Discriminant D =>
    tensorModule
      ({ stateField := action D (representative D c)
         vacuum_field := module_vacuum D (representative D c)
         borcherds := by
           intro a b v p q r
           change Function.HasFiniteSupport (moduleLeft D (representative D c) p q r a b v) ∧
             Function.HasFiniteSupport (moduleFirst D (representative D c) p q r a b v) ∧
             Function.HasFiniteSupport (moduleSecond D (representative D c) p q r a b v) ∧ _
           exact module_borcherds D (representative D c) a b v p q r } :
        FullJacobiLatticeModule D (Carrier D))
      (Multiplicity J c))

private theorem sectorPhi_current (β : Charge D) (i : Fin D.rank) (m : ℤ)
    (x : Carrier D ⊗[ℂ] jointWeight J β) :
    sectorPhi J hNil H hHG hGH β
      (TensorProduct.map ((action D β (currentState D i))[[m]]) LinearMap.id x) =
      current J i m (sectorPhi J hNil H hHG hGH β x) := by
  have h : (sectorPhi J hNil H hHG hGH β).comp
      (TensorProduct.map ((action D β (currentState D i))[[m]]) LinearMap.id) =
      (current J i m).comp (sectorPhi J hNil H hHG hGH β) := by
    apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro n
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro w
    change sectorPhi J hNil H hHG hGH β
      (((action D β (currentState D i))[[m]]) (Finsupp.single n P) ⊗ₜ[ℂ] w) =
      current J i m (sectorPhi J hNil H hHG hGH β (Finsupp.single n P ⊗ₜ[ℂ] w))
    rw [currentState_single, action_current_coefficients,
      sectorPhi_single, sectorPhi_single]
    exact (current_sector J hNil H hHG hGH β n i m P w).symm
  exact LinearMap.congr_fun h x

private theorem sectorPhi_exponential (β α : Charge D) (m : ℤ)
    (x : Carrier D ⊗[ℂ] jointWeight J β) :
    sectorPhi J hNil H hHG hGH β
      (TensorProduct.map ((action D β (groundState D α))[[m]]) LinearMap.id x) =
      E J α m (sectorPhi J hNil H hHG hGH β x) := by
  have h : (sectorPhi J hNil H hHG hGH β).comp
      (TensorProduct.map ((action D β (groundState D α))[[m]]) LinearMap.id) =
      (E J α m).comp (sectorPhi J hNil H hHG hGH β) := by
    apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro n
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro w
    change sectorPhi J hNil H hHG hGH β
      (((action D β (groundState D α))[[m]]) (Finsupp.single n P) ⊗ₜ[ℂ] w) =
      E J α m (sectorPhi J hNil H hHG hGH β (Finsupp.single n P ⊗ₜ[ℂ] w))
    rw [show groundState D α = Finsupp.single α (1 : Oscillator D) from rfl,
      action_ground_coefficients]
    rw [E_sector J hNil H hHG hGH β n α P m w]
    simp only [shiftedRawSingle, one_mul, smul_eq_mul,
      ← TensorProduct.smul_tmul', map_smul, sectorPhi_single,
      map_sum, LinearMap.sum_apply, weightPairing]
  exact LinearMap.congr_fun h x

private theorem Phi_current (i : Fin D.rank) (m : ℤ) (x : Model J) :
    Phi J hNil H hHG hGH (current (canonicalModule J) i m x) =
      current J i m (Phi J hNil H hHG hGH x) := by
  have h : (Phi J hNil H hHG hGH).comp (current (canonicalModule J) i m) =
      (current J i m).comp (Phi J hNil H hHG hGH) := by
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro y
    change Phi J hNil H hHG hGH
      (mode (canonicalModule J) (currentState D i) m
        (DirectSum.lof ℂ (Discriminant D) (Sector J) c y)) = _
    simp only [LinearMap.comp_apply, canonicalModule, directSumModule_mode, DirectSum.lmap_lof,
      tensorModule_mode, mode, Phi, DirectSum.toModule_lof]
    exact sectorPhi_current J hNil H hHG hGH (representative D c) i m y
  exact LinearMap.congr_fun h x

private theorem Phi_exponential (α : Charge D) (m : ℤ) (x : Model J) :
    Phi J hNil H hHG hGH (E (canonicalModule J) α m x) =
      E J α m (Phi J hNil H hHG hGH x) := by
  have h : (Phi J hNil H hHG hGH).comp (E (canonicalModule J) α m) =
      (E J α m).comp (Phi J hNil H hHG hGH) := by
    apply DirectSum.linearMap_ext
    intro c
    apply LinearMap.ext
    intro y
    change Phi J hNil H hHG hGH
      (mode (canonicalModule J) (groundState D α) m
        (DirectSum.lof ℂ (Discriminant D) (Sector J) c y)) = _
    simp only [LinearMap.comp_apply, canonicalModule, directSumModule_mode, DirectSum.lmap_lof,
      tensorModule_mode, mode, Phi, DirectSum.toModule_lof]
    exact sectorPhi_exponential J hNil H hHG hGH (representative D c) α m y
  exact LinearMap.congr_fun h x

variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

include hD in
/-- The nontrivial generator computations above feed the existing allstate
iterate/generation theorem. Every original state and integer mode is retained. -/
theorem Phi_all_modes (a : Carrier D) (m : ℤ) (x : Model J) :
    Phi J hNil H hHG hGH (mode (canonicalModule J) a m x) =
      mode J a m (Phi J hNil H hHG hGH x) := by
  exact all_modes_of_generators (canonicalModule J) J (Phi J hNil H hHG hGH) hD
    (Phi_current J hNil H hHG hGH)
    (Phi_exponential J hNil H hHG hGH) a m x

/-- The opposite direction follows from the proved actual two-sided inverse. -/
theorem Psi_all_modes (a : Carrier D) (m : ℤ) (v : M) :
    Psi J hNil H hHG hGH hD (mode J a m v) =
      mode (canonicalModule J) a m (Psi J hNil H hHG hGH hD v) := by
  apply (coordinateEquiv J hNil H hHG hGH hD).injective
  change Phi J hNil H hHG hGH (Psi J hNil H hHG hGH hD (mode J a m v)) =
    Phi J hNil H hHG hGH (mode (canonicalModule J) a m (Psi J hNil H hHG hGH hD v))
  rw [Phi_Psi, Phi_all_modes J hNil H hHG hGH hD, Phi_Psi]

/-- Discharge local nilpotence using the supplied theorem about the ORIGINAL
weak module, with no conformal grading or nonzero-module assumption. -/
def originalNilpotence : OriginalPositiveNilpotence J := by
  intro i r v
  obtain ⟨N, hN, hv⟩ :=
    FullJacobiPositiveCurrentNilpotence.positive_current_locally_nilpotent
      J hD i ((r : ℤ)+1) (by omega) v
  exact ⟨N,hv⟩

def inverseGram : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  Classical.choose (LatticePositiveEnergy.complex_inverse_exists D hD)

private theorem inverseGram_left : inverseGram hD * gramComplex D = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).1

private theorem inverseGram_right : gramComplex D * inverseGram hD = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).2

/-- Actual canonical forward map plus the explicit finite Taylor/weight
inverse. Its entire telescope is originalJ and original positivity only. -/
def classificationEquiv : Model J ≃ₗ[ℂ] M :=
  coordinateEquiv J (originalNilpotence J hD) (inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) hD

/-- Full original weak-module classification endpoint, as a SOURCE CANDIDATE.
No additional nilpotence, inverse Gram, field, spectrum or S-law input. -/
theorem classification (a : Carrier D) (m : ℤ) (x : Model J) :
    classificationEquiv J hD (mode (canonicalModule J) a m x) =
      mode J a m (classificationEquiv J hD x) := by
  exact Phi_all_modes J (originalNilpotence J hD) (inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) hD a m x

theorem classification_inverse (a : Carrier D) (m : ℤ) (v : M) :
    (classificationEquiv J hD).symm (mode J a m v) =
      mode (canonicalModule J) a m ((classificationEquiv J hD).symm v) := by
  exact Psi_all_modes J (originalNilpotence J hD) (inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) hD a m v

/-- Literal forward normalization, including arbitrary polynomials and charges. -/
theorem classification_on_single (c : Discriminant D) (n : Charge D)
    (P : Oscillator D) (w : Multiplicity J c) :
    classificationEquiv J hD
      (DirectSum.lof ℂ (Discriminant D) (Sector J) c (Finsupp.single n P ⊗ₜ[ℂ] w)) =
      polynomialOperator J (originalNilpotence J hD) (inverseGram hD) (inverseGram_left hD) P
        (S J (originalNilpotence J hD) (inverseGram hD)
          (inverseGram_left hD) (inverseGram_right hD) n (representative D c) w.val : M) := by
  exact Phi_single J (originalNilpotence J hD) (inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) c n P w

/-- This is the actual normalized [0]1 inclusion, not a chosen basis of M. -/
theorem classification_normalization (c : Discriminant D) (w : Multiplicity J c) :
    classificationEquiv J hD
      (DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w)) = (w.val : M) := by
  rw [classification_on_single, polynomialOperator_one, S_zero]
  rfl

/-- A fully displayed vectorwise finite inverse. The first support consists
of actual Taylor coefficients; each second support belongs to one actual
ground vector. Zero coefficients and empty supports require no exceptions. -/
theorem classification_inverse_explicit (v : M) :
    let hN := originalNilpotence J hD
    let H := inverseGram hD
    let hL := inverseGram_left hD
    let hR := inverseGram_right hD
    let T := W J hN H hL
    let ω := fun d => vacuumToOmega J hN H hL hR (T.coefficient d v)
    (classificationEquiv J hD).symm v =
      ∑ d ∈ (T.coefficients v).support,
        ∑ b ∈ (jointDecomposition J hN hD (ω d)).support,
          DirectSum.lof ℂ (Discriminant D) (Sector J) (weightIndex hD b).1
            (Finsupp.single (weightIndex hD b).2 (MvPolynomial.monomial d 1) ⊗ₜ[ℂ]
              returnWeight J hN H hL hR hD b ((jointDecomposition J hN hD (ω d)) b)) := by
  dsimp only
  rw [show (classificationEquiv J hD).symm v =
    Psi J (originalNilpotence J hD) (inverseGram hD)
      (inverseGram_left hD) (inverseGram_right hD) hD v from rfl, Psi_expansion]
  apply Finset.sum_congr rfl
  intro d hd
  exact coefficientLift_expansion J (originalNilpotence J hD) (inverseGram hD)
    (inverseGram_left hD) (inverseGram_right hD) hD d _

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
