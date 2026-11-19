/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldCrossedChannel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldCrossedChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual odd untwisted field gives crossed Jacobi and nonzero Leech twisted modes. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockParityT
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import Batteries.Tactic.OpenPrivate

/-! The original odd untwisted field interchanges the two sign eigenspaces
of the original twisted carrier. Its signed coefficient identity uses
the fixed algebra action on both eigenspaces. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped VertexOperator TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldCrossedChannel

open LatticeGeneratingFieldLocality (Carrier LatticeData)
open LatticeInvolution (FixedCarrier mem_eigenspace mem_fixedSpace minusSpace theta)
open LatticeAllStateReconstruction (mu)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockPhysicalRescaling (physicalSlice physicalSlice_mode)
open LatticeHalfFockParityT (actualParity)
open HalfFock.LatticeHalfFockParityField (correctedField_target_parity paritySpace)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open OriginalOrbifoldConformal (conformalVector)
open OriginalOrbifoldSectorModules (fixedParityY oddY oddY_ncoeff_val)
open StateFieldResidueReconstruction (epsilon integerBinomial)

private theorem odd_eigen (D : LatticeData) (a : minusSpace D) :
    theta D a.val = (-1 : ℂ) • a.val :=
  (mem_eigenspace D (-1) a.val).mp a.property

private theorem crossed_closed (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) (e : ℤ) (x : paritySpace D hu s) :
    (correctedField D hu a.val).coeff e x.val ∈ paritySpace D hu (-s) := by
  have hx := x.property
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  rw [correctedField_target_parity, odd_eigen, hx]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_smul, mul_neg, mul_one]

private def crossedSlice (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) :
    HVertexOperator ℤ ℂ (paritySpace D hu s) (paritySpace D hu (-s)) :=
  HVertexOperator.of_coeff
    (fun e => (((physicalSlice D hu (correctedField D hu a.val) 1).coeff e).comp
      (paritySpace D hu s).subtype).codRestrict (paritySpace D hu (-s))
        (fun x => crossed_closed D hu s a (2 * e - 1) x)) (by
    intro x
    apply ((physicalSlice D hu (correctedField D hu a.val) 1).isPWO_support_coeff x.val).mono
    intro e he hz
    apply he
    apply Subtype.ext
    exact hz)

private theorem crossedSlice_coeff_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) (e : ℤ) (x : paritySpace D hu s) :
    ((crossedSlice D hu s a).coeff e x).val =
      (correctedField D hu a.val).coeff (2 * e - 1) x.val := rfl

/-- The shift-one physical slice of the original odd field, with both
twisted sign eigenspaces as its actual domain and codomain. -/
def crossedY (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ) :
    minusSpace D →ₗ[ℂ] HVertexOperator ℤ ℂ (paritySpace D hu s) (paritySpace D hu (-s)) where
  toFun := crossedSlice D hu s
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro x
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    apply Subtype.ext
    simp only [crossedSlice_coeff_val, Submodule.coe_add, map_add, Pi.add_apply,
      LinearMap.add_apply]
  map_smul' z a := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro x
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
    apply Subtype.ext
    simp only [crossedSlice_coeff_val, Submodule.coe_smul, map_smul, Pi.smul_apply,
      LinearMap.smul_apply]

/-- The integer label `n` on the shift-one slice is the physical mode
`n + 1/2`, at doubled exponent `-2*n-3`. -/
def crossedMode (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) (n : ℤ) :
    paritySpace D hu s →ₗ[ℂ] paritySpace D hu (-s) :=
  (crossedY D hu s a).coeff (-n - 1)

@[simp] theorem crossedMode_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) (n : ℤ) (x : paritySpace D hu s) :
    (crossedMode D hu s a n x).val =
      (correctedField D hu a.val).coeff (-2*n-3) x.val := by
  change ((crossedSlice D hu s a).coeff (-n-1) x).val = _
  rw [crossedSlice_coeff_val, show 2*(-n-1)-1 = -2*n-3 by omega]

private theorem fixedMode_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (n : ℤ) (x : paritySpace D hu s) :
    (((fixedParityY D hu s a)[[n]]) x).val =
      (correctedField D hu a.val).coeff (-2*n-2) x.val := by
  change (correctedField D hu a.val).coeff (2*(-n-1)) x.val = _
  rw [show 2*(-n-1) = -2*n-2 by omega]

private theorem finite_of_coe {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} (f : ℕ → S)
    (hf : Function.HasFiniteSupport (fun i => (f i).val)) :
    Function.HasFiniteSupport f :=
  hf.subset fun _ hi hz => hi (Subtype.ext hz)

private theorem finsum_val {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} (f : ℕ → S) :
    (∑ᶠ i, f i).val = ∑ᶠ i, (f i).val :=
  S.subtype.toAddMonoidHom.map_finsum_of_injective Subtype.val_injective f

/-- Signed coefficient Jacobi for a fixed first source and an odd second
source. The iterate and both orders land in the opposite twisted eigenspace. -/
theorem crossed_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (b : minusSpace D)
    (u : paritySpace D hu s) (p q r : ℤ) :
    let left := fun i : ℕ => integerBinomial p i •
      crossedMode D hu s (((oddY D a)[[r+i]]) b) (p+q-i) u
    let first := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      ((fixedParityY D hu (-s) a)[[p+r-i]]) (crossedMode D hu s b (q+i) u)
    let second := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      (epsilon r • crossedMode D hu s b (q+r-i) (((fixedParityY D hu s a)[[p+i]]) u))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ i : ℕ, left i) = (∑ᶠ i : ℕ, first i) - (∑ᶠ i : ℕ, second i) := by
  have eigen : theta D a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace D a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu a.val 0 eigen b.val 1
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have binom (n : ℤ) (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  have h := native p q r u.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at h
  simp only [physicalSlice_mode, Int.cast_zero, zero_div, add_zero, zero_add, sub_zero,
    ← binom, show ∀ n : ℤ, -2*n-1-2 = -2*n-3 by intro n; omega] at h
  dsimp only
  refine ⟨finite_of_coe _ ?_, finite_of_coe _ ?_, finite_of_coe _ ?_, ?_⟩
  · simpa only [Submodule.coe_smul, crossedMode_val, oddY_ncoeff_val, mu] using h.1
  · simpa only [Submodule.coe_smul, fixedMode_val, crossedMode_val] using h.2.1
  · simpa only [Submodule.coe_smul, fixedMode_val, crossedMode_val, epsilon] using h.2.2.1
  · apply Subtype.ext
    simpa only [finsum_val, Submodule.coe_sub, Submodule.coe_smul, crossedMode_val,
      fixedMode_val, oddY_ncoeff_val, mu, epsilon] using h.2.2.2

/-- The odd-sector zero mode of the fixed conformal vector is the literal
`L(-1)` and acts by the original lattice translation. -/
theorem odd_conformal_mode_zero_val (D : LatticeData) (hu : IsUnit D.G.det)
    (a : minusSpace D) :
    (((oddY D (conformalVector D hu).1)[[0]]) a).val =
      LatticeSugawaraConformal.translation D a.val := by
  rw [oddY_ncoeff_val]
  have h := LatticeActualConformalState.omega_modes D (actualInverse D) (-1)
  change ((LatticeAllStateField.Y D (conformalVector D hu).1.val)[[0]]) = _ at h
  rw [h, LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D _
    (actualInverse_left D hu) (actualInverse_right D hu)]

/-- Original lattice translation preserves the odd untwisted source. -/
theorem odd_translation_mem_minusSpace (D : LatticeData) (hu : IsUnit D.G.det)
    (a : minusSpace D) : LatticeSugawaraConformal.translation D a.val ∈ minusSpace D := by
  rw [← odd_conformal_mode_zero_val D hu a]
  exact (((oddY D (conformalVector D hu).1)[[0]]) a).property

/-- The derivative of the actual crossed field at physical mode `n + 1/2`.
The same identity acts from either twisted sign to its opposite sign. -/
theorem crossedMode_L_minus_one (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : minusSpace D) (n : ℤ) :
    crossedMode D hu s (((oddY D (conformalVector D hu).1)[[0]]) a) n =
      -((n : ℂ) + 1 / 2) • crossedMode D hu s a (n - 1) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.smul_apply, Submodule.coe_smul, crossedMode_val,
    odd_conformal_mode_zero_val]
  rw [LatticeHalfFockOriginalTranslation.correctedField_translation_physical,
    show (-2 * n - 3 + 2 : ℤ) = -2 * (n - 1) - 3 by omega]
  have factor : ((-2 * (n - 1) - 3 : ℤ) : ℂ) / 2 = -((n : ℂ) + 1 / 2) := by
    push_cast
    ring
  rw [factor]

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeAllStateField (vacuum)
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeHalfFock (tensorCurrent tensorEnd current frequency)
open LatticeHalfFockChargedCoefficients (omega)
open LatticeHalfFockChargedTensorCoefficients (groundRank)
open LatticeHalfFockGradedTrace
open LatticeTwistedGroundRealization (Half)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open private current_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

local notation "D" => leechData

private theorem leechUnit : IsUnit leechData.G.det := leech_spec.2.1

/-- The actual untwisted neutral current of colour `i` belongs to the odd sector. -/
def neutralCurrent (i : Fin leechData.rank) : minusSpace D :=
  ⟨neutralMode D i (-1) (vacuum D), by
    rw [minusSpace, mem_eigenspace, LatticeInvolution.theta_neutralMode,
      LatticeInvolution.theta_vacuum, neg_one_smul]⟩

private def groundIndex : OddFiber D 0 × Half (groundRank D leechUnit) :=
  (⟨0, by simp [oddWeight]⟩, 0)

private def oneParticleIndex (i : Fin leechData.rank) :
    OddFiber D 1 × Half (groundRank D leechUnit) :=
  (⟨Finsupp.single (i, 0) 1, by simp [oddWeight, Finsupp.weight_single, omega]⟩, 0)

private theorem basis_parity (N : ℕ) (j : OddFiber D N × Half (groundRank D leechUnit)) :
    actualGradeVector D leechUnit N j ∈ paritySpace D leechUnit ((-1 : ℂ)^N) := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact actualParity_on_actualGrade D leechUnit N
    ⟨actualGradeVector D leechUnit N j, actualGradeVector_mem D leechUnit N j⟩

/-- Oscillator vacuum tensored with the ground basis vector at the zero label. -/
def groundState : paritySpace D leechUnit 1 :=
  ⟨actualGradeVector D leechUnit 0 groundIndex, by
    simpa only [pow_zero] using basis_parity 0 groundIndex⟩

/-- One oscillator of colour `i` at energy `1/2` on the same ground vector. -/
def oneParticleState (i : Fin leechData.rank) : paritySpace D leechUnit (-1) :=
  ⟨actualGradeVector D leechUnit 1 (oneParticleIndex i), by
    simpa only [pow_one] using basis_parity 1 (oneParticleIndex i)⟩

private def groundCoordinate : ActualGround D leechUnit :=
  Pi.single (0 : Half (groundRank D leechUnit)) 1

private theorem groundState_val :
    groundState.val = (1 : LatticeGeneratingFieldLocality.Oscillator D) ⊗ₜ[ℂ] groundCoordinate := by
  change actualAmbientBasis D leechUnit (0, 0) = _
  simp only [actual_basis_apply, MvPolynomial.monomial_zero', map_one, groundCoordinate]

private theorem oneParticleState_val (i : Fin leechData.rank) :
    (oneParticleState i).val = MvPolynomial.X (i, 0) ⊗ₜ[ℂ] groundCoordinate := by
  change actualAmbientBasis D leechUnit (Finsupp.single (i, 0) 1, 0) = _
  simp only [actual_basis_apply, ← MvPolynomial.X_pow_eq_monomial, pow_one, groundCoordinate]

private theorem basis_energy (N : ℕ) (j : OddFiber D N × Half (groundRank D leechUnit)) :
    actualTensorL0 D leechUnit (actualGradeVector D leechUnit N j) =
      ((3 : ℂ) / 2 + (N : ℂ) / 2) • actualGradeVector D leechUnit N j := by
  unfold actualGradeVector
  rw [actual_basis_eigenvalue, j.1.2, leech_spec.1]
  norm_num

private theorem neutralCurrent_mode_val (s : ℂ) (i : Fin leechData.rank) (n : ℤ)
    (x : paritySpace D leechUnit s) :
    (crossedMode D leechUnit s (neutralCurrent i) n x).val =
      tensorCurrent D (ActualGround D leechUnit) i n x.val := by
  rw [crossedMode_val]
  exact current_coeff D leechUnit i n x.val

/-- At the physical modes `-1/2` and `+1/2`, the actual odd neutral
current sends the ground vector to the one-particle vector and sends that
one-particle vector back with coefficient `Gᵢᵢ / 2`. Both values are nonzero. -/
theorem leech_neutralCurrent_channels (i : Fin leechData.rank) :
    let g := groundState
    let w := oneParticleState i
    let a := neutralCurrent i
    let created := crossedMode D leechUnit 1 a (-1) g
    let annihilated := crossedMode D leechUnit (-1) a 0 w
    actualTensorL0 D leechUnit g.val = (3 / 2 : ℂ) • g.val ∧
    actualTensorL0 D leechUnit w.val = (2 : ℂ) • w.val ∧
    created = w ∧ created ≠ 0 ∧
    annihilated.val = ((leechData.G i i : ℂ) / 2) • g.val ∧ annihilated ≠ 0 := by
  dsimp only
  have hg : groundState.val ≠ 0 := (actualAmbientBasis D leechUnit).ne_zero (0, 0)
  have hw : (oneParticleState i).val ≠ 0 :=
    (actualAmbientBasis D leechUnit).ne_zero (Finsupp.single (i, 0) 1, 0)
  have hdiag : (0 : ℝ) < (leechData.G i i : ℝ) := leech_spec.2.2.1.diag_pos
  have hgram : (leechData.G i i : ℂ) ≠ 0 := by
    have hne : leechData.G i i ≠ 0 := by exact_mod_cast hdiag.ne'
    exact_mod_cast hne
  have hcreate : crossedMode D leechUnit 1 (neutralCurrent i) (-1) groundState =
      oneParticleState i := by
    apply Subtype.ext
    rw [neutralCurrent_mode_val, groundState_val, oneParticleState_val]
    have negative : (-1 : ℤ) < 0 := by decide
    have index : (-(-1 : ℤ) - 1).toNat = 0 := by decide
    simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
      current, negative, ite_true, index, LinearMap.mulLeft_apply, mul_one]
  have hannihilate :
      (crossedMode D leechUnit (-1) (neutralCurrent i) 0 (oneParticleState i)).val =
        ((leechData.G i i : ℂ) / 2) • groundState.val := by
    rw [neutralCurrent_mode_val, oneParticleState_val, groundState_val]
    simp only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
      current, lt_irrefl, ite_false, Int.toNat_zero, LinearMap.smul_apply,
      LatticeActualAnnihilation.annihilate_X, ite_true, smul_smul,
      TensorProduct.smul_tmul', frequency, Int.cast_zero, zero_add]
    rw [div_mul_eq_mul_div, one_mul]
  refine ⟨?_, ?_, hcreate, ?_, hannihilate, ?_⟩
  · simpa only [groundState, Nat.cast_zero, zero_div, add_zero]
      using basis_energy 0 groundIndex
  · simpa only [oneParticleState, Nat.cast_one, show (3 : ℂ) / 2 + 1 / 2 = 2 by norm_num]
      using basis_energy 1 (oneParticleIndex i)
  · rw [hcreate]
    exact fun hz => hw (congrArg Subtype.val hz)
  · intro hz
    have hzero := congrArg Subtype.val hz
    rw [hannihilate, Submodule.coe_zero] at hzero
    exact (smul_ne_zero (div_ne_zero hgram (by norm_num)) hg) hzero

#print axioms crossedY
#print axioms crossedMode_val
#print axioms crossed_borcherds
#print axioms odd_conformal_mode_zero_val
#print axioms odd_translation_mem_minusSpace
#print axioms crossedMode_L_minus_one
#print axioms leech_neutralCurrent_channels

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldCrossedChannel
