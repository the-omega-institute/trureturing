import D5.S3.VertexAlgebra.TemporaryNativeTransverse24Ghost

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24

open Module LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def transverseEuler : Derivation ℂ Polynomial Polynomial :=
  MvPolynomial.mkDerivation ℂ (fun mode : Mode => (positiveFrequency mode : ℂ) • MvPolynomial.X mode)

def oscillatorLevel (powers : Exponent) : ℕ := Finsupp.weight positiveFrequency powers

theorem transverseEuler_X (mode : Mode) :
    transverseEuler (MvPolynomial.X mode) = (positiveFrequency mode : ℂ) • MvPolynomial.X mode := by
  simp [transverseEuler]

theorem transverseEuler_monomial (powers : Exponent) (scalar : ℂ) :
    transverseEuler (MvPolynomial.monomial powers scalar) =
      (oscillatorLevel powers : ℂ) • MvPolynomial.monomial powers scalar := by
  classical
  rw [transverseEuler, MvPolynomial.mkDerivation_monomial]
  have term (mode : Mode) :
      MvPolynomial.monomial (powers - Finsupp.single mode 1) (powers mode : ℂ) •
        ((positiveFrequency mode : ℂ) • MvPolynomial.X mode) =
      ((positiveFrequency mode : ℂ) * (powers mode : ℂ)) •
        (MvPolynomial.monomial powers (1 : ℂ) : Polynomial) := by
    have identity := MvPolynomial.X_mul_pderiv_monomial (i := mode) (m := powers) (r := (1 : ℂ))
    simp only [MvPolynomial.pderiv_monomial, one_mul] at identity
    change MvPolynomial.monomial (powers - Finsupp.single mode 1) (powers mode : ℂ) *
      ((positiveFrequency mode : ℂ) • MvPolynomial.X mode) = _
    rw [mul_smul_comm, mul_comm _ (MvPolynomial.X mode), identity]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp_rw [Finsupp.sum, term, ← Finset.sum_smul]
  have weight : (∑ mode ∈ powers.support, (positiveFrequency mode : ℂ) * (powers mode : ℂ)) =
      (oscillatorLevel powers : ℂ) := by
    simp only [oscillatorLevel, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul]
    apply Finset.sum_congr rfl
    intro mode member
    ring
  rw [weight, smul_comm scalar]
  simp [MvPolynomial.smul_monomial]

variable (D : LatticeData) (beta : Charge D) (frame : OriginalAdaptedFrameData D beta)

theorem oscillatorEuler_coordinate (index : Index D) :
    oscillatorEuler D (coordinate D frame.frame index) =
      (index.2 + 1 : ℂ) • coordinate D frame.frame index := by
  simp only [coordinate, map_sum, map_smul, oscillatorEuler, MvPolynomial.mkDerivation_X]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro original member
  simp only [Derivation.map_smul, MvPolynomial.mkDerivation_X]
  rw [smul_comm]

theorem matterEmbedding_X_coordinate (mode : Mode) :
    matterEmbedding D beta frame (MvPolynomial.X mode) =
      coordinate D frame.frame (rowMode D beta frame mode) := by
  simp [matterEmbedding, MvPolynomial.rename_X, coordinateSub_X]

theorem oscillatorEuler_matterEmbedding (polynomial : Polynomial) :
    oscillatorEuler D (matterEmbedding D beta frame polynomial) =
      matterEmbedding D beta frame (transverseEuler polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [matterEmbedding, coordinateSub, oscillatorEuler, transverseEuler]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial mode inductionHypothesis =>
      simp only [map_mul, Derivation.leibniz, map_add, map_smul,
        matterEmbedding_X_coordinate, oscillatorEuler_coordinate, inductionHypothesis,
        transverseEuler_X, positiveFrequency, rowMode]
      simp [smul_eq_mul, map_mul, map_smul, matterEmbedding_X_coordinate,
        transverseEuler_X, positiveFrequency, rowMode, mul_comm, mul_left_comm, mul_assoc]

theorem oscillatorLevel_native_frequency (powers : Exponent) :
    Finsupp.weight (fun index : Index D => index.2 + 1) (exponentInclusion D beta frame powers) =
      oscillatorLevel powers := by
  unfold exponentInclusion oscillatorLevel
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index_inj (rowMode_injective D beta frame)]
  rfl

def transverseEnergy : Module.End ℂ Polynomial :=
  transverseEuler.toLinearMap + (chosenH D beta - 1) • (1 : Module.End ℂ Polynomial)

theorem transverseEnergy_monomial (powers : Exponent) (scalar : ℂ) :
    transverseEnergy D beta (MvPolynomial.monomial powers scalar) =
      ((oscillatorLevel powers : ℂ) + chosenH D beta - 1) • MvPolynomial.monomial powers scalar := by
  simp only [transverseEnergy, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Derivation.coeFn_coe, transverseEuler_monomial]
  module

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)

include leftGramInverse rightGramInverse in
theorem chosenH_signed_norm : chosenH D beta = (bilinear D beta beta : ℂ) / 2 := by
  rw [chosenH_original_chargeQuadratic D H leftGramInverse rightGramInverse,
    chargeQuadratic_eq D H leftGramInverse rightGramInverse]

include leftGramInverse rightGramInverse in
theorem M0_lane (upper : Bool) (polynomial : Polynomial) :
    M D H 0 (lane D beta frame upper polynomial) =
      lane D beta frame upper (transverseEuler polynomial) +
        chosenH D beta • lane D beta frame upper polynomial := by
  simp only [lane_eq_physical]
  change M D H 0 (Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ]
    downWord (epsilonSites upper) down) = _
  simp only [M, TensorProduct.map_tmul, LinearMap.id_apply,
    sugawaraMode_zero_single D H leftGramInverse rightGramInverse, oscillatorEuler_matterEmbedding,
    ← chosenH_signed_norm D beta H leftGramInverse rightGramInverse,
    Finsupp.single_add, Finsupp.smul_single, TensorProduct.add_tmul, TensorProduct.smul_tmul]
  simp only [← Finsupp.smul_single, TensorProduct.smul_tmul']
  rfl

theorem G0_lane (upper : Bool) (polynomial : Polynomial) :
    G D 0 (lane D beta frame upper polynomial) = (-1 : ℂ) • lane D beta frame upper polynomial := by
  simp only [lane_eq_physical]
  change G D 0 (Finsupp.single beta (matterEmbedding D beta frame polynomial) ⊗ₜ[ℂ]
    downWord (epsilonSites upper) down) = _
  simp only [G, TensorProduct.map_tmul, LinearMap.id_apply, polarized_L_zero, TensorProduct.tmul_smul]
  cases upper <;>
    norm_num [epsilonSites, polarizedLevel, polarizedWeight, BcGhostLZeroSpectrum.siteWeight, physicalLane]

include leftGramInverse rightGramInverse in
theorem T0_lane (upper : Bool) (polynomial : Polynomial) :
    (M D H 0 + G D 0) (lane D beta frame upper polynomial) =
      lane D beta frame upper (transverseEnergy D beta polynomial) := by
  simp only [LinearMap.add_apply, M0_lane D beta frame H leftGramInverse rightGramInverse,
    G0_lane, transverseEnergy, map_add, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_smul, Derivation.coeFn_coe]
  module

include leftGramInverse rightGramInverse in
theorem T0_realize (pair : Polynomial × Polynomial) :
    (M D H 0 + G D 0) (realize D beta frame pair) =
      realize D beta frame (transverseEnergy D beta pair.1, transverseEnergy D beta pair.2) := by
  simp only [realize, LinearMap.coe_mk, AddHom.coe_mk, map_add,
    T0_lane D beta frame H leftGramInverse rightGramInverse]

include leftGramInverse rightGramInverse in
theorem T0_preserves (state : State D) (member : state ∈ fixedReduced D beta frame) :
    (M D H 0 + G D 0) state ∈ fixedReduced D beta frame := by
  rw [← realize_extract D beta frame state member,
    T0_realize D beta frame H leftGramInverse rightGramInverse]
  exact realize_mem D beta frame _

def reducedT0 : Module.End ℂ (fixedReduced D beta frame) :=
  ((M D H 0 + G D 0).comp (fixedReduced D beta frame).subtype).codRestrict (fixedReduced D beta frame)
    (fun state => T0_preserves D beta frame H leftGramInverse rightGramInverse state state.property)

theorem T0_transport (pair : Polynomial × Polynomial) :
    (reducedEquiv D beta frame).symm
      (reducedT0 D beta frame H leftGramInverse rightGramInverse (reducedEquiv D beta frame pair)) =
      (transverseEnergy D beta pair.1, transverseEnergy D beta pair.2) := by
  change extract D beta frame ((M D H 0 + G D 0) (realize D beta frame pair)) = _
  rw [T0_realize D beta frame H leftGramInverse rightGramInverse, extract_realize]

include leftGramInverse rightGramInverse in
theorem T0_realize_eigen_iff (energy : ℂ) (pair : Polynomial × Polynomial) :
    (M D H 0 + G D 0) (realize D beta frame pair) = energy • realize D beta frame pair ↔
      transverseEnergy D beta pair.1 = energy • pair.1 ∧
        transverseEnergy D beta pair.2 = energy • pair.2 := by
  rw [T0_realize D beta frame H leftGramInverse rightGramInverse, ← map_smul]
  constructor
  · intro equality
    have coordinates := realize_injective D beta frame equality
    exact ⟨congrArg Prod.fst coordinates, congrArg Prod.snd coordinates⟩
  · rintro ⟨lowerEquality, upperEquality⟩
    apply congrArg (realize D beta frame)
    exact Prod.ext lowerEquality upperEquality

theorem transverseEnergy_coeff (polynomial : Polynomial) (powers : Exponent) :
    MvPolynomial.coeff powers (transverseEnergy D beta polynomial) =
      ((oscillatorLevel powers : ℂ) + chosenH D beta - 1) * MvPolynomial.coeff powers polynomial := by
  classical
  have equality : (MvPolynomial.lcoeff ℂ powers).comp (transverseEnergy D beta) =
      ((oscillatorLevel powers : ℂ) + chosenH D beta - 1) • (MvPolynomial.lcoeff ℂ powers) := by
    apply (MvPolynomial.basisMonomials Mode ℂ).ext
    intro other
    change MvPolynomial.coeff powers (transverseEnergy D beta (MvPolynomial.monomial other 1)) =
      ((oscillatorLevel powers : ℂ) + chosenH D beta - 1) *
        MvPolynomial.coeff powers (MvPolynomial.monomial other 1)
    rw [transverseEnergy_monomial, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases same : other = powers
    · subst other
      rfl
    · simp [MvPolynomial.coeff_monomial, same, Ne.symm same]
  exact congrArg (fun operator : Polynomial →ₗ[ℂ] ℂ => operator polynomial) equality

def polynomialEnergySector (energy : ℂ) : Submodule ℂ Polynomial :=
  LinearMap.ker (transverseEnergy D beta - energy • (1 : Module.End ℂ Polynomial))

theorem polynomialEnergySector_mem (energy : ℂ) (polynomial : Polynomial) :
    polynomial ∈ polynomialEnergySector D beta energy ↔
      transverseEnergy D beta polynomial = energy • polynomial := by
  simp [polynomialEnergySector, LinearMap.mem_ker, sub_eq_zero]

theorem polynomialEnergySector_coefficients (energy : ℂ) (polynomial : Polynomial) :
    polynomial ∈ polynomialEnergySector D beta energy ↔
      ∀ powers : Exponent, MvPolynomial.coeff powers polynomial ≠ 0 →
        (oscillatorLevel powers : ℂ) + chosenH D beta - 1 = energy := by
  rw [polynomialEnergySector_mem]
  constructor
  · intro homogeneous powers nonzero
    have equality := congrArg (MvPolynomial.coeff powers) homogeneous
    rw [transverseEnergy_coeff, MvPolynomial.coeff_smul, smul_eq_mul] at equality
    exact mul_right_cancel₀ nonzero equality
  · intro supported
    apply MvPolynomial.ext
    intro powers
    rw [transverseEnergy_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases zero : MvPolynomial.coeff powers polynomial = 0
    · simp [zero]
    · rw [supported powers zero]

theorem zeroT0_coefficients (polynomial : Polynomial) :
    polynomial ∈ polynomialEnergySector D beta 0 ↔
      ∀ powers : Exponent, MvPolynomial.coeff powers polynomial ≠ 0 →
        (oscillatorLevel powers : ℂ) = 1 - chosenH D beta := by
  rw [polynomialEnergySector_coefficients]
  apply forall_congr'
  intro powers
  apply imp_congr_right
  intro nonzero
  constructor <;> intro equality <;> linear_combination equality

theorem zeroT0_nonzero_level_matching (polynomial : Polynomial) (nonzero : polynomial ≠ 0)
    (onShell : polynomial ∈ polynomialEnergySector D beta 0) :
    ∃ level : ℕ, (level : ℂ) = 1 - chosenH D beta := by
  have nonzeroCoefficient : ∃ powers : Exponent, MvPolynomial.coeff powers polynomial ≠ 0 := by
    by_contra noCoefficient
    push_neg at noCoefficient
    apply nonzero
    apply MvPolynomial.ext
    intro powers
    simpa using noCoefficient powers
  obtain ⟨powers, present⟩ := nonzeroCoefficient
  exact ⟨oscillatorLevel powers, (zeroT0_coefficients D beta polynomial).mp onShell powers present⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource.NativeTransverse24
