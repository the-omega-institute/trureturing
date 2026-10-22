/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeL1
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeL1
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native corrected-field BPZ transposition with the actual ordinary Sugawara mode. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Leech
import D5.S3.VertexAlgebra.LatticeOppositeCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockAllStateField LatticeHalfFockChargedTensorCoefficients
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open TwistedGround.NativeOrbit TwistedGround.NativeSymmetricForm
open scoped BigOperators TensorProduct

noncomputable section

private abbrev ordinaryOne : Module.End ℂ (Carrier data) :=
  LatticeSugawaraCurrents.sugawaraMode data
    LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.inverse 1

private def sourceLoweringVariable (charge : Charge data) : Index data → Oscillator data
  | (axis, 0) => MvPolynomial.C (bilinear data (unitCharge data axis) charge : ℂ)
  | (axis, order + 1) => (order + 2 : ℂ) • MvPolynomial.X (axis, order)

private def sourceLowering (charge : Charge data) :
    Derivation ℂ (Oscillator data) (Oscillator data) :=
  MvPolynomial.mkDerivation ℂ (sourceLoweringVariable charge)

private theorem negative_current_single (axis : Fin data.rank) (order : ℕ)
    (charge : Charge data) (polynomial : Oscillator data) :
    LatticeFiniteNegativeGeneration.neutralMode data axis (-(order : ℤ) - 1)
      (Finsupp.single charge polynomial) =
        Finsupp.single charge (polynomial * MvPolynomial.X (axis, order)) := by
  rw [LatticeSugawaraCurrents.neutralMode_single,
    LatticeSugawaraCurrents.neutralPolynomialMode_negative]
  simp only [LinearMap.mulLeft_apply, mul_comm]

private theorem ordinary_one_sector (charge : Charge data) (polynomial : Oscillator data) :
    ordinaryOne (Finsupp.single charge polynomial) =
      Finsupp.single charge (sourceLowering charge polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    have ground := LatticeSugawaraVirasoro.sugawaraMode_ground_positive data
      LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.inverse charge 1 (by omega)
    rw [show MvPolynomial.C scalar = scalar • (1 : Oscillator data) by simp [MvPolynomial.smul_eq_C_mul],
      ← Finsupp.smul_single, map_smul, ground, smul_zero]
    simp [sourceLowering]
  | add first second firstProof secondProof =>
    simp only [Finsupp.single_add, map_add, firstProof, secondProof]
  | mul_X polynomial index ih =>
    rcases index with ⟨axis, order⟩
    have commute := congrArg (fun operator : Module.End ℂ (Carrier data) =>
      operator (Finsupp.single charge polynomial))
        (LatticeSugawaraCurrents.sugawaraMode_current_commutator data
          LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.inverse
          LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.leftInverse
          LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.rightInverse
          axis 1 (-(order : ℤ) - 1))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, negative_current_single,
      ih, LinearMap.smul_apply] at commute
    rw [sub_eq_iff_eq_add] at commute
    rw [commute, Derivation.leibniz]
    simp only [sourceLowering, MvPolynomial.mkDerivation_X, smul_eq_mul]
    cases order with
    | zero =>
      norm_num only [Nat.cast_zero, neg_zero, zero_sub, Int.cast_neg, Int.cast_one,
        neg_neg, add_neg_cancel, one_smul] at commute ⊢
      rw [LatticeSugawaraVirasoro.neutralMode_zero_single]
      simp only [LatticeSugawaraVirasoro.chargeScalar, sourceLoweringVariable,
        Finsupp.smul_single, MvPolynomial.smul_eq_C_mul, ← Finsupp.single_add]
      congr 1
      ring
    | succ order =>
      rw [show (1 : ℤ) + (-(↑(order + 1) : ℤ) - 1) = -(order : ℤ) - 1 by omega,
        negative_current_single]
      simp only [sourceLoweringVariable, Finsupp.smul_single, ← Finsupp.single_add,
        MvPolynomial.smul_eq_C_mul]
      congr 1
      push_cast
      ring

private def sourceEndpoint (charge : Charge data) (axis : Fin data.rank) : ℕ → Oscillator data
  | 0 => MvPolynomial.C (bilinear data (unitCharge data axis) charge : ℂ)
  | frequency + 1 => MvPolynomial.X (axis, frequency)

private def sourceFlowJet (charge : Charge data) (index : Index data) :
    Polynomial (Oscillator data) :=
  ∑ selection : Fin (index.2 + 2), Polynomial.monomial (index.2 + 1 - selection.val)
    (((index.2 + 1).choose selection.val : ℂ) • sourceEndpoint charge index.1 selection.val)

private def sourceFlow (charge : Charge data) :
    Oscillator data →ₐ[ℂ] Polynomial (Oscillator data) :=
  MvPolynomial.aeval (sourceFlowJet charge)

private theorem sourceFlowJet_coeff (charge : Charge data) (index : Index data) (power : ℕ) :
    (sourceFlowJet charge index).coeff power =
      if power ≤ index.2 + 1 then
        (((index.2 + 1).choose power : ℂ) •
          sourceEndpoint charge index.1 (index.2 + 1 - power)) else 0 := by
  classical
  unfold sourceFlowJet
  rw [Polynomial.finset_sum_coeff]
  by_cases within : power ≤ index.2 + 1
  · rw [if_pos within]
    let selected : Fin (index.2 + 2) := ⟨index.2 + 1 - power, by omega⟩
    rw [Finset.sum_eq_single selected]
    · rw [Polynomial.coeff_monomial, if_pos (by dsimp [selected]; omega)]
      dsimp only [selected]
      rw [← Nat.choose_symm within]
    · intro other _ different
      rw [Polynomial.coeff_monomial, if_neg]
      intro equal
      apply different
      apply Fin.ext
      dsimp [selected]
      have := other.isLt
      omega
    · simp
  · rw [if_neg within]
    apply Finset.sum_eq_zero
    intro selection _
    rw [Polynomial.coeff_monomial, if_neg]
    omega

private theorem sourceFlowJet_derivative (charge : Charge data) (index : Index data) :
    Polynomial.derivative (sourceFlowJet charge index) =
      sourceFlow charge (sourceLoweringVariable charge index) := by
  rcases index with ⟨axis, order⟩
  cases order with
  | zero =>
    apply Polynomial.ext
    intro power
    simp only [Polynomial.coeff_derivative, sourceFlowJet_coeff,
      sourceLoweringVariable, sourceFlow, MvPolynomial.aeval_C,
      Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]
    cases power <;> simp [sourceEndpoint]
  | succ order =>
    apply Polynomial.ext
    intro power
    simp only [Polynomial.coeff_derivative, sourceLoweringVariable, map_smul,
      sourceFlow, MvPolynomial.aeval_X, Polynomial.coeff_smul, sourceFlowJet_coeff]
    by_cases within : power ≤ order + 1
    · rw [if_pos (by omega), if_pos within]
      have binomial := congrArg (fun value : ℕ => (value : ℂ))
        (Nat.add_one_mul_choose_eq (order + 1) power)
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at binomial
      rw [show order + 1 + 1 - (power + 1) = order + 1 - power by omega]
      rw [show (((order + 1 + 1).choose (power + 1) : ℂ) •
          sourceEndpoint charge axis (order + 1 - power)) * (power + 1) =
          (((order + 1 + 1).choose (power + 1) : ℂ) * (power + 1 : ℂ)) •
            sourceEndpoint charge axis (order + 1 - power) by
              simp [MvPolynomial.smul_eq_C_mul, map_mul, map_add]; ring]
      rw [← binomial, mul_smul]
      congr 1
      push_cast
      ring
    · rw [if_neg (by omega), if_neg within]
      simp

private theorem sourceFlow_derivative (charge : Charge data) (polynomial : Oscillator data) :
    Polynomial.derivative (sourceFlow charge polynomial) =
      sourceFlow charge (sourceLowering charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [sourceFlow, sourceLowering]
  | add first second firstProof secondProof =>
    simp only [map_add, Polynomial.derivative_add, firstProof, secondProof]
  | mul_X polynomial index ih =>
    rw [map_mul, Polynomial.derivative_mul, ih]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, sourceLowering,
      MvPolynomial.mkDerivation_X]
    rw [show sourceFlow charge (MvPolynomial.X index) = sourceFlowJet charge index by
      simp [sourceFlow], sourceFlowJet_derivative]
    ring

private theorem sourceFlow_coeff_zero (charge : Charge data) (polynomial : Oscillator data) :
    (sourceFlow charge polynomial).coeff 0 = polynomial := by
  have maps : (Polynomial.eval₂AlgHom (AlgHom.id ℂ (Oscillator data)) 0
      (fun _ => Commute.all _ _)).comp
      (sourceFlow charge) = AlgHom.id ℂ (Oscillator data) := by
    apply MvPolynomial.algHom_ext
    intro index
    simp only [AlgHom.comp_apply, AlgHom.id_apply, sourceFlow, MvPolynomial.aeval_X,
      Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_at_zero, AlgHom.id_apply, sourceFlowJet_coeff, if_pos (Nat.zero_le _),
      Nat.choose_zero_right, Nat.cast_one, one_smul, Nat.sub_zero]
    rcases index with ⟨axis, order⟩
    rfl
  have evaluated := AlgHom.congr_fun maps polynomial
  change Polynomial.eval₂ (RingHom.id (Oscillator data)) 0
    (sourceFlow charge polynomial) = polynomial at evaluated
  rw [Polynomial.eval₂_at_zero] at evaluated
  exact evaluated

private theorem ordinary_one_power_coeff (charge : Charge data) (polynomial : Oscillator data)
    (power : ℕ) :
    (ordinaryOne ^ power) (Finsupp.single charge polynomial) =
      (power.factorial : ℂ) • Finsupp.single charge ((sourceFlow charge polynomial).coeff power) := by
  induction power generalizing polynomial with
  | zero => simp [sourceFlow_coeff_zero]
  | succ power ih =>
    rw [pow_succ, Module.End.mul_apply, ordinary_one_sector, ih,
      ← sourceFlow_derivative, Polynomial.coeff_derivative, Nat.factorial_succ,
      Nat.cast_mul, mul_smul]
    simp only [Finsupp.smul_single, MvPolynomial.smul_eq_C_mul, map_mul]
    congr 1
    push_cast
    simp only [map_add, map_one, map_natCast]
    ring

private theorem ordinary_one_normalized (charge : Charge data) (polynomial : Oscillator data)
    (power : ℕ) :
    Finsupp.single charge ((sourceFlow charge polynomial).coeff power) =
      ((power.factorial : ℂ)⁻¹) •
        ((ordinaryOne ^ power) (Finsupp.single charge polynomial)) := by
  rw [ordinary_one_power_coeff, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast power.factorial_ne_zero), one_smul]

private theorem ground_reflection_phase (charge : Charge data) :
    groundReflection charge = LatticeGeneratingFieldLocality.paritySign
      (LatticePositiveEnergy.chargeEnergy data charge) • LinearMap.id := by
  have square := original_integral_square (-charge)
  rw [original_integral_sign, LatticeInvolution.bilinear_neg_neg] at square
  rw [groundReflection, ← pow_two, square]
  apply LinearMap.ext
  intro state
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.smul_apply,
      Module.End.one_apply, TensorProduct.tmul_smul, LatticePositiveEnergy.chargeEnergy]
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.smul_apply, LinearMap.id_apply,
      firstProof, secondProof, smul_add]

private theorem opposite_source_phase (charge : Charge data) (polynomial : Oscillator data)
    (exponent : ℤ) (state : NativeTensor) :
    (nativeOppositeYtw (Finsupp.single charge polynomial)).coeff exponent state =
      LatticeGeneratingFieldLocality.paritySign (LatticePositiveEnergy.chargeEnergy data charge) •
        ((Ytw data determinantUnit (Finsupp.single charge polynomial)).coeff exponent state) := by
  simp only [nativeOppositeYtw, Ytw, Finsupp.lsum_single]
  change (correctedPolynomial data determinantUnit charge polynomial).coeff exponent
    (groundReflection charge state) = _
  rw [ground_reflection_phase]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]

private theorem paritySign_nat (weight : ℕ) :
    LatticeGeneratingFieldLocality.paritySign (weight : ℤ) = (-1 : ℂ)^weight := by
  simp only [LatticeGeneratingFieldLocality.paritySign, neg_one_pow_eq_ite,
    Int.even_coe_nat]

private def sourceReadout (charge : Charge data) (exponent : ℤ) (first second : NativeTensor) :
    Oscillator data →ₗ[ℂ] ℂ where
  toFun polynomial := tensorPairing first
    ((Ytw data determinantUnit (Finsupp.single charge polynomial)).coeff exponent second)
  map_add' first second := by
    simp only [Finsupp.single_add, map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' scalar polynomial := by
    simp only [← Finsupp.smul_single, map_smul, LinearMap.smul_apply,
      Pi.smul_apply, RingHom.id_apply]

private def flowReadout (charge : Charge data) (weight exponent : ℤ)
    (first second : NativeTensor) : Polynomial (Oscillator data) →ₗ[ℂ] ℂ :=
  Polynomial.lsum (fun power =>
    sourceReadout charge (-exponent - 4 * weight + 2 * (power : ℤ)) first second)

private theorem flowReadout_monomial (charge : Charge data) (weight exponent : ℤ)
    (first second : NativeTensor) (power : ℕ) (polynomial : Oscillator data) :
    flowReadout charge weight exponent first second (Polynomial.monomial power polynomial) =
      sourceReadout charge (-exponent - 4 * weight + 2 * (power : ℤ)) first second polynomial := by
  simp [flowReadout, Polynomial.lsum]

private theorem sourceFlow_coeff_vanish (charge : Charge data) (polynomial : Oscillator data)
    (power : ℕ) (beyond : LatticeSugawaraLocalNilpotence.oscillatorBound data
      (Finsupp.single charge polynomial) < power) :
    (sourceFlow charge polynomial).coeff power = 0 := by
  have coefficient := ordinary_one_normalized charge polynomial power
  rw [LatticeSugawaraLocalNilpotence.one_pow_eq_zero data
    LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.inverse _ _ beyond, smul_zero] at coefficient
  exact Finsupp.single_eq_zero.mp coefficient

private theorem flowReadout_expansion (charge : Charge data) (polynomial : Oscillator data)
    (weight exponent : ℤ) (first second : NativeTensor) (bound : ℕ)
    (within : LatticeSugawaraLocalNilpotence.oscillatorBound data
      (Finsupp.single charge polynomial) ≤ bound) :
    flowReadout charge weight exponent first second (sourceFlow charge polynomial) =
      ∑ power ∈ Finset.range (bound + 1), ((power.factorial : ℂ)⁻¹) *
        tensorPairing first ((Ytw data determinantUnit
          ((ordinaryOne ^ power) (Finsupp.single charge polynomial))).coeff
            (-exponent - 4 * weight + 2 * (power : ℤ)) second) := by
  classical
  have support : (sourceFlow charge polynomial).support ⊆ Finset.range (bound + 1) := by
    intro power present
    rw [Polynomial.mem_support_iff] at present
    by_contra outside
    have beyond : LatticeSugawaraLocalNilpotence.oscillatorBound data
        (Finsupp.single charge polynomial) < power := by
      simp only [Finset.mem_range] at outside
      omega
    exact present (sourceFlow_coeff_vanish charge polynomial power beyond)
  change (∑ power ∈ (sourceFlow charge polynomial).support,
    sourceReadout charge _ first second ((sourceFlow charge polynomial).coeff power)) = _
  calc
    _ = ∑ power ∈ Finset.range (bound + 1),
        sourceReadout charge (-exponent - 4 * weight + 2 * (power : ℤ)) first second
          ((sourceFlow charge polynomial).coeff power) := by
      apply Finset.sum_subset support
      intro power _ outside
      rw [Polynomial.notMem_support_iff.mp outside, map_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro power _
      change tensorPairing first ((Ytw data determinantUnit
        (Finsupp.single charge ((sourceFlow charge polynomial).coeff power))).coeff _ second) = _
      rw [ordinary_one_normalized]
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

private theorem sourceFlow_word (charge : Charge data) (count : ℕ)
    (axes : Fin count → Fin data.rank) (orders : Fin count → ℕ) :
    sourceFlow charge (∏ j : Fin count, MvPolynomial.X (axes j, orders j)) =
      ∑ selection : ((j : Fin count) → Fin (orders j + 2)),
        Polynomial.monomial (∑ j : Fin count, (orders j + 1 - (selection j).val))
          ((∏ j : Fin count, ((orders j + 1).choose (selection j).val : ℂ)) •
            (∏ j : Fin count, sourceEndpoint charge (axes j) (selection j).val)) := by
  classical
  simp only [map_prod, sourceFlow, MvPolynomial.aeval_X, sourceFlowJet, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro selection _
  have product (indices : Finset (Fin count)) :
      (∏ j ∈ indices, Polynomial.monomial (orders j + 1 - (selection j).val)
        (((orders j + 1).choose (selection j).val : ℂ) •
          sourceEndpoint charge (axes j) (selection j).val)) =
      Polynomial.monomial (∑ j ∈ indices, (orders j + 1 - (selection j).val))
        (∏ j ∈ indices, (((orders j + 1).choose (selection j).val : ℂ) •
          sourceEndpoint charge (axes j) (selection j).val)) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices absent ih =>
      rw [Finset.prod_insert absent, Finset.sum_insert absent,
        Finset.prod_insert absent, ih, Polynomial.monomial_mul_monomial]
  rw [product, Finset.prod_smul]

private theorem sourceEndpoint_eq (charge : Charge data) (axis : Fin data.rank) (frequency : ℕ) :
    sourceEndpoint charge axis frequency =
      if frequency = 0 then MvPolynomial.C (bilinear data (unitCharge data axis) charge : ℂ)
      else MvPolynomial.X (axis, frequency - 1) := by
  cases frequency <;> simp [sourceEndpoint]

private theorem native_word_one (charge : Charge data) (count : ℕ)
    (axes : Fin count → Fin data.rank) (orders : Fin count → ℕ)
    (exponent : ℤ) (first second : NativeTensor) (bound : ℕ)
    (within : LatticeSugawaraLocalNilpotence.oscillatorBound data
      (Finsupp.single charge (∏ j : Fin count, MvPolynomial.X (axes j, orders j))) ≤ bound) :
    let weight : ℤ := LatticePositiveEnergy.chargeEnergy data charge +
      ((∑ j : Fin count, (orders j + 1) : ℕ) : ℤ)
    tensorPairing ((Ytw data determinantUnit (Finsupp.single charge
      (∏ j : Fin count, MvPolynomial.X (axes j, orders j)))).coeff exponent first) second =
      paritySign weight * ∑ power ∈ Finset.range (bound + 1), ((power.factorial : ℂ)⁻¹) *
        tensorPairing first ((Ytw data determinantUnit
          ((ordinaryOne ^ power) (Finsupp.single charge
            (∏ j : Fin count, MvPolynomial.X (axes j, orders j))))).coeff
              (-exponent - 4 * weight + 2 * (power : ℤ)) second) := by
  classical
  dsimp only
  let weight : ℤ := LatticePositiveEnergy.chargeEnergy data charge +
    ((∑ j : Fin count, (orders j + 1) : ℕ) : ℤ)
  rw [← flowReadout_expansion charge _ weight exponent first second bound within]
  rw [original_word_source_reflection, sourceFlow_word, map_sum]
  simp only [flowReadout_monomial, map_smul, smul_eq_mul, sourceEndpoint_eq,
    opposite_source_phase, LinearMap.smul_apply]
  have phase : (-1 : ℂ) ^ (∑ j : Fin count, (orders j + 1)) *
      paritySign (LatticePositiveEnergy.chargeEnergy data charge) = paritySign weight := by
    dsimp only [weight]
    rw [LatticeActualGeneratorLocality.paritySign_add, paritySign_nat, mul_comm]
  rw [← phase]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selection _
  have lowering : ((∑ j : Fin count, (orders j + 1 - (selection j).val) : ℕ) : ℤ) =
      ((∑ j : Fin count, (orders j + 1) : ℕ) : ℤ) -
        ∑ j : Fin count, ((selection j).val : ℤ) := by
    simp only [Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.cast_sub (by have := (selection j).isLt; omega)
  have energy := LatticePositiveEnergy.two_chargeEnergy data charge
  have exponentLaw : -exponent - 4 * weight +
      2 * ((∑ j : Fin count, (orders j + 1 - (selection j).val) : ℕ) : ℤ) =
      -2 * chargeNorm data charge - exponent -
        2 * ((∑ j : Fin count, (orders j + 1) : ℕ) : ℤ) -
        2 * ∑ j : Fin count, ((selection j).val : ℤ) := by
    rw [lowering]
    dsimp only [weight, chargeNorm] at *
    omega
  simp only [sourceReadout, LinearMap.coe_mk, AddHom.coe_mk]
  rw [exponentLaw]
  simp only [Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
  ring

private def leftReadout (exponent : ℤ) (first second : NativeTensor) : Carrier data →ₗ[ℂ] ℂ where
  toFun source := tensorPairing ((Ytw data determinantUnit source).coeff exponent first) second
  map_add' source other := by
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' scalar source := by
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

private def rightReadout (exponent : ℤ) (first second : NativeTensor) : Carrier data →ₗ[ℂ] ℂ where
  toFun source := tensorPairing first ((Ytw data determinantUnit source).coeff exponent second)
  map_add' source other := by
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' scalar source := by
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

private theorem oscillatorBound_basis (label : LatticePositiveEnergy.Label data) :
    LatticeSugawaraLocalNilpotence.oscillatorBound data
      (LatticePositiveEnergy.carrierBasis data label) =
        LatticePositiveEnergy.oscillatorEnergy label.2 := by
  unfold LatticeSugawaraLocalNilpotence.oscillatorBound
  rw [LatticePositiveEnergy.carrierCoeffEquiv_basis]
  simp

/-- Native BPZ transposition with the actual ordinary Sugawara one-mode and its intrinsic bound. -/
theorem original_native_bpz_homogeneous (source : Carrier data) (weight exponent : ℤ)
    (homogeneous : source ∈ LatticePositiveEnergy.grade data weight)
    (first second : NativeTensor) :
    tensorPairing ((Ytw data determinantUnit source).coeff exponent first) second =
      paritySign weight * ∑ power ∈ Finset.range
        (LatticeSugawaraLocalNilpotence.oscillatorBound data source + 1),
        ((power.factorial : ℂ)⁻¹) * tensorPairing first
          ((Ytw data determinantUnit
            ((LatticeSugawaraCurrents.sugawaraMode data
              LatticeHalfFockNativeSpectrum.explicitLeechSpectrum.inverse 1 ^ power) source)).coeff
                (-exponent - 4 * weight + 2 * (power : ℤ)) second) := by
  classical
  let bound := LatticeSugawaraLocalNilpotence.oscillatorBound data source
  let left := leftReadout exponent first second
  let right : Carrier data →ₗ[ℂ] ℂ := paritySign weight •
    ∑ power ∈ Finset.range (bound + 1), ((power.factorial : ℂ)⁻¹) •
      (rightReadout (-exponent - 4 * weight + 2 * (power : ℤ)) first second).comp
        (ordinaryOne ^ power)
  suffices identity : left source = right source by
    simpa only [left, right, bound, leftReadout, rightReadout,
      LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] using identity
  rw [← (LatticePositiveEnergy.carrierBasis data).linearCombination_repr source]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro label present
  congr 1
  change label ∈ (LatticePositiveEnergy.carrierCoeffEquiv data source).support at present
  have energy : LatticePositiveEnergy.energy data label = weight := by
    by_contra different
    have zero := (LatticePositiveEnergy.mem_grade_iff data weight source).mp homogeneous
      label different
    exact (Finsupp.mem_support_iff.mp present) zero
  let word := LatticeAllStateField.occurrences data label.2
  have polynomial : (∏ j : Fin word.length,
      MvPolynomial.X ((word.get j).1, (word.get j).2) : Oscillator data) =
        MvPolynomial.monomial label.2 1 := by
    rw [← List.prod_ofFn]
    change (List.ofFn ((fun index : Index data =>
      (MvPolynomial.X index : Oscillator data)) ∘ word.get)).prod = _
    rw [← List.map_ofFn, List.ofFn_get]
    exact LatticeAllStateField.occurrences_product data label.2
  have wordWeight : (∑ j : Fin word.length, ((word.get j).2 + 1)) =
      LatticePositiveEnergy.oscillatorEnergy label.2 := by
    rw [← List.sum_ofFn]
    change (List.ofFn ((fun index : Index data => index.2 + 1) ∘ word.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
    exact LatticeHalfFockCorrectionGrading.wordWeight_occurrences data label.2
  have within : LatticeSugawaraLocalNilpotence.oscillatorBound data
      (Finsupp.single label.1
        (∏ j : Fin word.length, MvPolynomial.X ((word.get j).1, (word.get j).2))) ≤ bound := by
    rw [polynomial, ← LatticePositiveEnergy.carrierBasis_apply, oscillatorBound_basis]
    exact Finset.le_sup (f := fun label : LatticePositiveEnergy.Label data =>
      LatticePositiveEnergy.oscillatorEnergy label.2) present
  have identity := native_word_one label.1 word.length
    (fun j => (word.get j).1) (fun j => (word.get j).2) exponent first second bound within
  dsimp only at identity
  rw [wordWeight, show LatticePositiveEnergy.chargeEnergy data label.1 +
    (LatticePositiveEnergy.oscillatorEnergy label.2 : ℤ) = weight from energy, polynomial] at identity
  simpa only [left, right, leftReadout, rightReadout,
    LatticePositiveEnergy.carrierBasis_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] using identity

#print axioms original_native_bpz_homogeneous

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
