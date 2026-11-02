/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original statewise oscillator, signed charge-coset and ground Fourier reduction. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import Mathlib.LinearAlgebra.Trace
import Batteries.Tactic.OpenPrivate

/-!
Native original oscillator and charge-coset reduction; identityK remains open.
Original operators and source inverse: commit 835f8774e5b209b01e6985b2c168054dae37c240.
Classical twisted lattice coefficient calculus; inherited supplier attributions
remain in the imported sources. No claim of a new VOA, crossing proof, Monster,
BRST, string or AdS theorem is made here.

The oscillator formula below is constructed on the original polynomial module.
Its mode sums are finite after application to each input. The tensor support
theorem is used through an explicitly split ground coordinate, rather than
through an unjustified finsum of endomorphisms.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField LatticeTwistedGroundRealization
open LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField
open LatticeTwistedGroundRealization.SignQuotient
open LatticePositiveEnergy LatticeAllStateField LatticeInvolution
open ActualChargedAdjoint SignedOscillatorWick OperatorAlgebra MixedIntertwiner
open SourceBPZ.OriginalSourcePairing SourceBPZ.OriginalSourceCoevaluation
open private selectedGroundPairing actualForm_tmul from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private selected_central from D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
open private reduced_lift coefficient_operator from D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
open private ground_pairing_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private T kernel ambientCoefficient homogeneous_coefficient liftGrade from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

def oscillatorJet (D : LatticeData) (i : Index D) (m : ℤ) :
    Module.End ℂ (Oscillator D) := jetScalar i.2 m • current D i.1 m

/-- Same recursion, order and doubled exponents as the original flatCoefficient. -/
def oscillatorFlat (D : LatticeData) (a : Charge D) :
    (w : List (Index D)) → ModeTuple D w → ℤ → Module.End ℂ (Oscillator D)
  | [], _, e => oscillatorCoefficient D a e
  | i :: w, modes, e =>
    if modes.1 < 0 then oscillatorJet D i modes.1 *
      oscillatorFlat D a w modes.2 (e + 2*modes.1 + 2*i.2 + 3)
    else oscillatorFlat D a w modes.2 (e + 2*modes.1 + 2*i.2 + 3) *
      oscillatorJet D i modes.1

private theorem flat_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (modes : ModeTuple D w)
    (e : ℤ) (x : Oscillator D) (g : ActualGround D hu) :
    flatCoefficient D hu (chargedField D hu a) w modes e (x ⊗ₜ[ℂ] g) =
      chargeScalar D a •
        (oscillatorFlat D a w modes e x ⊗ₜ[ℂ] groundAction D hu a g) := by
  induction w generalizing e x with
  | nil =>
    simp only [flatCoefficient, oscillatorFlat, chargedField, HVertexOperator.coeff_of_coeff,
      chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul]
  | cons i w ih =>
    rcases modes with ⟨m, modes⟩
    by_cases hm : m < 0
    · simp only [flatCoefficient, oscillatorFlat, if_pos hm, Module.End.mul_apply]
      rw [ih]
      simp [jetCurrent, oscillatorJet, tensorCurrent, tensorEnd,
        TensorProduct.map_tmul, TensorProduct.smul_tmul, smul_smul]
    · simp only [flatCoefficient, oscillatorFlat, if_neg hm, Module.End.mul_apply]
      rw [show jetCurrent D hu i m (x ⊗ₜ[ℂ] g) =
        oscillatorJet D i m x ⊗ₜ[ℂ] g by
          simp [jetCurrent, oscillatorJet, tensorCurrent, tensorEnd,
            TensorProduct.map_tmul, TensorProduct.smul_tmul] ]
      exact ih modes _ _

/-- A ground-coordinate projection on the actual tensor module. -/
private def oscillatorCoordinate (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu →ₗ[ℂ] Oscillator D :=
  TensorProduct.lift {
    toFun := fun x => {
      toFun := fun g => g 0 • x
      map_add' := by intro g h; simp [add_smul]
      map_smul' := by intro c g; simp [smul_smul, mul_comm] }
    map_add' := by intro x y; ext g; simp [smul_add]
    map_smul' := by intro c x; ext g; simp [smul_smul, mul_comm] }

private theorem oscillatorCoordinate_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (x : Oscillator D) (g : ActualGround D hu) :
    oscillatorCoordinate D hu (x ⊗ₜ[ℂ] g) = g 0 • x := by
  rfl

/-- The existing pointwise tensor support bound also bounds the oscillator terms.
The witness ground input is the inverse original charge action on the constant
function one. Thus its charged image has coordinate exactly one. -/
theorem oscillatorFlat_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) (x : Oscillator D) :
    Function.HasFiniteSupport (fun modes : ModeTuple D w =>
      oscillatorFlat D a w modes e x) := by
  let oneGround : ActualGround D hu := fun _ => 1
  let g := groundRepresentation D hu (groundLift D a)⁻¹ oneGround
  have hg : groundAction D hu a g = oneGround := by
    exact (groundRepresentation D hu).self_inv_apply (groundLift D a) oneGround
  have hc : chargeScalar D a ≠ 0 := zpow_ne_zero _ (by norm_num)
  apply (flatTerm_finite D hu (chargedField D hu a) w e (x ⊗ₜ[ℂ] g)).subset
  intro modes hm hz
  apply hm
  have projected := congrArg (oscillatorCoordinate D hu) hz
  change oscillatorCoordinate D hu
    (flatCoefficient D hu (chargedField D hu a) w modes e (x ⊗ₜ[ℂ] g)) = _ at projected
  rw [flat_tmul, map_smul, hg, oscillatorCoordinate_tmul] at projected
  have killed : chargeScalar D a • oscillatorFlat D a w modes e x = 0 := by
    simpa [oneGround] using projected
  exact (smul_eq_zero.mp killed).resolve_left hc

/-- A statewise sum, never an infinite sum in Module.End. -/
def oscillatorWord (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ) : Module.End ℂ (Oscillator D) where
  toFun x := ∑ᶠ modes : ModeTuple D w, oscillatorFlat D a w modes e x
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib (oscillatorFlat_finite D hu a w e x)
      (oscillatorFlat_finite D hu a w e y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (oscillatorFlat_finite D hu a w e x)).symm

private theorem word_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w : List (Index D)) (e : ℤ)
    (x : Oscillator D) (g : ActualGround D hu) :
    (wordField D hu (chargedField D hu a) w).coeff e (x ⊗ₜ[ℂ] g) =
      chargeScalar D a •
        (oscillatorWord D hu a w e x ⊗ₜ[ℂ] groundAction D hu a g) := by
  rw [wordField_coefficient]
  simp only [flatTerm, flat_tmul]
  rw [← smul_finsum' _ ((oscillatorFlat_finite D hu a w e x).subset
    (by intro modes hm hz; exact hm (by change oscillatorFlat D a w modes e x ⊗ₜ[ℂ] _ = 0; simp only [show oscillatorFlat D a w modes e x = 0 from hz, TensorProduct.zero_tmul])))]
  congr 1
  exact (map_finsum ((TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip
    (groundAction D hu a g)) (oscillatorFlat_finite D hu a w e x)).symm

def oscillatorNormal (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) : Oscillator D →ₗ[ℂ] Module.End ℂ (Oscillator D) :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun beta => oscillatorWord D hu a
      (LatticeHalfFockFockNormalField.occurrences D beta) e)

private theorem normal_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (p x : Oscillator D) (g : ActualGround D hu) :
    (polynomialField D hu a p).coeff e (x ⊗ₜ[ℂ] g) =
      chargeScalar D a •
        (oscillatorNormal D hu a e p x ⊗ₜ[ℂ] groundAction D hu a g) := by
  let ev : Module.End ℂ (Oscillator D) →ₗ[ℂ] Oscillator D := {
    toFun := fun A => A x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let lhs := (coefficientAt D hu e (x ⊗ₜ[ℂ] g)).comp (polynomialField D hu a)
  let rhs := chargeScalar D a •
    (((TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu)).flip
      (groundAction D hu a g)).comp (ev.comp (oscillatorNormal D hu a e)))
  have equality : lhs = rhs := by
    apply (MvPolynomial.basisMonomials (Index D) ℂ).ext
    intro beta
    change (polynomialField D hu a (MvPolynomial.monomial beta 1)).coeff e
      (x ⊗ₜ[ℂ] g) = _
    rw [polynomialField_monomial_public]
    change _ = chargeScalar D a •
      (oscillatorNormal D hu a e ((MvPolynomial.basisMonomials (Index D) ℂ) beta) x ⊗ₜ[ℂ]
        groundAction D hu a g)
    rw [oscillatorNormal, Module.Basis.constr_basis]
    exact word_tmul D hu a (LatticeHalfFockFockNormalField.occurrences D beta) e x g
  exact LinearMap.congr_fun equality p

/-- Literal finite Corr, including charge-linear singleton terms, followed by
the original shift e + 2s and the statewise normal coefficient. -/
def oscillatorCorrected (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) : Oscillator D →ₗ[ℂ] Module.End ℂ (Oscillator D) :=
  (Finsupp.lsum ℂ (fun s : ℕ => oscillatorNormal D hu a (e + 2*(s : ℤ)))).comp
    (Corr D a)

/-- O3 on EVERY original source polynomial and EVERY actual tensor factor. -/
theorem corrected_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ)
    (x : Oscillator D) (g : ActualGround D hu) :
    (correctedField D hu (Finsupp.single a p)).coeff e (x ⊗ₜ[ℂ] g) =
      chargeScalar D a •
        (oscillatorCorrected D hu a e p x ⊗ₜ[ℂ] groundAction D hu a g) := by
  classical
  simp only [correctedField, Finsupp.lsum_single, correctedPolynomial,
    LinearMap.comp_apply]
  change coefficientAt D hu e (x ⊗ₜ[ℂ] g)
    (correctedSum D hu a (Corr D a p)) = _
  simp only [correctedSum, Finsupp.lsum_apply, Finsupp.sum, LinearMap.comp_apply,
    map_sum, oscillatorCorrected, LinearMap.sum_apply]
  rw [TensorProduct.sum_tmul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change (shiftField D hu s (polynomialField D hu a ((Corr D a p) s))).coeff e
    (x ⊗ₜ[ℂ] g) = _
  rw [shiftField_coefficient_public]
  exact normal_tmul D hu a (e + 2*(s : ℤ)) ((Corr D a p) s) x g

def oscillatorLower (D : LatticeData) : Module.End ℂ (Oscillator D) :=
  L D (HalfFockSpectralFiberSource.actualInverse D) 1

private theorem lower_power_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ n)
      (p ⊗ₜ[ℂ] g) = (oscillatorLower D ^ n) p ⊗ₜ[ℂ] g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

def quadraticSign (D : LatticeData) (a : ModTwoCharge D) : ℂ :=
  complexSign (modTwoCocycle D a a)

def fourierSign (D : LatticeData) (a b : ModTwoCharge D) : ℂ :=
  complexSign (modTwoPairing D a b)

private theorem quadraticSign_square (D : LatticeData) (a : ModTwoCharge D) :
    quadraticSign D a * quadraticSign D a = 1 := sign_square _

/-- The quadratic refinement is derived from the actual lower-triangular cocycle. -/
theorem quadraticSign_add (D : LatticeData) (a b : ModTwoCharge D) :
    quadraticSign D (a+b) =
      quadraticSign D a * quadraticSign D b * fourierSign D a b := by
  unfold quadraticSign fourierSign
  rw [← complexSign_add, ← complexSign_add]
  congr 1
  rw [← mod_two_cocycle_symmetrization]
  simp only [map_add, AddMonoidHom.add_apply]
  abel

theorem quadraticSign_integral (D : LatticeData) (a : Charge D) :
    quadraticSign D (reduceCharge D a) = paritySign (bilinear D a a / 2) := by
  unfold quadraticSign
  rw [cocycle_reduction]
  change complexSign (lowerCocycleExponent D a a : F₂) = _
  rw [complexSign_integral, integral_cocycle_square]

private theorem groundAction_reduction (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) : groundAction D hu a =
      chargeOperator D (groundRepresentation D hu) (reduceCharge D a) := by
  apply congrArg (groundRepresentation D hu)
  apply (quotientEquiv D).injective
  rw [reduced_lift]
  rfl

private theorem chargeOperator_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : ModTwoCharge D) :
    chargeOperator D (groundRepresentation D hu) a *
      chargeOperator D (groundRepresentation D hu) b =
    complexSign (modTwoCocycle D a b) •
      chargeOperator D (groundRepresentation D hu) (a+b) := by
  have lifts : chargeLift D a * chargeLift D b =
      QuotientGroup.mk (⟨modTwoCocycle D a b, 0⟩ : Extension D) * chargeLift D (a+b) := by
    apply (quotientEquiv D).injective
    simp only [map_mul, reduced_lift]
    change (⟨0, a⟩ : ReducedExtension D) * ⟨0, b⟩ =
      reduction D ⟨modTwoCocycle D a b, 0⟩ * ⟨0, a+b⟩
    ext i
    · change 0 + 0 + modTwoCocycle D a b =
        modTwoCocycle D a b + 0 + modTwoCocycle D 0 (a+b)
      simp
    · change (a+b) i = (0+(a+b)) i
      simp
  unfold chargeOperator
  rw [← map_mul, lifts, map_mul, selected_central, smul_mul_assoc, one_mul]

private theorem dualOperator_sign (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) : dualOperator D (groundRepresentation D hu) a =
      quadraticSign D a • chargeOperator D (groundRepresentation D hu) a := by
  have lifts : (chargeLift D a)⁻¹ =
      QuotientGroup.mk (⟨modTwoCocycle D a a, 0⟩ : Extension D) * chargeLift D a := by
    apply (quotientEquiv D).injective
    simp only [map_inv, map_mul, reduced_lift]
    change (⟨0, a⟩ : ReducedExtension D)⁻¹ =
      reduction D ⟨modTwoCocycle D a a, 0⟩ * ⟨0, a⟩
    ext i
    · change -0 + modTwoCocycle D a a =
        modTwoCocycle D a a + 0 + modTwoCocycle D 0 a
      simp
    · change (-a) i = (0+a) i
      simp only [Pi.neg_apply, zero_add]
      exact CharTwo.neg_eq _
  unfold dualOperator chargeOperator quadraticSign
  rw [lifts, map_mul, selected_central, smul_mul_assoc, one_mul]

private abbrev groundForm (D : LatticeData) (hu : IsUnit D.G.det) :=
  (selectedGroundPairing D hu).form

private theorem ground_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (x y : ActualGround D hu) :
    groundForm D hu (chargeOperator D (groundRepresentation D hu) a x) y =
      quadraticSign D a *
        groundForm D hu x (chargeOperator D (groundRepresentation D hu) a y) := by
  have reduction : reduceCharge D (integralLift D a) = a := by
    ext i
    simp [reduceCharge, integralLift]
  have h := (selectedGroundPairing D hu).signed_adjoint (integralLift D a) x y
  rw [groundAction_reduction, reduction, ← quadraticSign_integral, reduction] at h
  exact h

/-- G3. Consume the EXISTING operator reconstruction on the selected ground.
No second ground-duality datum or completeness premise is introduced. -/
theorem ground_completeness (D : LatticeData) (hu : IsUnit D.G.det)
    (x y z t : ActualGround D hu) :
    ∑ a : ModTwoCharge D,
      (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z) =
      groundForm D hu t x * groundForm D hu y z := by
  classical
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have central : groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) := by
    simpa [complexSign] using selected_central D hu 1
  obtain ⟨algebra⟩ := actual_operator_algebra D hu (groundRank D hu) rank_eq
    (groundRepresentation D hu) central
  let rankOne := (groundForm D hu y).smulRight x
  have coefficient (a : ModTwoCharge D) :
      traceCoefficient D (groundRepresentation D hu) a rankOne =
        (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D a *
          groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) := by
    have product : chargeOperator D (groundRepresentation D hu) a * rankOne =
        (groundForm D hu y).smulRight
          (chargeOperator D (groundRepresentation D hu) a x) := by
      ext v
      simp [rankOne, Module.End.mul_apply]
    change (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ *
      LinearMap.trace ℂ (ActualGround D hu)
        (dualOperator D (groundRepresentation D hu) a * rankOne) = _
    rw [dualOperator_sign, smul_mul_assoc, product, map_smul, LinearMap.trace_smulRight]
    simp only [smul_eq_mul]
    ring
  have expanded := congrArg (fun A : Module.End ℂ (ActualGround D hu) =>
    groundForm D hu t (A z)) (algebra.reconstruction rankOne)
  simpa [coefficient, rankOne, LinearMap.sum_apply, map_sum, map_smul,
    LinearMap.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using expanded

private theorem ground_rechannel (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (x y z t : ActualGround D hu) :
    groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
      groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z) =
    ∑ b : ModTwoCharge D,
      (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D (a+b) *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) b z) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
  classical
  have complete := ground_completeness D hu
    (chargeOperator D (groundRepresentation D hu) a z) y
    (chargeOperator D (groundRepresentation D hu) a x) t
  trans ∑ b : ModTwoCharge D,
    (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D b *
      groundForm D hu y (chargeOperator D (groundRepresentation D hu) b
        (chargeOperator D (groundRepresentation D hu) a z)) *
      groundForm D hu t (chargeOperator D (groundRepresentation D hu) b
        (chargeOperator D (groundRepresentation D hu) a x))
  · exact (mul_comm _ _).trans complete.symm
  apply Fintype.sum_equiv (Equiv.addRight a) _ _
  intro b
  have haa : a+a = 0 := by funext i; exact CharTwo.add_self_eq_zero (a i)
  have sign := sign_square (modTwoCocycle D b a)
  change _ = (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ *
    quadraticSign D (a+(b+a)) *
      groundForm D hu y (chargeOperator D (groundRepresentation D hu) (b+a) z) *
      groundForm D hu t (chargeOperator D (groundRepresentation D hu) (b+a) x)
  rw [show a+(b+a) = b by rw [add_comm b a, ← add_assoc, haa, zero_add] ]
  change _ * _ * groundForm D hu y
    ((chargeOperator D (groundRepresentation D hu) b *
      chargeOperator D (groundRepresentation D hu) a) z) * groundForm D hu t
    ((chargeOperator D (groundRepresentation D hu) b *
      chargeOperator D (groundRepresentation D hu) a) x) = _
  simp only [chargeOperator_mul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  calc
    _ = (complexSign (modTwoCocycle D b a) * complexSign (modTwoCocycle D b a)) *
        ((Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D b *
          groundForm D hu y (chargeOperator D (groundRepresentation D hu) (b+a) z) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) (b+a) x)) := by ring
    _ = _ := by rw [sign, one_mul]

/-- G4: first channel into the common (y,z;x,t) channel, with the exact character. -/
theorem ground_exchange_first (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (x y z t : ActualGround D hu) :
    groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
      groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z) =
    ∑ b : ModTwoCharge D,
      (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D a * fourierSign D a b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
  rw [ground_rechannel]
  apply Finset.sum_congr rfl
  intro b hb
  rw [quadraticSign_add,
    (ground_pairing_symmetric D hu (selectedGroundPairing D hu)).eq y
      (chargeOperator D (groundRepresentation D hu) b z), ground_adjoint]
  have hs := quadraticSign_square D b
  calc
    _ = (quadraticSign D b * quadraticSign D b) *
        ((Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D a * fourierSign D a b *
          groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)) := by ring
    _ = _ := by rw [hs, one_mul]

/-- G5: second right channel into the SAME common ground channel. -/
theorem ground_exchange_second (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (x y z t : ActualGround D hu) :
    groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
      groundForm D hu t (chargeOperator D (groundRepresentation D hu) a y) =
    ∑ b : ModTwoCharge D,
      (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D (a+b) *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
  exact ground_rechannel D hu a x z y t

/-- The oscillator part of the ACTUAL ordered homogeneous source functional.
The exponent is 2s, not -2s-2. Both original L(1) powers and factorial cutoffs
are retained literally. -/
def oscillatorKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k : ℤ) (a : Charge D) (p P Q : Oscillator D) : ℂ :=
  ∑ i ∈ Finset.range (K-1), ∑ j ∈ Finset.range (H-1),
    let s : ℤ := k+1-(i : ℤ)-2*(H : ℤ)+(j : ℤ)
    ((-1 : ℂ)^((H : ℤ)+s) / ((i.factorial : ℂ)*(j.factorial : ℂ))) *
      wick D ((oscillatorLower D ^ i) Q)
        (oscillatorCorrected D hu a (2*s) p ((oscillatorLower D ^ j) P))

private theorem kernel_single_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k : ℤ) (a : Charge D) (p P Q : Oscillator D)
    (x y : ActualGround D hu) :
    kernel D hu H K k (P ⊗ₜ[ℂ] x) (Q ⊗ₜ[ℂ] y) (Finsupp.single a p) =
      chargeScalar D a * oscillatorKernel D hu H K k a p P Q *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) (reduceCharge D a) x) := by
  classical
  simp only [kernel, oscillatorKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, CorrectedInversion.K_R, LinearMap.coe_mk, AddHom.coe_mk, T, lower_power_tmul, corrected_tmul,
    map_smul, actualForm_tmul, groundAction_reduction, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem chargeScalar_neg (D : LatticeData) (a : Charge D) :
    chargeScalar D (-a) = chargeScalar D a := by
  simp only [chargeScalar, chargeNorm, bilinear_neg_neg]

/-- O4. Every signed original energy-fiber element is present. The dual
polynomial is the EXISTING -(k+1)^(-1) G^(-1) substitution divided by all
occupation factorials. The TWO charged scalar factors are explicit. The
theta reflection is inside one, and only one, half-average. -/
def cosetKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k t : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ᶠ b : EnergyFiber D ((H : ℤ)+(K : ℤ)-k-1),
    if reduceCharge D b.val.1 = a then
      chargeScalar D b.val.1 * chargeScalar D (-b.val.1) *
        (oscillatorKernel D hu H K k b.val.1 (MvPolynomial.monomial b.val.2 1) P Q +
          oscillatorKernel D hu H K k (-b.val.1)
            (sigma D (MvPolynomial.monomial b.val.2 1)) P Q) *
        wick D S (oscillatorCorrected D hu (-b.val.1) (-2*t-2)
          (dualOscillatorMonomial D b.val.2) R)
    else 0

/-- O5 on the unchanged actual tensor inputs. Ground vectors are unrestricted;
P,Q may be any original polynomials that realize the stated actual homogeneous
inputs. R and the detector S have no homogeneity or parity restriction.
This uses the original source inverse and its full-fiber half-average. -/
theorem fourM_factorization (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k t : ℤ)
    (u v : HalfFock.LatticeHalfFockParityField.paritySpace D hu (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    fourMScalar D hu hD k t u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, cosetKernel D hu H K k t P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z) := by
  classical
  let h : ℤ := (H : ℤ)+(K : ℤ)-k-1
  letI := energyFiber_finite D hD h
  letI := Fintype.ofFinite (EnergyFiber D h)
  have contracted := (fourM_contraction D hu hD h24 H K k t u v
    (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) huH hvK).1
  rw [fourMScalar, originalI_homogeneous D hu hD h24 H K k u v huH hvK]
  change actualForm D hu (S ⊗ₜ[ℂ] d)
    ((correctedField D hu ((sourceGradePairingEquiv D hu hD h).symm
      (normalizedCoefficient D hu k u v h)).val).coeff (-2*t-2) (R ⊗ₜ[ℂ] z)) = _
  rw [contracted]
  let term : EnergyFiber D h → ℂ := fun b =>
    chargeScalar D b.val.1 * chargeScalar D (-b.val.1) *
      (oscillatorKernel D hu H K k b.val.1 (MvPolynomial.monomial b.val.2 1) P Q +
        oscillatorKernel D hu H K k (-b.val.1)
          (sigma D (MvPolynomial.monomial b.val.2 1)) P Q) *
      wick D S (oscillatorCorrected D hu (-b.val.1) (-2*t-2)
        (dualOscillatorMonomial D b.val.2) R)
  trans (2 : ℂ)⁻¹ * ∑ b : EnergyFiber D h,
    term b *
      groundForm D hu y (chargeOperator D (groundRepresentation D hu) (reduceCharge D b.val.1) x) *
      groundForm D hu d (chargeOperator D (groundRepresentation D hu) (reduceCharge D b.val.1) z)
  · congr 1
    rw [finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro b hb
    rw [huP, hvQ, carrierBasis_apply]
    change (kernel D hu H K k (P ⊗ₜ[ℂ] x) (Q ⊗ₜ[ℂ] y)
        (Finsupp.single b.val.1 (MvPolynomial.monomial b.val.2 1)) +
      kernel D hu H K k (P ⊗ₜ[ℂ] x) (Q ⊗ₜ[ℂ] y)
        (thetaLinear D (Finsupp.single b.val.1 (MvPolynomial.monomial b.val.2 1)))) * _ = _
    rw [theta_single, kernel_single_tmul, kernel_single_tmul]
    simp only [dualCarrierBasis, corrected_tmul, map_smul, actualForm_tmul,
      chargeScalar_neg, groundAction_reduction,
      map_neg]
    have negRed : -reduceCharge D b.val.1 = reduceCharge D b.val.1 := by
      funext i; exact CharTwo.neg_eq _
    rw [negRed]
    dsimp only [term]
    rw [chargeScalar_neg]
    ring
  · simp only [cosetKernel, finsum_eq_sum_of_fintype, ← mul_assoc,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [mul_assoc, ite_mul, zero_mul]
    rw [Finset.sum_eq_single (reduceCharge D b.val.1)]
    · simp [term, mul_assoc]
    · intro a ha hne
      simp [Ne.symm hne]
    · simp

/-- The common-channel four-linear tensors are independent on the ORIGINAL
selected ground. This isolates a coefficient using the existing operator basis;
it does not assert crossing or add a ground-algebra premise. -/
theorem ground_tensor_independent (D : LatticeData) (hu : IsUnit D.G.det)
    (c : ModTwoCharge D → ℂ)
    (vanishes : ∀ x y z t : ActualGround D hu,
      ∑ b : ModTwoCharge D, c b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) = 0) :
    ∀ b, c b = 0 := by
  classical
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have central : groundRepresentation D hu (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (ActualGround D hu)) := by
    simpa [complexSign] using selected_central D hu 1
  obtain ⟨algebra⟩ := actual_operator_algebra D hu (groundRank D hu) rank_eq
    (groundRepresentation D hu) central
  have operatorZero (x t : ActualGround D hu) :
      ∑ b : ModTwoCharge D,
        (c b * groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)) •
          chargeOperator D (groundRepresentation D hu) b = 0 := by
    apply LinearMap.ext
    intro y
    apply (selectedGroundPairing D hu).nondegenerate.2
    intro z
    simpa [LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply,
      smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using vanishes x y z t
  intro b
  have coordinate (x t : ActualGround D hu) :
      c b * groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) = 0 := by
    have h := congrArg (traceCoefficient D (groundRepresentation D hu) b) (operatorZero x t)
    simpa [map_sum, map_smul, coefficient_operator D hu (groundRepresentation D hu) central] using h
  by_contra hc
  have zeroOperator : chargeOperator D (groundRepresentation D hu) b = 0 := by
    apply LinearMap.ext
    intro x
    apply (selectedGroundPairing D hu).nondegenerate.2
    intro t
    exact (mul_eq_zero.mp (coordinate x t)).resolve_left hc
  exact algebra.basis.ne_zero b ((algebra.basis_apply b).trans zeroOperator)

/-- The common output weight is H+K+L-m-n-r-2. These are literal finite
coefficient sums, with all integer modes and both transported right phases. -/
def channelA (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) : ℂ :=
  ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
    Ring.choose (m : ℂ) j *
      cosetKernel D hu H K (r+(j : ℤ)) (m+n-(j : ℤ)) P Q R S a

def channelB (D : LatticeData) (hu : IsUnit D.G.det)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) : ℂ :=
  ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
    ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
      Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) *
        (ell.factorial : ℂ)⁻¹ *
          cosetKernel D hu K L (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ))
            Q R P ((oscillatorLower D ^ ell) S) a

def channelD (D : LatticeData) (hu : IsUnit D.G.det)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) : ℂ :=
  ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
    ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
      Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) *
        (ell.factorial : ℂ)⁻¹ *
          cosetKernel D hu H L (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ))
            P R Q ((oscillatorLower D ^ ell) S) a

/-- K is an EXPLICIT charge-coset polynomial identity from cosetKernel.
It is not defined by a Jacobi expression, and it is not proved in this file. -/
def identityK (D : LatticeData) (hu : IsUnit D.G.det)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) : Prop :=
  ∀ b : ModTwoCharge D,
    (∑ a : ModTwoCharge D, quadraticSign D a * fourierSign D a b *
      channelA D hu H K m n r P Q R S a) =
    (2 : ℂ)^12 * channelB D hu H K L m n r P Q R S b -
      ∑ a : ModTwoCharge D, quadraticSign D (a+b) *
        channelD D hu H K L m n r P Q R S a

set_option maxHeartbeats 4000000 in
/-- The actual original law on homogeneous tensor inputs is equivalent to the
EXPLICIT charge-coset kernel law, tested against all oscillator/ground tensor
detectors. TensorProduct.induction_on recovers every original detector. This
consumes S and O5 and supplies their operator-to-polynomial connection.
OriginalFourMReduction extends the INPUTS from these tensors to all states. -/
theorem original_jacobi_tensor_kernel (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (P Q R : Oscillator D) (x y z : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y) (hwR : w.val = R ⊗ₜ[ℂ] z)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val) :
    originalJacobi D hu hD m n r u v w ↔
    ∀ (S : Oscillator D) (d : ActualGround D hu),
      (∑ a : ModTwoCharge D, channelA D hu H K m n r P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z)) =
      (∑ b : ModTwoCharge D, channelB D hu H K L m n r P Q R S b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) b x)) -
      (∑ a : ModTwoCharge D, channelD D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a y)) := by
  classical
  let iterate (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
      Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d
  let first (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
            ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d)
  let second (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
            ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ ell) d)
  have leftExpansion (S : Oscillator D) (d : ActualGround D hu) :
      iterate (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelA D hu H K m n r P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z) := by
    dsimp only [iterate]
    simp only [channelA, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hwR, fourM_factorization D hu hD h24 H K (r+(j : ℤ)) (m+n-(j : ℤ))
      u v P Q R S x y z d huP hvQ huH hvK]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have firstExpansion (S : Oscillator D) (d : ActualGround D hu) :
      first (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelB D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a y) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a x) := by
    dsimp only [first]
    simp only [channelB, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [huP, lower_power_tmul,
      fourM_factorization D hu hD h24 K L (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ))
        v w Q R P ((oscillatorLower D ^ ell) S) y z x d hvQ hwR hvK hwL]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have secondExpansion (S : Oscillator D) (d : ActualGround D hu) :
      second (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelD D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a y) := by
    dsimp only [second]
    simp only [channelD, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [hvQ, lower_power_tmul,
      fourM_factorization D hu hD h24 H L (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ))
        u w P R Q ((oscillatorLower D ^ ell) S) x z y d huP hwR huH hwL]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [original_jacobi_scalar_finite D hu hD h24 H K L m n r u v w huH hvK hwL]
  change (∀ d, iterate d = first d-second d) ↔ _
  constructor
  · intro original S d
    have h := original (S ⊗ₜ[ℂ] d)
    rwa [leftExpansion, firstExpansion, secondExpansion] at h
  · intro polynomial d
    induction d using TensorProduct.induction_on with
    | zero => simp [iterate, first, second, fourMScalar]
    | tmul S d =>
      rw [leftExpansion, firstExpansion, secondExpansion]
      exact polynomial S d
    | add d e hd he =>
      dsimp only [iterate, first, second, fourMScalar] at hd he ⊢
      simp only [map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib] at hd he ⊢
      linear_combination hd + he

private theorem original_ground_dimension (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) :
    (Module.finrank ℂ (ActualGround D hu) : ℂ) = (2 : ℂ)^12 := by
  have h := (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.2.2.2.1 h24
  exact_mod_cast h

/-- Actual ground elimination for the three EXPLICIT polynomial/coset channels.
No crossing assumption is used in either direction. The reverse implication
uses the independent ORIGINAL ground tensor coefficients above. The connection
to actual homogeneous tensor inputs is original_jacobi_tensor_kernel. The finite
trilinear input extension and full all-state equivalence are proved in
OriginalFourMReduction. -/
theorem coset_ground_elimination (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) :
    (∀ x y z t : ActualGround D hu,
      (∑ a : ModTwoCharge D, channelA D hu H K m n r P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z)) =
      (∑ b : ModTwoCharge D, channelB D hu H K L m n r P Q R S b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)) -
      (∑ a : ModTwoCharge D, channelD D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a y))) ↔
      identityK D hu H K L m n r P Q R S := by
  classical
  let A := channelA D hu H K m n r P Q R S
  let B := channelB D hu H K L m n r P Q R S
  let F := channelD D hu H K L m n r P Q R S
  let size : ℂ := (2 : ℂ)^12
  have size_ne : size ≠ 0 := by dsimp [size]; norm_num
  let residual : ModTwoCharge D → ℂ := fun b =>
    (∑ a : ModTwoCharge D, quadraticSign D a * fourierSign D a b * A a) -
      size * B b + ∑ a : ModTwoCharge D, quadraticSign D (a+b) * F a
  have first (x y z t : ActualGround D hu) :
      size * (∑ a : ModTwoCharge D, A a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z)) =
      ∑ b : ModTwoCharge D,
        (∑ a : ModTwoCharge D, quadraticSign D a * fourierSign D a b * A a) *
          groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
    trans size * ∑ a : ModTwoCharge D, A a *
      ∑ b : ModTwoCharge D,
        (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D a * fourierSign D a b *
          groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_assoc, ground_exchange_first]
    simp only [original_ground_dimension D hu h24, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [size]
    field_simp
  have second (x y z t : ActualGround D hu) :
      size * (∑ a : ModTwoCharge D, F a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a y)) =
      ∑ b : ModTwoCharge D,
        (∑ a : ModTwoCharge D, quadraticSign D (a+b) * F a) *
          groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
    trans size * ∑ a : ModTwoCharge D, F a *
      ∑ b : ModTwoCharge D,
        (Module.finrank ℂ (ActualGround D hu) : ℂ)⁻¹ * quadraticSign D (a+b) *
          groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
          groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_assoc, ground_exchange_second]
    simp only [original_ground_dimension D hu h24, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [size]
    field_simp
  have expansion (x y z t : ActualGround D hu) :
      size * ((∑ a : ModTwoCharge D, A a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a z)) -
      (∑ b : ModTwoCharge D, B b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x)) +
      (∑ a : ModTwoCharge D, F a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) a y))) =
      ∑ b : ModTwoCharge D, residual b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu t (chargeOperator D (groundRepresentation D hu) b x) := by
    rw [mul_add, mul_sub, first, second, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [residual]
    ring
  constructor
  · intro scalar
    have coefficients : ∀ b, residual b = 0 := by
      apply ground_tensor_independent D hu residual
      intro x y z t
      rw [← expansion]
      dsimp only [A, B, F]
      linear_combination size * (scalar x y z t)
    intro b
    have h := coefficients b
    dsimp only [residual, size, A, B, F] at h
    change _ = _
    linear_combination h
  · intro charge_identity
    have coefficients (b : ModTwoCharge D) : residual b = 0 := by
      have h := charge_identity b
      dsimp only [residual, size, A, B, F]
      linear_combination h
    intro x y z t
    have h := expansion x y z t
    simp only [coefficients, zero_mul, Finset.sum_const_zero] at h
    have zero := (mul_eq_zero.mp h).resolve_left size_ne
    change _ = _ - _
    linear_combination zero

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset



