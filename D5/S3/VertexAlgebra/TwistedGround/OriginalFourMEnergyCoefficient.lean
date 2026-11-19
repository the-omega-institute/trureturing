/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMEnergyCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fourM coefficients from the total-energy diagonal of the sewn Gaussian. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy

/-! The original fourM contraction on the finite total-energy diagonal. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient LatticeInvolution
open HalfFock.LatticeHalfFockParityField
open OriginalFourMChargeCoset OriginalGaussianFixedEnergy
open OriginalGaussianExternalBlocks OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open OriginalGaussianSourceRestriction OriginalSourceInverseCoefficient
open SourceBPZ.OriginalSourceCoevaluation
open SignedOscillatorWick MixedIntertwiner OperatorAlgebra
open FactorialFockMetric (weight)
open MvPolynomial
open private groundAction_reduction groundForm chargeScalar_neg lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private theorem groundAction_neg (D : LatticeData) (hu : IsUnit D.G.det) (q : Charge D) :
    groundAction D hu (-q) = groundAction D hu q := by
  rw [groundAction_reduction, groundAction_reduction, map_neg]
  congr 1
  funext b
  exact CharTwo.neg_eq _

private theorem reflected_corrected_even (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (p x : Oscillator D) (s : ℤ) :
    oscillatorCorrected D hu (-q) (2*s) (sigma D p) x =
      oscillatorCorrected D hu q (2*s) p x := by
  let g₁ : ActualGround D hu := fun _ => 1
  let g := groundRepresentation D hu (groundLift D q)⁻¹ g₁
  have hg : groundAction D hu q g = g₁ :=
    (groundRepresentation D hu).self_inv_apply (groundLift D q) g₁
  have phase : (-1 : ℂ)^(2*s) = 1 := by
    rw [zpow_mul]
    norm_num
  have h := correctedField_theta D hu (Finsupp.single q p) (2*s)
  change (correctedField D hu (thetaLinear D (Finsupp.single q p))).coeff (2*s) = _ at h
  rw [theta_single, phase, one_smul] at h
  have applied := LinearMap.congr_fun h (x ⊗ₜ[ℂ] g)
  change (correctedField D hu (Finsupp.single (-q) (sigma D p))).coeff (2*s) (x ⊗ₜ[ℂ] g) =
    (correctedField D hu (Finsupp.single q p)).coeff (2*s) (x ⊗ₜ[ℂ] g) at applied
  rw [corrected_tmul, corrected_tmul, groundAction_neg, hg, chargeScalar_neg] at applied
  have hc : chargeScalar D q ≠ 0 := zpow_ne_zero _ (by norm_num)
  have projected := congrArg (oscillatorCoordinate D hu) applied
  simp only [map_smul, oscillatorCoordinate_tmul, show g₁ 0 = 1 from rfl, one_smul]
    at projected
  exact (smul_right_injective (Oscillator D) hc) projected

/-- The reflected first leg agrees at each even Laurent mode of the original
left kernel. The equality holds before summing over the intermediate energy. -/
theorem oscillatorKernel_reflected (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k : ℤ) (q : Charge D) (p P Q : Oscillator D) :
    oscillatorKernel D hu H K k (-q) (sigma D p) P Q =
      oscillatorKernel D hu H K k q p P Q := by
  unfold oscillatorKernel
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [reflected_corrected_even]

/-- The half-average reduces to one original kernel by equality of its two
reflected terms, with the right leg held at its original exponent. -/
theorem cosetKernel_unreflected (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (k t : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    cosetKernel D hu H K k t P Q R S a =
      ∑ᶠ b : EnergyFiber D ((H : ℤ)+(K : ℤ)-k-1),
        if reduceCharge D b.val.1 = a then
          chargeScalar D b.val.1 * chargeScalar D (-b.val.1) *
            oscillatorKernel D hu H K k b.val.1 (monomial b.val.2 1) P Q *
            wick D S (oscillatorCorrected D hu (-b.val.1) (-2*t-2)
              (dualOscillatorMonomial D b.val.2) R)
        else 0 := by
  classical
  let := energyFiber_finite D hD ((H : ℤ)+(K : ℤ)-k-1)
  let := Fintype.ofFinite (EnergyFiber D ((H : ℤ)+(K : ℤ)-k-1))
  simp only [cosetKernel, oscillatorKernel_reflected, finsum_eq_sum_of_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

private def chargeFiberEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (E : ℕ) :
    EnergyFiber D E ≃
      Σ q : {q : Charge D // chargeEnergy D q ≤ E},
        {alpha : Exponent D // oscillatorEnergy alpha = E - (chargeEnergy D q.val).toNat} where
  toFun b := by
    have hb := b.property
    change chargeEnergy D b.val.1 + (oscillatorEnergy b.val.2 : ℤ) = (E : ℤ) at hb
    have hq := chargeEnergy_nonneg D hD b.val.1
    refine ⟨⟨b.val.1, by omega⟩, ⟨b.val.2, ?_⟩⟩
    change oscillatorEnergy b.val.2 = E - (chargeEnergy D b.val.1).toNat
    omega
  invFun b := by
    have hq := chargeEnergy_nonneg D hD b.1.val
    have hm := b.1.property
    have hn := b.2.property
    exact ⟨(b.1.val, b.2.val), show chargeEnergy D b.1.val +
        (oscillatorEnergy b.2.val : ℤ) = (E : ℤ) by omega⟩
  left_inv b := Subtype.ext rfl
  right_inv b := by
    rcases b with ⟨⟨q, hq⟩, ⟨alpha, ha⟩⟩
    rfl

private theorem oscillatorFiber_finite (D : LatticeData) (n : ℕ) :
    Finite {alpha : Exponent D // oscillatorEnergy alpha = n} := by
  let := oscillatorLeFinite D n
  exact Finite.of_injective
    (fun a : {alpha : Exponent D // oscillatorEnergy alpha = n} =>
      (⟨a.val, a.property.le⟩ : {alpha : Exponent D // oscillatorEnergy alpha ≤ n}))
    (fun a b h => Subtype.ext (congrArg
      (fun x : {alpha : Exponent D // oscillatorEnergy alpha ≤ n} => x.val) h))

private theorem oscillator_finsum (D : LatticeData) (n : ℕ) (f : Exponent D → ℂ) :
    (∑ᶠ a : {alpha : Exponent D // oscillatorEnergy alpha = n}, f a.val) =
      ∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then f alpha else 0 := by
  classical
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]


/-- The even ordinary coefficients of the original sewn Gaussian, with the
charge factor and the formal shift by the full charge energy. -/
def chargeSeries (D : LatticeData) (q : Charge D)
    (betaL gammaL betaR gammaR : Exponent D) : PowerSeries ℂ :=
  (16 : ℂ)^(-chargeEnergy D q) •
    (PowerSeries.X ^ (chargeEnergy D q).toNat *
      PowerSeries.mk (fun n =>
        let F := fourSupport D betaL gammaL betaR gammaR
        coefficient (2*n) (sewn D q (compactExternal D F)
          (externalOccupation D F betaL gammaL betaR gammaR))))

private theorem chargeScalar_pair (D : LatticeData) (q : Charge D) :
    chargeScalar D q * chargeScalar D (-q) = (16 : ℂ)^(-chargeEnergy D q) := by
  rw [chargeScalar_neg, chargeScalar, ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [show (16 : ℂ) = 2 ^ (4 : ℤ) by norm_num, ← zpow_mul]
  have h := two_chargeEnergy D q
  change 2 * chargeEnergy D q = chargeNorm D q at h
  congr 1
  omega

private theorem chargeSeries_coeff (D : LatticeData) (q : Charge D) (E : ℕ)
    (hq : chargeEnergy D q ≤ E) (betaL gammaL betaR gammaR : Exponent D) :
    PowerSeries.coeff E (chargeSeries D q betaL gammaL betaR gammaR) =
      let F := fourSupport D betaL gammaL betaR gammaR
      chargeScalar D q * chargeScalar D (-q) *
        coefficient (2*(E - (chargeEnergy D q).toNat))
          (sewn D q (compactExternal D F) (externalOccupation D F betaL gammaL betaR gammaR)) := by
  have h : (chargeEnergy D q).toNat ≤ E := by omega
  simp [chargeSeries, PowerSeries.coeff_X_pow_mul', h, chargeScalar_pair, smul_eq_mul]

/-- The doubled half-integral weight of an external monomial. -/
abbrev doubledWeight (D : LatticeData) (b : Exponent D) : ℤ :=
  Finsupp.weight (fun i => (LatticeHalfFockChargedCoefficients.omega D i : ℤ)) b

/-- The literal Laurent selector for one leg at the remaining oscillator energy. -/
def selector (D : LatticeData) (q : Charge D) (e : ℤ) (n : ℕ)
    (beta gamma : Exponent D) : ℂ :=
  if e + chargeNorm D q = -2*(n : ℤ) - doubledWeight D beta + doubledWeight D gamma
  then 1 else 0

private abbrev wickLeg (D : LatticeData) (hu : IsUnit D.G.det) (q : Charge D)
    (e : ℤ) (p P Q : Oscillator D) :=
  wick D Q (oscillatorCorrected D hu q e p P)

private theorem wickLeg_expand (D : LatticeData) (hu : IsUnit D.G.det) (q : Charge D)
    (e : ℤ) (p P Q : Oscillator D) :
    wickLeg D hu q e p P Q =
      ∑ beta ∈ P.support, ∑ gamma ∈ Q.support,
        P.coeff beta * Q.coeff gamma *
          wickLeg D hu q e p (monomial beta 1) (monomial gamma 1) := by
  classical
  conv_lhs => rw [P.as_sum, Q.as_sum]
  simp only [wickLeg, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro g hg
  rw [show monomial b (P.coeff b) = P.coeff b • monomial b 1 by
    simp [smul_monomial, smul_eq_mul],
    show monomial g (Q.coeff g) = Q.coeff g • monomial g 1 by
      simp [smul_monomial, smul_eq_mul] ]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- All four external occupations and their literal factorial and Laurent
factors, at a fixed charge and total energy. -/
def polynomialCoefficient (D : LatticeData) (q : Charge D) (E : ℕ) (eL eR : ℤ)
    (P Q R S : Oscillator D) : ℂ :=
  ∑ betaL ∈ P.support, ∑ gammaL ∈ Q.support,
    ∑ betaR ∈ R.support, ∑ gammaR ∈ S.support,
      let n := E - (chargeEnergy D q).toNat
      (P.coeff betaL * Q.coeff gammaL * R.coeff betaR * S.coeff gammaR) *
        (weight betaL : ℂ) * (weight gammaL : ℂ) *
        (weight betaR : ℂ) * (weight gammaR : ℂ) *
        selector D q eL n betaL gammaL * selector D (-q) eR n betaR gammaR *
        PowerSeries.coeff E (chargeSeries D q betaL gammaL betaR gammaR)

private theorem monomialCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (E : ℕ)
    (hq : chargeEnergy D q ≤ E) (eL eR : ℤ) (betaL gammaL betaR gammaR : Exponent D) :
    let n := E - (chargeEnergy D q).toNat
    (∑ᶠ a : {alpha : Exponent D // oscillatorEnergy alpha = n},
      chargeScalar D q * chargeScalar D (-q) *
        wickLeg D hu q eL (monomial a.val 1) (monomial betaL 1) (monomial gammaL 1) *
        wickLeg D hu (-q) eR (dualOscillatorMonomial D a.val)
          (monomial betaR 1) (monomial gammaR 1)) =
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
        (weight betaR : ℂ) * (weight gammaR : ℂ) *
        selector D q eL n betaL gammaL * selector D (-q) eR n betaR gammaR *
        PowerSeries.coeff E (chargeSeries D q betaL gammaL betaR gammaR) := by
  dsimp only
  rw [oscillator_finsum D (E - (chargeEnergy D q).toNat) (fun alpha =>
    chargeScalar D q * chargeScalar D (-q) *
      wickLeg D hu q eL (monomial alpha 1) (monomial betaL 1) (monomial gammaL 1) *
      wickLeg D hu (-q) eR (dualOscillatorMonomial D alpha)
        (monomial betaR 1) (monomial gammaR 1)),
    chargeSeries_coeff D q E hq]
  rw [show (∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha =
      E - (chargeEnergy D q).toNat then
        chargeScalar D q * chargeScalar D (-q) *
          wickLeg D hu q eL (monomial alpha 1) (monomial betaL 1) (monomial gammaL 1) *
          wickLeg D hu (-q) eR (dualOscillatorMonomial D alpha)
            (monomial betaR 1) (monomial gammaR 1) else 0) = _ from
    original_fixed_energy_coefficient D hu q betaL gammaL betaR gammaR eL eR
      (E - (chargeEnergy D q).toNat)]
  unfold selector
  dsimp only
  ring

private theorem polynomialCoefficient_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (E : ℕ)
    (hq : chargeEnergy D q ≤ E) (eL eR : ℤ) (P Q R S : Oscillator D) :
    (∑ᶠ a : {alpha : Exponent D // oscillatorEnergy alpha = E - (chargeEnergy D q).toNat},
      chargeScalar D q * chargeScalar D (-q) *
        wickLeg D hu q eL (monomial a.val 1) P Q *
        wickLeg D hu (-q) eR (dualOscillatorMonomial D a.val) R S) =
      polynomialCoefficient D q E eL eR P Q R S := by
  classical
  let := oscillatorFiber_finite D (E - (chargeEnergy D q).toNat)
  let := Fintype.ofFinite {alpha : Exponent D //
    oscillatorEnergy alpha = E - (chargeEnergy D q).toNat}
  unfold polynomialCoefficient
  simp only [finsum_eq_sum_of_fintype]
  simp_rw [show ∀ p, wickLeg D hu q eL p P Q = _ from fun p =>
      wickLeg_expand D hu q eL p P Q, Finset.mul_sum, Finset.sum_mul]
  simp_rw [show ∀ p, wickLeg D hu (-q) eR p R S = _ from fun p =>
      wickLeg_expand D hu (-q) eR p R S, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro betaL hbL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gammaL hgL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro betaR hbR
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gammaR hgR
  let c := P.coeff betaL * Q.coeff gammaL * R.coeff betaR * S.coeff gammaR
  calc
    _ = c * ∑ alpha : {alpha : Exponent D //
        oscillatorEnergy alpha = E - (chargeEnergy D q).toNat},
      chargeScalar D q * chargeScalar D (-q) *
        wickLeg D hu q eL (monomial alpha.val 1) (monomial betaL 1) (monomial gammaL 1) *
        wickLeg D hu (-q) eR (dualOscillatorMonomial D alpha.val)
          (monomial betaR 1) (monomial gammaR 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha ha
      dsimp [c]
      ring
    _ = _ := by
      rw [← finsum_eq_sum_of_fintype, monomialCoefficient D hu q E hq]
      dsimp [c]
      ring


/-- The original left Laurent exponent written on the total-energy diagonal. -/
def leftExponent (H K E i j : ℕ) : ℤ :=
  -2*(E : ℤ) - (2*(H : ℤ)-3-2*(j : ℤ)) + (2*(K : ℤ)-3-2*(i : ℤ))

private abbrev chargeSublevel (D : LatticeData) (E : ℕ) :=
  {q : Charge D // chargeEnergy D q ≤ E}

/-- One fixed coset of the total-energy diagonal before the substitution
of the negative square coordinate. Each degree is a finite sum. -/
def cosetSeries (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (t : ℤ) (P Q R S : Oscillator D)
    (a : ModTwoCharge D) : PowerSeries ℂ := PowerSeries.mk fun E =>
  let : Finite (chargeSublevel D E) := (chargeSublevel_finite D hD E).to_subtype
  let := Fintype.ofFinite (chargeSublevel D E)
  ∑ q : chargeSublevel D E, if reduceCharge D q.val = a then
    ∑ i ∈ Finset.range (K-1), ∑ j ∈ Finset.range (H-1),
      ((-1 : ℂ)^((K : ℤ)-(i : ℤ)+(j : ℤ)) / ((i.factorial : ℂ)*(j.factorial : ℂ))) *
        polynomialCoefficient D q.val E (leftExponent H K E i j) (-2*t-2)
          ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ i) Q) R S
    else 0

private theorem cosetKernel_energy_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K E : ℕ) (t : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    cosetKernel D hu H K ((H : ℤ)+(K : ℤ)-E-1) t P Q R S a =
      PowerSeries.coeff E (PowerSeries.rescale (-1) (cosetSeries D hD H K t P Q R S a)) := by
  classical
  let k : ℤ := (H : ℤ)+(K : ℤ)-E-1
  change cosetKernel D hu H K k t P Q R S a = _
  rw [cosetKernel_unreflected D hu hD]
  have he : (H : ℤ)+(K : ℤ)-k-1 = (E : ℤ) := by dsimp [k]; ring
  rw [he, PowerSeries.coeff_rescale, cosetSeries, PowerSeries.coeff_mk]
  let := energyFiber_finite D hD (E : ℤ)
  let := Fintype.ofFinite (EnergyFiber D E)
  let : Finite (chargeSublevel D E) := (chargeSublevel_finite D hD E).to_subtype
  let := Fintype.ofFinite (chargeSublevel D E)
  let (q : chargeSublevel D E) := oscillatorFiber_finite D (E - (chargeEnergy D q.val).toNat)
  let (q : chargeSublevel D E) := Fintype.ofFinite {alpha : Exponent D //
    oscillatorEnergy alpha = E - (chargeEnergy D q.val).toNat}
  rw [finsum_eq_sum_of_fintype, ← (chargeFiberEquiv D hD E).symm.sum_comp, Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  change (∑ alpha : {alpha : Exponent D //
      oscillatorEnergy alpha = E - (chargeEnergy D q.val).toNat},
    if reduceCharge D q.val = a then
      chargeScalar D q.val * chargeScalar D (-q.val) *
        oscillatorKernel D hu H K k q.val (monomial alpha.val 1) P Q *
        wickLeg D hu (-q.val) (-2*t-2) (dualOscillatorMonomial D alpha.val) R S
    else 0) = _
  by_cases hqa : reduceCharge D q.val = a
  · simp only [ite_eq_left hqa, oscillatorKernel, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hleft : 2*(k+1-(i : ℤ)-2*(H : ℤ)+(j : ℤ)) = leftExponent H K E i j := by
      dsimp [k, leftExponent]
      ring
    rw [hleft, ← polynomialCoefficient_eq D hu q.val E q.property,
      finsum_eq_sum_of_fintype]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    have hsign : (H : ℤ)+(k+1-(i : ℤ)-2*(H : ℤ)+(j : ℤ)) =
        -(E : ℤ) + ((K : ℤ)-(i : ℤ)+(j : ℤ)) := by dsimp [k]; ring
    rw [hsign, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    rw [show -(E : ℤ) = (E : ℤ) - 2*(E : ℤ) by ring,
      zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul (-1 : ℂ) 2 (E : ℤ)]
    norm_num [zpow_natCast]
    ring
  · simp [hqa]

/-- The original rank-24 homogeneous fourM scalar is the total-energy
coefficient of the sewn Gaussian, with the two ordered ground coefficients
outside the oscillator contraction in each mod-two charge coset. -/
theorem fourM_energy_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K E : ℕ) (t : ℤ) (u v : paritySpace D hu (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    fourMScalar D hu hD ((H : ℤ)+(K : ℤ)-E-1) t u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D,
        PowerSeries.coeff E (PowerSeries.rescale (-1) (cosetSeries D hD H K t P Q R S a)) *
          groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
          groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z) := by
  rw [fourM_factorization D hu hD h24 H K _ t u v P Q R S x y z d huP hvQ huH hvK]
  simp only [cosetKernel_energy_coefficient D hu hD H K E t]

/-- The original scalar at negative signed total energy has an empty
intermediate fiber. -/
theorem fourM_negative_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k t : ℤ) (u v : paritySpace D hu (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hneg : (H : ℤ) + (K : ℤ) - k - 1 < 0) :
    fourMScalar D hu hD k t u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) = 0 := by
  rw [fourM_factorization D hu hD h24 H K k t u v P Q R S x y z d huP hvQ huH hvK]
  let : IsEmpty (EnergyFiber D ((H : ℤ)+(K : ℤ)-k-1)) := ⟨fun b => by
    have hq := chargeEnergy_nonneg D hD b.val.1
    have hb := b.property
    dsimp [LatticePositiveEnergy.energy] at hb
    omega⟩
  simp [cosetKernel, finsum_of_isEmpty]


private theorem doubledWeight_cast (D : LatticeData) (beta : Exponent D) :
    doubledWeight D beta = (oddWeight D beta : ℤ) := by
  simp only [doubledWeight, oddWeight, Finsupp.weight_apply, Finsupp.sum,
    nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_id]

private theorem lowering_weight (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H j : ℕ) (P : Oscillator D) (g : ActualGround D hu)
    (henergy : actualTensorL0 D hu (P ⊗ₜ[ℂ] g) = (H : ℂ) • (P ⊗ₜ[ℂ] g))
    (hg : g ≠ 0) (beta : Exponent D) (hb : beta ∈ ((oscillatorLower D ^ j) P).support) :
    doubledWeight D beta = 2*(H : ℤ)-3-2*(j : ℤ) := by
  classical
  have hlo := lowering_integer_energy D hu h24 (H : ℤ) (P ⊗ₜ[ℂ] g)
    (by simpa only [Int.cast_natCast] using henergy) j
  change actualTensorL0 D hu
      ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ j)
        (P ⊗ₜ[ℂ] g)) = _ at hlo
  rw [lower_power_tmul] at hlo
  obtain ⟨b, hgb⟩ : ∃ b, g b ≠ 0 := by
    by_contra! hz
    exact hg (funext hz)
  let p := (oscillatorLower D ^ j) P
  let B := actualAmbientBasis D hu
  have hrepr : B.repr (p ⊗ₜ[ℂ] g) (beta, b) = g b * p.coeff beta := by
    unfold B actualAmbientBasis
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    rfl
  have hn : B.repr (p ⊗ₜ[ℂ] g) (beta, b) ≠ 0 := by
    rw [hrepr]
    exact mul_ne_zero hgb (mem_support_iff.mp hb)
  change actualTensorL0 D hu (p ⊗ₜ[ℂ] g) =
    (((H : ℤ)-(j : ℤ) : ℤ) : ℂ) • (p ⊗ₜ[ℂ] g) at hlo
  have hc := congrArg (fun v => B.repr v (beta, b)) hlo
  change (actualAmbientBasis D hu).repr (actualTensorL0 D hu (p ⊗ₜ[ℂ] g)) (beta, b) =
    _ at hc
  rw [actualTensorL0_repr] at hc
  simp only [← show B = actualAmbientBasis D hu from rfl, map_smul,
    Finsupp.smul_apply, smul_eq_mul, h24] at hc
  have hw := mul_right_cancel₀ hn hc
  have hw' : (oddWeight D beta : ℂ) = (((2*(H : ℤ)-3-2*(j : ℤ) : ℤ)) : ℂ) := by
    push_cast at hw ⊢
    linear_combination 2 * hw
  rw [doubledWeight_cast]
  exact_mod_cast hw'

/-- The two actual left occupations have the lowering-shifted weights.
Their difference gives the original exponent, and the literal selector is
one throughout the positive charge sublevel. -/
theorem lowered_left_selector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K E i j : ℕ) (q : Charge D) (hq : chargeEnergy D q ≤ E)
    (P Q : Oscillator D) (x y : ActualGround D hu)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] x) = (H : ℂ) • (P ⊗ₜ[ℂ] x))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] y) = (K : ℂ) • (Q ⊗ₜ[ℂ] y))
    (beta gamma : Exponent D)
    (hb : beta ∈ ((oscillatorLower D ^ j) P).support)
    (hg : gamma ∈ ((oscillatorLower D ^ i) Q).support) :
    doubledWeight D beta = 2*(H : ℤ)-3-2*(j : ℤ) ∧
    doubledWeight D gamma = 2*(K : ℤ)-3-2*(i : ℤ) ∧
    leftExponent H K E i j = -2*(E : ℤ)-doubledWeight D beta+doubledWeight D gamma ∧
    selector D q (leftExponent H K E i j) (E - (chargeEnergy D q).toNat) beta gamma = 1 := by
  have hβ := lowering_weight D hu h24 H j P x hP hx beta hb
  have hγ := lowering_weight D hu h24 K i Q y hQ hy gamma hg
  have he : leftExponent H K E i j =
      -2*(E : ℤ)-doubledWeight D beta+doubledWeight D gamma := by
    rw [hβ, hγ]
    rfl
  have hm := chargeEnergy_nonneg D hD q
  have hnorm : chargeNorm D q = 2 * chargeEnergy D q := (two_chargeEnergy D q).symm
  refine ⟨hβ, hγ, he, ?_⟩
  unfold selector
  rw [ite_eq_left]
  omega

/-- The right leg selects the signed mode determined by its even weight
difference and vanishes for an odd difference. -/
theorem right_selector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (E : ℕ) (q : Charge D) (hq : chargeEnergy D q ≤ E)
    (t : ℤ) (beta gamma : Exponent D) :
    selector D (-q) (-2*t-2) (E - (chargeEnergy D q).toNat) beta gamma =
      if (doubledWeight D beta - doubledWeight D gamma) % 2 = 0 then
        if t = (E : ℤ)-1+(doubledWeight D beta-doubledWeight D gamma)/2 then 1 else 0
      else 0 := by
  have hnorm : chargeNorm D (-q) = 2 * chargeEnergy D q := by
    unfold chargeNorm
    rw [bilinear_neg_neg, ← two_chargeEnergy]
  have hm := chargeEnergy_nonneg D hD q
  unfold selector
  split_ifs <;> first | rfl | omega

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
