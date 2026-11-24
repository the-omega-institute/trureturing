/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledOccupationReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeDoubledOccupationReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous inverse-flow occupation coefficients of the actual mixed Leech pair field. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledBPZCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

/-! The homogeneous occupation form of the mixed BPZ sewing coefficient. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledOccupationReadout

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open ActualLeechHyperbolic (leechData leech_spec)
open ActualChargedAdjoint (actualForm)
open OperatorAlgebra (chargeOperator)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeMixedPairField (mu)
open NativeDoubledBPZWick (leftExponent projectionFactor)
open NativeDoubledBPZCoevaluation (mu_fourPoint_gaussian_cosets mu_fourPoint_off_right_grade)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMEnergyCoefficient (doubledWeight selector polynomialCoefficient chargeSeries)
open OriginalFourMVariableSupport (occupationReadout inverseFlow)
open OriginalFourMChargeGerm (chargeSectorSewn)
open OriginalFourMChargeNormal (sewn_charge_coefficient)
open OriginalGaussianSewnAnalytic (coefficient)

open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private groundForm lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private doubledWeight_cast from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private occupationReadout_nested occupationLinear_sum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent
open private coefficient_fun_sum coefficient_const_mul chargeSectorSewn_analyticAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm

/-- The actual tensor lowering shifts the doubled weight of each supported
occupation by twice the number of lowering steps. -/
theorem lowering_weight (D : LatticeData) (hu : IsUnit D.G.det) (M j : ℕ)
    (P : Oscillator D) (p : ActualGround D hu) (hp : p ≠ 0)
    (hP : P ⊗ₜ[ℂ] p ∈ actualGrade D hu M) (β : Exponent D)
    (hβ : β ∈ ((oscillatorLower D ^ j) P).support) :
    doubledWeight D β = (M : ℤ) - 2 * (j : ℤ) := by
  classical
  have henergy := (actualGrade_eigen D hu M (P ⊗ₜ[ℂ] p)).mp hP
  have hlo := lowering_eigen D hu (M : ℤ) (P ⊗ₜ[ℂ] p)
    (by simpa only [Int.cast_natCast] using henergy) j
  simp only [T, lower_power_tmul] at hlo
  obtain ⟨b, hb⟩ : ∃ b, p b ≠ 0 := by
    by_contra! hz
    exact hp (funext hz)
  let A := (oscillatorLower D ^ j) P
  let B := actualAmbientBasis D hu
  have hrepr : B.repr (A ⊗ₜ[ℂ] p) (β, b) = p b * A.coeff β := by
    unfold B actualAmbientBasis
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    rfl
  have hn : B.repr (A ⊗ₜ[ℂ] p) (β, b) ≠ 0 := by
    rw [hrepr]
    exact mul_ne_zero hb (MvPolynomial.mem_support_iff.mp hβ)
  have hc := congrArg (fun v => B.repr v (β, b)) hlo
  change (actualAmbientBasis D hu).repr (actualTensorL0 D hu (A ⊗ₜ[ℂ] p)) (β, b) = _ at hc
  rw [actualTensorL0_repr] at hc
  simp only [← show B = actualAmbientBasis D hu from rfl, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at hc
  have hw := mul_right_cancel₀ hn hc
  have hw' : (oddWeight D β : ℂ) = (((M : ℤ) - 2 * (j : ℤ) : ℤ) : ℂ) := by
    change (D.rank : ℂ) / 16 + (oddWeight D β : ℂ) / 2 =
      (D.rank : ℂ) / 16 + (((M : ℤ) - 2 * (j : ℤ) : ℤ) : ℂ) / 2 at hw
    linear_combination 2 * hw
  rw [doubledWeight_cast]
  exact_mod_cast hw'

/-- The cutoff `M / 2 + 1` also retains the last lowering at even `M`. -/
theorem lowering_eq_zero_of_cutoff (D : LatticeData) (hu : IsUnit D.G.det) (M j : ℕ)
    (P : Oscillator D) (p : ActualGround D hu) (hp : p ≠ 0)
    (hP : P ⊗ₜ[ℂ] p ∈ actualGrade D hu M) (hj : M / 2 + 1 ≤ j) :
    (oscillatorLower D ^ j) P = 0 := by
  apply MvPolynomial.ext
  intro β
  rw [show (0 : Oscillator D).coeff β = 0 from rfl]
  by_contra hβ
  have hw := lowering_weight D hu M j P p hp hP β (MvPolynomial.mem_support_iff.mpr hβ)
  rw [doubledWeight_cast] at hw
  omega

/-- Homogeneity makes the original signed left selector one on supported
lowered occupations throughout the charge sublevel. -/
theorem lowered_left_selector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (M K E j ell : ℕ)
    (q : Charge D) (hq : chargeEnergy D q ≤ E) (P Q : Oscillator D)
    (x y : ActualGround D hu) (hx : x ≠ 0) (hy : y ≠ 0)
    (hP : P ⊗ₜ[ℂ] x ∈ actualGrade D hu M) (hQ : Q ⊗ₜ[ℂ] y ∈ actualGrade D hu K)
    (β γ : Exponent D) (hβ : β ∈ ((oscillatorLower D ^ j) P).support)
    (hγ : γ ∈ ((oscillatorLower D ^ ell) Q).support) :
    selector D q (leftExponent M K E j ell) (E - (chargeEnergy D q).toNat) β γ = 1 := by
  have hwβ := lowering_weight D hu M j P x hx hP β hβ
  have hwγ := lowering_weight D hu K ell Q y hy hQ γ hγ
  have hm := chargeEnergy_nonneg D hD q
  have hn : chargeNorm D q = 2 * chargeEnergy D q := (two_chargeEnergy D q).symm
  unfold selector leftExponent
  rw [hwβ, hwγ, hn, ite_eq_left (by omega)]

/-- The reflected right selector uses the full signed doubled exponent.
The charge norm cancels the energy shift, including at charge zero. -/
theorem right_selector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (L N E : ℕ)
    (q : Charge D) (hq : chargeEnergy D q ≤ E) (eR : ℤ) (R S : Oscillator D)
    (z d : ActualGround D hu) (hz : z ≠ 0) (hd : d ≠ 0)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade D hu L) (hS : S ⊗ₜ[ℂ] d ∈ actualGrade D hu N)
    (δ η : Exponent D) (hδ : δ ∈ R.support) (hη : η ∈ S.support) :
    selector D (-q) eR (E - (chargeEnergy D q).toNat) δ η =
      if eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) then 1 else 0 := by
  have hwδ := lowering_weight D hu L 0 R z hz hR δ (by simpa using hδ)
  have hwη := lowering_weight D hu N 0 S d hd hS η (by simpa using hη)
  have hm := chargeEnergy_nonneg D hD q
  have hn : chargeNorm D (-q) = 2 * chargeEnergy D q := by
    unfold chargeNorm
    rw [bilinear_neg_neg, ← two_chargeEnergy]
  unfold selector
  rw [hwδ, hwη, hn]
  split_ifs <;> first | rfl | omega

private theorem polynomialCoefficient_on_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (M K L N E j ell : ℕ)
    (q : Charge D) (hq : chargeEnergy D q ≤ E) (P Q R S : Oscillator D)
    (x y z d : ActualGround D hu) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hd : d ≠ 0)
    (hP : P ⊗ₜ[ℂ] x ∈ actualGrade D hu M) (hQ : Q ⊗ₜ[ℂ] y ∈ actualGrade D hu K)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade D hu L) (hS : S ⊗ₜ[ℂ] d ∈ actualGrade D hu N) :
    polynomialCoefficient D q E (leftExponent M K E j ell) ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ))
        ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S =
      occupationReadout D ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S
        (fun β γ δ η => PowerSeries.coeff E (chargeSeries D q β γ δ η)) := by
  unfold polynomialCoefficient occupationReadout
  dsimp only
  refine Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl fun γ hγ =>
    Finset.sum_congr rfl fun δ hδ => Finset.sum_congr rfl fun η hη => ?_
  simp only [lowered_left_selector D hu hD M K E j ell q hq P Q x y hx hy hP hQ β γ hβ hγ,
    right_selector D hu hD L N E q hq ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ))
      R S z d hz hd hR hS δ η hδ hη, ite_true, mul_one]

private theorem lowering_weight_product (j ell : ℕ) :
    (-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ)) =
      ((-1 : ℂ) ^ j / (j.factorial : ℂ)) * ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem inverseFlow_readout (D : LatticeData) (M K : ℕ) (P Q R S : Oscillator D)
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    occupationReadout D (inverseFlow D (M / 2 + 1) P) (inverseFlow D (K / 2 + 1) Q) R S f =
      ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
        ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
          occupationReadout D ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S f := by
  simp only [occupationReadout_nested, inverseFlow, map_sum, map_smul, smul_eq_mul]
  simp only [occupationLinear_sum, Finset.mul_sum, lowering_weight_product, mul_assoc]

private theorem occupationReadout_sum {ι : Type*} (D : LatticeData) (P Q R S : Oscillator D)
    (t : Finset ι) (c : ι → ℂ)
    (f : ι → Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    occupationReadout D P Q R S (fun β γ δ η => ∑ i ∈ t, c i * f i β γ δ η) =
      ∑ i ∈ t, c i * occupationReadout D P Q R S (f i) := by
  simp only [occupationReadout_nested, occupationLinear_sum]

open Classical in
/-- The exact fixed-occupation coefficient from the native charge series in
one mod-two coset. The charge shift and both charge scalars are in `chargeSeries`. -/
def cosetChargeCoefficient (D : LatticeData) (E : ℕ) (a : ModTwoCharge D)
    (β γ δ η : Exponent D) : ℂ :=
  ∑ᶠ q : {q : Charge D // chargeEnergy D q ≤ E},
    if reduceCharge D q.val = a then PowerSeries.coeff E (chargeSeries D q.val β γ δ η) else 0

set_option maxHeartbeats 4000000 in
-- Elaborate the finite charge sum with all four dependent occupation supports.
/-- Commute the finite charge sum through all four occupation sums and
combine the two signed factorial-weighted lowering ranges. -/
theorem coset_lowering_eq_inverse_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (M K L N E : ℕ) (a : ModTwoCharge D)
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hd : d ≠ 0)
    (hP : P ⊗ₜ[ℂ] x ∈ actualGrade D hu M) (hQ : Q ⊗ₜ[ℂ] y ∈ actualGrade D hu K)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade D hu L) (hS : S ⊗ₜ[ℂ] d ∈ actualGrade D hu N) :
    (∑ᶠ q : {q : Charge D // chargeEnergy D q ≤ E},
      if reduceCharge D q.val = a then
        ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
          ((-1 : ℂ) ^ ((j : ℤ) + (ell : ℤ)) / ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
            polynomialCoefficient D q.val E (leftExponent M K E j ell)
              ((N : ℤ) - (L : ℤ) - 2 * (E : ℤ))
              ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ ell) Q) R S
      else 0) =
      occupationReadout D (inverseFlow D (M / 2 + 1) P) (inverseFlow D (K / 2 + 1) Q) R S
        (cosetChargeCoefficient D E a) := by
  classical
  let Charges := {q : Charge D // chargeEnergy D q ≤ E}
  let : Finite Charges := (chargeSublevel_finite D hD E).to_subtype
  let := Fintype.ofFinite Charges
  let c (q : Charges) : ℂ := if reduceCharge D q.val = a then 1 else 0
  let f (q : Charges) (β γ δ η : Exponent D) :=
    PowerSeries.coeff E (chargeSeries D q.val β γ δ η)
  have hcoeff : cosetChargeCoefficient D E a = fun β γ δ η => ∑ q : Charges, c q * f q β γ δ η := by
    funext β γ δ η
    rw [cosetChargeCoefficient, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : reduceCharge D q.val = a <;> simp [c, f, hq]
  rw [hcoeff, occupationReadout_sum, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : reduceCharge D q.val = a
  · simp only [c, hq, ite_true, one_mul, inverseFlow_readout]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ell _ => ?_
    simp only [f, polynomialCoefficient_on_grade D hu hD M K L N E j ell q.val q.property
      P Q R S x y z d hx hy hz hd hP hQ hR hS]
  · simp [c, hq]

private theorem mixed_projection_eq_one (M K E : ℕ) (m : ℤ)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    projectionFactor (-1) ((M : ℤ) + (K : ℤ)) = 1 := by
  have ho : Odd ((M : ℤ) + (K : ℤ)) := ⟨(E : ℤ) + m - 2, by omega⟩
  rw [projectionFactor, neg_one_zpow_eq_ite, ite_eq_right (Int.not_even_iff_odd.mpr ho)]
  norm_num

set_option maxHeartbeats 4000000 in
-- The coevaluation rewrite elaborates the Leech charge and ground representations.
/-- The actual mixed Leech pair coefficient as the inverse-flow occupation
readout at the selected right Laurent exponent. -/
theorem mu_fourPoint_occupation_readout (s : Bool) (M K L N E : ℕ) (m eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (P Q R S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade leechData leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade leechData leechUnit N)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    actualForm leechData leechUnit (S ⊗ₜ[ℂ] d)
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff
          eR (R ⊗ₜ[ℂ] z)) =
      if eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) then
        ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3)) *
          ∑ a : ModTwoCharge leechData,
            (groundForm leechData leechUnit y
              (chargeOperator leechData (groundRepresentation leechData leechUnit) a x) *
            groundForm leechData leechUnit d
              (chargeOperator leechData (groundRepresentation leechData leechUnit) a z)) *
            occupationReadout leechData (inverseFlow leechData (M / 2 + 1) P)
              (inverseFlow leechData (K / 2 + 1) Q) R S (cosetChargeCoefficient leechData E a)
      else 0 := by
  classical
  by_cases heR : eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ)
  · rw [ite_eq_left heR,
      mu_fourPoint_gaussian_cosets s M K E m eR u v P Q R S x y z d hu hv huP hvQ hE,
      mixed_projection_eq_one M K E m hE, one_mul, heR]
    by_cases hx : x = 0
    · simp [hx, groundForm]
    by_cases hy : y = 0
    · simp [hy, groundForm]
    by_cases hz : z = 0
    · simp [hz, groundForm]
    by_cases hd : d = 0
    · simp [hd, groundForm]
    have hP : P ⊗ₜ[ℂ] x ∈ actualGrade leechData leechUnit M := huP ▸ hu
    have hQ : Q ⊗ₜ[ℂ] y ∈ actualGrade leechData leechUnit K := hvQ ▸ hv
    have hcoset (a : ModTwoCharge leechData) :=
      coset_lowering_eq_inverse_readout leechData leechUnit leech_spec.2.2.1
        M K L N E a P Q R S x y z d hx hy hz hd hP hQ hR hS
    simp only [hcoset]
  · rw [ite_eq_right heR]
    exact mu_fourPoint_off_right_grade s M K L N m (E : ℤ) eR u v
      (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d) hu hv hR hS hE heR

/-- The finite coset sum is the ordinary Taylor coefficient of the original
sewn charge sector at order `2 * E` in the sewing coordinate. -/
theorem cosetChargeCoefficient_eq_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (E : ℕ) (a : ModTwoCharge D)
    (β γ δ η : Exponent D) :
    cosetChargeCoefficient D E a β γ δ η =
      coefficient (2 * E) (chargeSectorSewn D a β γ δ η) := by
  classical
  let Charges := {q : Charge D // chargeEnergy D q ≤ E}
  let : Finite Charges := (chargeSublevel_finite D hD E).to_subtype
  let := Fintype.ofFinite Charges
  let charges : Set (Charge D) := {q | chargeEnergy D q ≤ E}
  let f (q : Charge D) : ℂ :=
    if reduceCharge D q = a then PowerSeries.coeff E (chargeSeries D q β γ δ η) else 0
  symm
  unfold chargeSectorSewn
  rw [sewn_charge_coefficient D hu hD, cosetChargeCoefficient,
    finsum_eq_sum_of_fintype]
  calc
    _ = ∑' q : Charge D, charges.indicator f q := by
      apply tsum_congr
      intro q
      by_cases hq : chargeEnergy D q ≤ E <;> by_cases ha : reduceCharge D q = a <;>
        simp [charges, f, Set.indicator, hq, ha]
    _ = ∑' q : Charges, f q := (tsum_subtype charges f).symm
    _ = ∑ q : Charges, f q := tsum_fintype (fun q : Charges => f q)

set_option maxHeartbeats 4000000 in
-- Discharge analyticity for the four nested finite sums.
private theorem occupationReadout_coset_eq_taylor (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (E : ℕ) (a : ModTwoCharge D)
    (P Q R S : Oscillator D) :
    occupationReadout D P Q R S (cosetChargeCoefficient D E a) =
      coefficient (2 * E) (fun ρ => occupationReadout D P Q R S
        (fun β γ δ η => chargeSectorSewn D a β γ δ η ρ)) := by
  have hsector (β γ δ η : Exponent D) :
      AnalyticAt ℂ (chargeSectorSewn D a β γ δ η) 0 :=
    chargeSectorSewn_analyticAt D hu hD a β γ δ η
  symm
  simp (discharger := fun_prop) only [occupationReadout, coefficient_fun_sum, coefficient_const_mul,
    cosetChargeCoefficient_eq_coefficient D hu hD E a]

set_option maxHeartbeats 4000000 in
-- Elaborate the coefficient rewrite under the Leech coset sum.
/-- The mixed coefficient in the analytic form of (T), with the ordinary
Taylor coefficient of each inverse-flow sewn occupation sector. -/
theorem mu_fourPoint_sewn_taylor (s : Bool) (M K L N E : ℕ) (m eR : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (P Q R S : Oscillator leechData) (x y z d : ActualGround leechData leechUnit)
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (hR : R ⊗ₜ[ℂ] z ∈ actualGrade leechData leechUnit L)
    (hS : S ⊗ₜ[ℂ] d ∈ actualGrade leechData leechUnit N)
    (hE : 2 * (E : ℤ) = (M : ℤ) + (K : ℤ) + 3 - 2 * m) :
    actualForm leechData leechUnit (S ⊗ₜ[ℂ] d)
        ((correctedField leechData leechUnit ((mu s u).coeff (-2 * m - 3) v).val).coeff
          eR (R ⊗ₜ[ℂ] z)) =
      if eR = (N : ℤ) - (L : ℤ) - 2 * (E : ℤ) then
        ((-1 : ℂ) ^ (E : ℤ) * Complex.I ^ ((K : ℤ) - 2 * (M : ℤ) - 3)) *
          ∑ a : ModTwoCharge leechData,
            (groundForm leechData leechUnit y
              (chargeOperator leechData (groundRepresentation leechData leechUnit) a x) *
            groundForm leechData leechUnit d
              (chargeOperator leechData (groundRepresentation leechData leechUnit) a z)) *
            coefficient (2 * E) (fun ρ =>
              occupationReadout leechData (inverseFlow leechData (M / 2 + 1) P)
                (inverseFlow leechData (K / 2 + 1) Q) R S
                (fun β γ δ η => chargeSectorSewn leechData a β γ δ η ρ))
      else 0 := by
  rw [mu_fourPoint_occupation_readout s M K L N E m eR u v P Q R S x y z d
    hu hv huP hvQ hR hS hE]
  simp only [occupationReadout_coset_eq_taylor leechData leechUnit leech_spec.2.2.1]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeDoubledOccupationReadout
