/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancellation of the native Gaussian discrepancy with the rank-24 charge sector. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMShiftedTheta
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity

/-! Finite Gaussian and charge-sector products in the original four-point charts. -/

set_option autoImplicit false

noncomputable section
open Complex Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChartProduct

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta (gramReal)
open OriginalFourMActualChart (Chart parameter periodRoot)
open OriginalFourMPeriodSource (dPeriod)
open OriginalFourMSignedOverlap (signedHalfSource covarianceMode taggedMode)
open OriginalGaussianSewnAnalytic (explicitMean)
open private chargeCovector_apply from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
open private chosenChartSource chartPuncture from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open OriginalFourMActualChart (pullB pullD)
open OriginalGaussianExternalSignedCandidate (G cauchy)
open OriginalGaussianExternalCandidateCore (rightChart leftChart)
open private nativeHalfX covOnChart from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open OriginalFourMShiftedTheta (chargeTheta chargeTheta_T chargeTheta_S)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private slit_of_re_lt doubleSlit_of_re chartA_mem dPeriod_ne_zero lipSign from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private quadraticSign_square from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

private abbrev pA (x : ℝ) : ℂ := slitPeriod (parameter .A (x : ℂ))
private abbrev pPf (x : ℝ) : ℂ := slitPeriod (1 - (x : ℂ))
private abbrev pB (x : ℝ) : ℂ := slitPeriod (x : ℂ)
private abbrev pD (upperA : Bool) (x : ℝ) : ℂ := dPeriod upperA (parameter .D (x : ℂ))

private abbrev bLift (x : ℝ) : ℂ := -I * (Real.sqrt x : ℂ)
private abbrev thetaSource (D : LatticeData) (p : ℂ) (M : Fin D.rank → ℂ) :
    Fin D.rank → ℂ := (I / (2 * (Real.pi : ℂ) * p)) • M

private def fourierRow (D : LatticeData) (a : ModTwoCharge D)
    (f : ModTwoCharge D → ℂ) : ℂ :=
  ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * f b

private theorem fourierRow_mul (D : LatticeData) (a : ModTwoCharge D) (c : ℂ)
    (f : ModTwoCharge D → ℂ) :
    fourierRow D a (fun b => c * f b) = c * fourierRow D a f := by
  unfold fourierRow
  simp only [mul_left_comm (fourierSign D a _), ← Finset.mul_sum]
  ring

private theorem fourierRow_quadratic_mul (D : LatticeData) (a : ModTwoCharge D)
    (c : ℂ) (f : ModTwoCharge D → ℂ) :
    c * fourierRow D a (fun b => quadraticSign D b * f b) =
      ((2 : ℂ)^ (12 : ℕ))⁻¹ *
        ∑ b, fourierSign D a b * quadraticSign D b * (c * f b) := by
  rw [← fourierRow_mul]
  unfold fourierRow
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem theta_neg_source (D : LatticeData) (hu : IsUnit D.G.det)
    (a : ModTwoCharge D) (τ : ℂ) (v : Fin D.rank → ℂ) :
    chargeTheta D hu a τ (-v) = chargeTheta D hu a τ v := by
  rw [OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum,
    OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum]
  have hneg (q : Charge D) : reduceCharge D (-q) = reduceCharge D q := by
    rw [map_neg]
    ext i
    exact ZMod.neg_eq_self_mod_two _
  let neg : {q : Charge D // reduceCharge D q = a} ≃
      {q : Charge D // reduceCharge D q = a} :=
    { toFun := fun q => ⟨-q.val, (hneg q.val).trans q.property⟩
      invFun := fun q => ⟨-q.val, (hneg q.val).trans q.property⟩
      left_inv := fun q => Subtype.ext (neg_neg q.val)
      right_inv := fun q => Subtype.ext (neg_neg q.val) }
  refine (neg.tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro q
  have hq : (fun i => (((-q.val) i : ℤ) : ℂ)) = -(fun i => (q.val i : ℂ)) := by
    ext i
    simp
  have hquad : bilinear D (-q.val) (-q.val) = bilinear D q.val q.val := by
    unfold bilinear
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.neg_apply]
    ring
  change Complex.exp (Real.pi * I * τ * (bilinear D (-q.val) (-q.val) : ℂ) / 2 +
    2 * Real.pi * I * ((D.G.map (Int.cast : ℤ → ℂ) *ᵥ
      (fun i => (((-q.val) i : ℤ) : ℂ))) ⬝ᵥ (-v))) = _
  rw [hquad, hq, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

private theorem theta_lip (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (a : ModTwoCharge D) (upperA : Bool)
    (τ : ℂ) (v : Fin D.rank → ℂ) :
    chargeTheta D hu a τ v =
      quadraticSign D a * chargeTheta D hu a (τ + lipSign upperA) v := by
  cases upperA
  · have ht := chargeTheta_T D hu hD a (τ - 1) v
    have he : τ - 1 + 1 = τ := by ring
    rw [he] at ht
    simpa [lipSign, sub_eq_add_neg] using ht
  · rw [show lipSign true = 1 by rfl, chargeTheta_T D hu hD, ← mul_assoc,
      quadraticSign_square, one_mul]

/-- A finite external sample uses the original two leg flags, half-coordinate,
and colour. The same puncture and colour may occur more than once. -/
structure Sample (D : LatticeData) where
  right : Bool
  outgoing : Bool
  q : ℂ
  colour : Fin D.rank

private def differential (D : LatticeData) (w : ℂ) (s : Sample D) : ℂ :=
  signedHalfSource s.right s.outgoing (s.q ^ 2) (w ^ 2)

private def sourceVector (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (m : X → ℂ) (i : Fin D.rank) : ℂ :=
  ∑ j, if (s j).colour = i then weights j * m j else 0

private def gram (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  D.G.map (Int.cast : ℤ → ℂ)

private def gaussianExponent (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (K : X → X → ℂ) : ℂ :=
  (∑ i, ∑ j, (weights i * weights j) * gram D (s i).colour (s j).colour * K i j) / 2

private theorem sourceVector_mul (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights m : X → ℂ) (c : ℂ) :
    sourceVector D s weights (fun j => c * m j) = c • sourceVector D s weights m := by
  ext i
  simp only [sourceVector, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split <;> ring

private theorem gaussianExponent_sub (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights m : X → ℂ) (K : X → X → ℂ) (c : ℂ) :
    gaussianExponent D s weights (fun i j => K i j - c * (m i * m j)) =
      gaussianExponent D s weights K -
        c * (sourceVector D s weights m ⬝ᵥ
          gram D *ᵥ sourceVector D s weights m) / 2 := by
  classical
  have hgram (j : X) (i : Fin D.rank) :
      ∑ k, gram D i k * (if (s j).colour = k then weights j * m j else 0) =
        gram D i (s j).colour * (weights j * m j) := by
    simp only [mul_ite, mul_zero]
    simp [eq_comm]
  have hvec (k : Fin D.rank) :
      (gram D *ᵥ sourceVector D s weights m) k =
        ∑ j, gram D k (s j).colour * (weights j * m j) := by
    simp only [mulVec, dotProduct, sourceVector, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hgram j k)
  have hsum :
      sourceVector D s weights m ⬝ᵥ gram D *ᵥ sourceVector D s weights m =
        ∑ i, ∑ j, weights i * weights j * gram D (s i).colour (s j).colour *
          (m i * m j) := by
    unfold dotProduct
    simp only [hvec, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ i, weights i * weights j * gram D (s i).colour (s j).colour *
          (m i * m j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [sourceVector, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_eq_single (s i).colour]
        · simp only [ite_true]
          ring
        · intro k _ hk
          simp [Ne.symm hk]
        · simp
      _ = _ := Finset.sum_comm
  have hcorrection :
      (∑ i, ∑ j, (weights i * weights j) * gram D (s i).colour (s j).colour *
          (c * (m i * m j))) = c * (sourceVector D s weights m ⬝ᵥ
            gram D *ᵥ sourceVector D s weights m) := by
    rw [hsum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [gaussianExponent, mul_sub, Finset.sum_sub_distrib, hcorrection, sub_div]

private def nativeCovariance (D : LatticeData) {X : Type*} (s : X → Sample D)
    (w : ℂ) (i j : X) : ℂ :=
  covarianceMode (s i).right (s j).right (s i).outgoing (s j).outgoing
    ((s i).q ^ 2) ((s j).q ^ 2) (w ^ 2)

private def chartScale (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => 1
  | .B => (bLift x)⁻¹
  | .D => I⁻¹

private def chartPeriod (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => pA x
  | .B => pB x
  | .D => pD upperA x

private def chartTau (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => I * pD upperA x / pA x
  | .B => -1 / (I * pB x / pPf x)
  | .D => -1 / (I * pD upperA x / pA x)

private def chartDifference (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => 0
  | .B => 1 / ((Real.pi : ℂ) * pPf x * pB x)
  | .D => 1 / ((Real.pi : ℂ) * pA x * pD upperA x)

private def pulledDifferential (D : LatticeData) (c : Chart) (x : ℝ) (w : ℂ)
    (s : Sample D) : ℂ := chartScale c x * differential D w s

private def pulledCovariance (D : LatticeData) {X : Type*} (s : X → Sample D)
    (upperA : Bool) (c : Chart) (x : ℝ) (w : ℂ) (i j : X) : ℂ :=
  nativeCovariance D s w i j - chartDifference upperA c x *
    (pulledDifferential D c x w (s i) * pulledDifferential D c x w (s j))

/-- Period-normalized finite generator in the common native A coordinates.
The B and D covariances use the common A free subtraction, with their
holomorphic differential correction in the target chart units. -/
def chartProduct (D : LatticeData) (hu : IsUnit D.G.det) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (upperA : Bool) (x : ℝ) (w : ℂ)
    (c : Chart) (a : ModTwoCharge D) : ℂ :=
  let p := chartPeriod upperA c x
  let M := sourceVector D s weights (fun i => pulledDifferential D c x w (s i))
  (p ^ (12 : ℕ))⁻¹ * Complex.exp (gaussianExponent D s weights
    (pulledCovariance D s upperA c x w)) *
    chargeTheta D hu a (chartTau upperA c x) (thetaSource D p M)

/-- Off the geometric poles the pulled covariance is the target elliptic
kernel evaluated with the target differential and the common A subtraction.
It includes the native mixed free term through the signed overlap identity. -/
theorem pulled_covariance_off_diagonal (D : LatticeData) {X : Type*}
    (s : X → Sample D) (i j : X) (upperA : Bool) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ))
    (hu : ‖(s i).q ^ 2‖ + ‖w‖ < 1) (hv : ‖(s j).q ^ 2‖ + ‖w‖ < 1)
    (hq : (s i).q ≠ 0) (hQ : (s j).q ≠ 0) (hw : w ≠ 0)
    (hg : G (s i).outgoing (s j).outgoing ((s i).q ^ 2) ((s j).q ^ 2) ≠ 0)
    (hr : rightChart (s i).outgoing ((s i).q ^ 2) - 1 ≠ 0)
    (hR : rightChart (s j).outgoing ((s j).q ^ 2) - 1 ≠ 0)
    (hrr : rightChart (s i).outgoing ((s i).q ^ 2) -
      rightChart (s j).outgoing ((s j).q ^ 2) ≠ 0)
    (hcross : rightChart (s i).outgoing ((s i).q ^ 2) -
      leftChart (s j).outgoing (w ^ 2) ((s j).q ^ 2) ≠ 0) :
    let u := nativeHalfX (s i).right (s i).outgoing (w ^ 2) (s i).q
    let v := nativeHalfX (s j).right (s j).outgoing (w ^ 2) (s j).q
    let free := if (s i).right = (s j).right ∧ (s i).outgoing = (s j).outgoing then
      cauchy (s i).outgoing (s j).outgoing ((s i).q ^ 2) ((s j).q ^ 2) else 0
    ((x : ℂ) * u - 1 ≠ 0) → ((x : ℂ) * v - 1 ≠ 0) → (u - v ≠ 0) →
    pulledCovariance D s upperA .B x w i j + free =
      (pulledDifferential D .B x w (s i) * pulledDifferential D .B x w (s j)) *
        covOnChart upperA .B x (pullB x u) (pullB x v) ∧
    pulledCovariance D s upperA .D x w i j + free =
      (pulledDifferential D .D x w (s i) * pulledDifferential D .D x w (s j)) *
        covOnChart upperA .D x (pullD x u) (pullD x v) := by
  dsimp only
  intro hu₁ hv₁ huv
  obtain ⟨hB, hD⟩ := OriginalFourMSignedOverlap.native_A_covariance_discrepancy upperA
    (s i).right (s j).right (s i).outgoing (s j).outgoing hx hx1 hwA
    hu hv hq hQ hw hg hr hR hrr hcross hu₁ hv₁ huv
  have hs : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hb : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs
  have res (k free m n c corr target : ℂ) (hc : c ≠ 0)
      (he : c^2 * (k + free) - m * n * target = m * n * corr) :
      k - corr * (c⁻¹ * m * (c⁻¹ * n)) + free =
        c⁻¹ * m * (c⁻¹ * n) * target := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hc))
    field_simp [hc]
    linear_combination he
  constructor
  · apply res _ _ _ _ (bLift x) _ _ hb
    simpa only [pulledDifferential, chartScale, nativeCovariance, differential,
      chartDifference, bLift, div_eq_mul_inv, one_mul] using hB
  · apply res _ _ _ _ I _ _ I_ne_zero
    simpa only [pulledDifferential, chartScale, nativeCovariance, differential,
      chartDifference, hwA, div_eq_mul_inv, one_mul] using hD

/-- The source attached to each native sample in the A exponential is the
sum of the actual two-leg charge means. -/
theorem native_sample_mean (D : LatticeData) (a : Charge D) (s : Sample D)
    {w : ℂ} (hw : ‖s.q ^ 2‖ + ‖w‖ < 1) :
    HasSum (fun n : ℕ =>
      explicitMean D a (fun _ : Unit => (s.outgoing, s.colour, n)) w
        (taggedMode s.right ()) * (s.q ^ 2) ^ n)
      (-(bilinear D (unitCharge D s.colour) a : ℂ) * differential D w s /
        slitPeriod (w ^ 2)) :=
  OriginalFourMSignedOverlap.native_mean_hasSum D a s.right s.outgoing s.colour hw

/-- The pullback used in the product carries the physical signs of the four
chosen source germs. The D root follows the corresponding period lip. -/
theorem physical_source_signs {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (lA eA lB eB lD eD : Bool)
    (hB : chartPuncture .A lA eA = chartPuncture .B lB eB)
    (hD : chartPuncture .A lA eA = chartPuncture .D lD eD) :
    let A := OriginalFourMActualChart.halfDifferentialAt .A x (chartPuncture .A lA eA)
    chartScale .B x * A =
      OriginalFourMActualChart.relativeB (chartPuncture .A lA eA) *
        OriginalFourMActualChart.halfDifferentialAt .B x (chartPuncture .B lB eB) ∧
    chartScale .D x * A =
      OriginalFourMActualChart.relativeD (chartPuncture .A lA eA) *
        OriginalFourMActualChart.halfDifferentialAt .D x (chartPuncture .D lD eD) := by
  obtain ⟨hb, hd⟩ := OriginalFourMSignedOverlap.chart_chosen_source_signs hx hx1
    lA eA lB eB lD eD hB hD
  dsimp only at hb hd ⊢
  simp only [OriginalFourMSignedOverlap.chart_source_at_puncture hx hx1] at hb hd
  have hs : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hl : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs
  have cancel (c s t : ℂ) (hc : c ≠ 0) : c⁻¹ * (c * s * t) = s * t := by
    rw [mul_assoc c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  constructor
  · rw [chartScale, hb]
    exact cancel (bLift x) _ _ hl
  · rw [chartScale, hd]
    exact cancel I _ _ I_ne_zero

private theorem linear_source (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights m : X → ℂ) (q : Charge D) {p : ℂ} (hp : p ≠ 0) :
    2 * Real.pi * I * ((gram D *ᵥ (fun i => (q i : ℂ))) ⬝ᵥ
        thetaSource D p (sourceVector D s weights m)) =
      ∑ j, weights j * (-(bilinear D (unitCharge D (s j).colour) q : ℂ) * m j / p) := by
  change 2 * Real.pi * I * ((gram D *ᵥ (fun i => (q i : ℂ))) ⬝ᵥ
    ((I / (2 * (Real.pi : ℂ) * p)) • sourceVector D s weights m)) = _
  rw [dotProduct_smul, smul_eq_mul, ← mul_assoc]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscalar : 2 * Real.pi * I * (I / (2 * (Real.pi : ℂ) * p)) = -1 / p := by
    field_simp [hπ, hp]
    ring_nf
    simp [I_sq]
  rw [hscalar]
  simp only [dotProduct, sourceVector, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (s j).colour]
  · simp only [ite_true]
    rw [show (gram D *ᵥ (fun i => (q i : ℂ))) (s j).colour =
      (bilinear D (unitCharge D (s j).colour) q : ℂ) from
       (chargeCovector_apply D q (s j).colour).1]
    ring
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- The generating product is a sum over the literal mod-two charge fiber,
with the signed transported linear means and the same quadratic exponent
in every lattice summand. -/
theorem chart_product_charge_sum (D : LatticeData) (hu : IsUnit D.G.det)
    {X : Type*} [Fintype X] (s : X → Sample D) (weights : X → ℂ)
    (upperA : Bool) (c : Chart) (x : ℝ) (w : ℂ) (a : ModTwoCharge D)
    (hp : chartPeriod upperA c x ≠ 0) :
    let p := chartPeriod upperA c x
    let E := gaussianExponent D s weights (pulledCovariance D s upperA c x w)
    chartProduct D hu s weights upperA x w c a =
      (p ^ (12 : ℕ))⁻¹ * ∑' q : {q : Charge D // reduceCharge D q = a},
        Complex.exp (E + (Real.pi * I * chartTau upperA c x *
            (bilinear D q.val q.val : ℂ) / 2 +
          ∑ j, weights j * (-(bilinear D (unitCharge D (s j).colour) q.val : ℂ) *
            pulledDifferential D c x w (s j) / p))) := by
  unfold chartProduct
  dsimp only
  rw [OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum, mul_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro q
  have h := linear_source D s weights (fun i => pulledDifferential D c x w (s i)) q.val hp
  unfold gram at h
  rw [h, ← Complex.exp_add]

private theorem normalize_complement (p q E δ : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (q ^ (12 : ℕ))⁻¹ * Complex.exp (E - δ) *
        ((-I * (I * q / p)) ^ (12 : ℕ) * Complex.exp δ) =
      (p ^ (12 : ℕ))⁻¹ * Complex.exp E := by
  have hratio : -I * (I * q / p) = q / p := by
    rw [← mul_div_assoc, neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg]
  rw [hratio, div_pow, Complex.exp_sub]
  field_simp [Complex.exp_ne_zero, hp, hq]

/-- Rank-24 oscillator determinant on its actual open disk, in the
integer-power normalization used by the chart product. -/
theorem native_rank24_determinant {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.exp (-12 * OriginalGaussianDeterminant.gaussianLogDet w) =
      ((1 - w ^ 2) ^ (3 : ℕ))⁻¹ * (slitPeriod (w ^ 2) ^ (12 : ℕ))⁻¹ := by
  have hw2 : ‖w ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have h0 : 1 - w ^ 2 ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hw2
    exact (lt_irrefl _) hw2
  have he : (Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - w^2))) ^ (12 : ℕ) =
      (1 - w^2) ^ (3 : ℕ) := by
    calc
      _ = Complex.exp ((3 : ℂ) * Complex.log (1 - w^2)) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = _ := by
        rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul,
          Complex.exp_log h0]
  rw [show (-12 : ℂ) = -(↑(12 : ℕ) : ℂ) by norm_num, neg_mul, Complex.exp_neg,
    Complex.exp_nat_mul, ← OriginalGaussianDeterminant.gaussianDet,
    OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity hw,
    mul_pow, he, mul_inv, slitPeriod_eq_period hw2]

set_option maxHeartbeats 400000 in
-- The two complex source substitutions and finite Fourier normalization share this proof.
/-- The complementary S law cancels the signed Gaussian correction at D.
The B path uses Pfaff translation followed by complementary S. This
comparison keeps every charge sector and every finite external weight. -/
theorem native_chart_product (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (w : ℂ) (a : ModTwoCharge D) :
    let A := chartProduct D hu s weights upperA x w .A
    let B := chartProduct D hu s weights upperA x w .B
    let C := chartProduct D hu s weights upperA x w .D
    C a = ((2 : ℂ)^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * A b) ∧
    B a = ((periodRoot .A x) ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ)^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * A b) := by
  let m := fun i => differential D w (s i)
  let M := sourceVector D s weights m
  let MB := sourceVector D s weights (fun i => (bLift x)⁻¹ * m i)
  let MD := sourceVector D s weights (fun i => I⁻¹ * m i)
  let E := gaussianExponent D s weights (nativeCovariance D s w)
  let δB := (1 / ((Real.pi : ℂ) * pPf x * pB x)) * (MB ⬝ᵥ gram D *ᵥ MB) / 2
  let δD := (1 / ((Real.pi : ℂ) * pA x * pD upperA x)) * (MD ⬝ᵥ gram D *ᵥ MD) / 2
  let tB := I * pB x / pPf x
  let tD := I * pD upperA x / pA x
  have hA := slitPeriod_ne_zero (chartA_mem hx)
  have hP := slitPeriod_ne_zero (r := 1 - (x : ℂ))
    (slit_of_re_lt (by simpa [sub_re] using hx))
  have hB := slitPeriod_ne_zero (r := (x : ℂ)) (slit_of_re_lt (by simpa using hx1))
  have hD₀ : pD upperA x ≠ 0 := by
    change dPeriod upperA ((x : ℂ)⁻¹) ≠ 0
    simpa only [ofReal_inv] using dPeriod_ne_zero upperA ((one_lt_inv₀ hx).2 hx1)
  have hp : pPf x = periodRoot .A x * pA x := OriginalFourMPeriodSource.chartB_pfaff_period hx
  have hs : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hl : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have htB : 0 < tB.im := by
    have ht := tau_im_pos (doubleSlit_of_re (r := 1 - (x : ℂ))
      (by simpa [sub_re] using sub_pos.mpr hx1)
      (by simpa [sub_re] using hx))
    simpa only [tau, sub_sub_cancel] using ht
  have hDt : tD = tB + lipSign upperA := by
    change I * dPeriod upperA ((x : ℂ)⁻¹) / pA x = _
    rw [dPeriod, inv_inv]
    change I * ((tau (1 - (x : ℂ)) + lipSign upperA) * pA x / I) / pA x = _
    rw [tau, sub_sub_cancel]
    change I * ((tB + lipSign upperA) * pA x / I) / pA x = _
    field_simp [hA, I_ne_zero]
  have htD : 0 < tD.im := by
    rw [hDt]
    cases upperA <;> simpa [lipSign, add_im] using htB
  have hMB : MB = (bLift x)⁻¹ • M := sourceVector_mul D s weights m _
  have hMD : MD = I⁻¹ • M := sourceVector_mul D s weights m _
  let zA := thetaSource D (pA x) M
  have hzD : (I / (2 * (Real.pi : ℂ) * pA x) * I) • MD = zA := by
    rw [hMD, smul_smul]
    congr 1
    field_simp [I_ne_zero]
  have hzB : (I / (2 * (Real.pi : ℂ) * pPf x) * (periodRoot .A x * bLift x)) • MB = zA := by
    rw [hMB, smul_smul]
    congr 1
    rw [hp]
    have hp0 : periodRoot .A x ≠ 0 := by
      change (Real.sqrt x : ℂ)⁻¹ ≠ 0
      exact inv_ne_zero hs
    field_simp [hA, hl, hp0, hπ]
  have hzSD : tD⁻¹ • zA = thetaSource D (pD upperA x) MD := by
    rw [← hzD, smul_smul]
    congr 1
    dsimp [tD]
    field_simp [I_ne_zero, hA, hD₀, hπ]
  have hzSB : tB⁻¹ • zA = -thetaSource D (pB x) MB := by
    rw [← hzB, smul_smul, ← neg_smul]
    congr 1
    have he : periodRoot .A x * bLift x = -I := by
      change (Real.sqrt x : ℂ)⁻¹ * (-I * (Real.sqrt x : ℂ)) = _
      field_simp [hs]
    rw [he]
    dsimp [tB]
    field_simp [I_ne_zero, hP, hB, hπ]
  obtain ⟨heB, heD⟩ := OriginalFourMShiftedTheta.chart_source_multipliers upperA hx hx1 D MB MD
  dsimp only at heB heD
  rw [hzB] at heB
  rw [hzD] at heD
  have hd := chargeTheta_S D hu hD hr a tD htD zA
  have hb := chargeTheta_S D hu hD hr a tB htB zA
  have heD' := heD
  have heB' := heB
  change _ = Complex.exp δD at heD'
  change _ = Complex.exp δB at heB'
  rw [hzSD, heD'] at hd
  rw [hzSB, theta_neg_source, heB'] at hb
  have hphase (b : ModTwoCharge D) :
      chargeTheta D hu b tB zA = quadraticSign D b * chargeTheta D hu b tD zA := by
    rw [hDt]
    exact theta_lip D hu hD b upperA tB zA
  have hformA (b : ModTwoCharge D) :
      chartProduct D hu s weights upperA x w .A b =
        ((pA x)^ (12 : ℕ))⁻¹ * Complex.exp E * chargeTheta D hu b tD zA := by
    unfold chartProduct pulledCovariance pulledDifferential
    simp only [chartPeriod, chartTau, chartDifference, chartScale, one_mul, zero_mul, sub_zero]
    rfl
  have hformD :
      chartProduct D hu s weights upperA x w .D a =
        ((pD upperA x)^ (12 : ℕ))⁻¹ * Complex.exp (E - δD) *
          chargeTheta D hu a (-1 / tD) (thetaSource D (pD upperA x) MD) := by
    unfold chartProduct pulledCovariance pulledDifferential
    dsimp only [chartPeriod, chartScale, chartDifference, chartTau]
    rw [gaussianExponent_sub]
  have hformB :
      chartProduct D hu s weights upperA x w .B a =
        ((pB x)^ (12 : ℕ))⁻¹ * Complex.exp (E - δB) *
          chargeTheta D hu a (-1 / tB) (thetaSource D (pB x) MB) := by
    unfold chartProduct pulledCovariance pulledDifferential
    dsimp only [chartPeriod, chartScale, chartDifference, chartTau]
    rw [gaussianExponent_sub]
  dsimp only
  simp only [hformA]
  constructor
  · have hnorm : ((pD upperA x)^ (12 : ℕ))⁻¹ * Complex.exp (E - δD) *
        ((-I * tD)^ (12 : ℕ) * Complex.exp δD) =
          ((pA x)^ (12 : ℕ))⁻¹ * Complex.exp E :=
      normalize_complement _ _ _ _ hA hD₀
    rw [hformD, hd, ← mul_assoc _ (_ * _), hnorm]
    exact (fourierRow_mul D a _ _).symm
  · have hnorm : ((pB x)^ (12 : ℕ))⁻¹ * Complex.exp (E - δB) *
        ((-I * tB)^ (12 : ℕ) * Complex.exp δB) =
          ((pPf x)^ (12 : ℕ))⁻¹ * Complex.exp E :=
      normalize_complement _ _ _ _ hP hB
    rw [hformB, hb, ← mul_assoc _ (_ * _), hnorm]
    simp only [hphase]
    have he : ((pPf x) ^ (12 : ℕ))⁻¹ * Complex.exp E =
        ((periodRoot .A x) ^ (12 : ℕ))⁻¹ *
          (((pA x) ^ (12 : ℕ))⁻¹ * Complex.exp E) := by
      rw [hp, mul_pow, mul_inv, mul_assoc]
    have hrow := fourierRow_quadratic_mul D a
      (((pA x)^ (12 : ℕ))⁻¹ * Complex.exp E) (fun b => chargeTheta D hu b tD zA)
    unfold fourierRow at hrow
    rw [he, mul_assoc, hrow]

open OriginalFourMDiscriminantCharge (doubled sectorEquiv)
open LatticeDiscriminantTheta (Discriminant pairingCharacter phase quadraticClass)
open LatticeDiscriminantWeil (rho weilS weilT)
open LatticeDiscriminantTheta (dual_lattice_realization)
open private doubled_posDef sqrt_det_doubled pairing_sign reduction_surjective from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMShiftedTheta

private theorem fourier_from_D (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24) (f : ModTwoCharge D → ℂ)
    (a : ModTwoCharge D) :
    fourierRow D a (fun b => quadraticSign D b * f b) =
      ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
        ∑ b, quadraticSign D (a + b) * fourierRow D b f := by
  let d := doubled D
  let hd := doubled_posDef D hD
  let : Fact (gramReal d).PosDef := ⟨hd⟩
  let : Fintype (Discriminant d) := Fintype.ofFinite _
  let e := sectorEquiv D hu
  let S := weilS d
  let T := weilT d
  have hρ : rho d = (2 : ℂ) ^ (12 : ℕ) := by
    unfold rho
    rw [(dual_lattice_realization d hd).2.2.1]
    exact sqrt_det_doubled D hu hd hr
  have hneg (b : ModTwoCharge D) : -(e b) = e b := by
    rw [← map_neg]
    congr 1
    ext i
    exact ZMod.neg_eq_self_mod_two _
  have hS (g : Discriminant d → ℂ) (b : ModTwoCharge D) :
      S g (e b) = fourierRow D b (fun c => g (e c)) := by
    change (rho d)⁻¹ * (∑ c : Discriminant d, pairingCharacter d hd (e b) (-c) * g c) = _
    rw [hρ, ← e.toEquiv.sum_comp (fun c => pairingCharacter d hd (e b) (-c) * g c)]
    unfold fourierRow
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    change pairingCharacter d hd (e b) (-(e c)) * g (e c) = _
    rw [hneg, pairing_sign D hu hd]
  have hQ (b : ModTwoCharge D) : phase (quadraticClass d (e b)) = quadraticSign D b := by
    obtain ⟨q, rfl⟩ := reduction_surjective D b
    exact OriginalFourMShiftedTheta.quadratic_phase_reduceCharge D hu hd q
  have hT (g : Discriminant d → ℂ) (b : ModTwoCharge D) :
      T g (e b) = quadraticSign D b * g (e b) := by
    change phase (quadraticClass d (e b)) * _ = _
    rw [hQ]
  have hT2 (g : Discriminant d → ℂ) : T (T g) = g := by
    funext b
    obtain ⟨c, rfl⟩ := e.surjective b
    rw [hT, hT, ← mul_assoc, quadraticSign_square, one_mul]
  obtain ⟨hs, hst⟩ := OriginalFourMShiftedTheta.original_finite_weil D hu hD hr
  have hS2 (g : Discriminant d → ℂ) : S (S g) = g :=
    LinearMap.congr_fun hs g
  have hcube (g : Discriminant d → ℂ) : S (T (S (T (S (T g))))) = g :=
    LinearMap.congr_fun hst g
  have hbraid (g : Discriminant d → ℂ) : S (T (S g)) = T (S (T g)) := by
    have h := congrArg (fun v => T (S v)) (hcube (T g))
    rwa [hS2, hT2, hT2] at h
  let g : Discriminant d → ℂ := fun b => f (e.symm b)
  have h := congrFun (hbraid (S g)) (e a)
  rw [hS2] at h
  simp only [hS, hT, g, AddEquiv.symm_apply_apply] at h
  rw [h]
  unfold fourierRow
  rw [← mul_assoc, mul_comm (quadraticSign D a), mul_assoc, Finset.mul_sum]
  apply congrArg (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro b _
  rw [OriginalFourMChargeCoset.quadraticSign_add]
  ring

/-- The D-to-B comparison has the original quadratic character at the
sum of the two sectors, with the Pfaff period-root power on the B side. -/
theorem chart_product_B_from_D (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (w : ℂ) (a : ModTwoCharge D) :
    (periodRoot .A x) ^ (12 : ℕ) * chartProduct D hu s weights upperA x w .B a =
      ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, quadraticSign D (a + b) *
        chartProduct D hu s weights upperA x w .D b := by
  have hp : periodRoot .A x ≠ 0 :=
    inv_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne')
  let f := chartProduct D hu s weights upperA x w .A
  have hd (b : ModTwoCharge D) :
      chartProduct D hu s weights upperA x w .D b = fourierRow D b f :=
    (native_chart_product D hu hD hr s weights upperA hx hx1 w b).1
  have hb := (native_chart_product D hu hD hr s weights upperA hx hx1 w a).2
  rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), one_mul]
  simp only [hd]
  have h := fourier_from_D D hu hD hr f a
  unfold fourierRow at h ⊢
  simpa only [mul_assoc, f] using h

open OriginalFourMActualChart
  (Puncture scale scaleRoot loweringParameter localCoordinate cubic)
open private nativeHalfY legendre from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private transition_slopes scale_ne from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

/-- At a nonpunctured native sample the sources in the B and D product
are the actual pullbacks of the two elliptic half-differentials. -/
theorem pulled_sample_differentials (D : LatticeData) (s : Sample D)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A (x : ℂ)) (hw : w ≠ 0)
    (hq : s.q ≠ 0) (hsmall : ‖s.q ^ 2‖ + ‖w ^ 2‖ < 1)
    (hX : (x : ℂ) * nativeHalfX s.right s.outgoing (w ^ 2) s.q - 1 ≠ 0) :
    let X := nativeHalfX s.right s.outgoing (w ^ 2)
    let y := nativeHalfY s.right s.outgoing (w ^ 2) s.q
    let yB := bLift x * deriv (pullB x) (X s.q) * y
    let yD := I * deriv (pullD x) (X s.q) * y
    (yB ^ 2 = cubic .B x (pullB x (X s.q)) ∧
      HasDerivAt (fun q => pullB x (X q)) (2 * yB * pulledDifferential D .B x w s) s.q) ∧
    (yD ^ 2 = cubic .D x (pullD x (X s.q)) ∧
      HasDerivAt (fun q => pullD x (X q)) (2 * yD * pulledDifferential D .D x w s) s.q) := by
  dsimp only
  obtain ⟨hcurve, hy, hder⟩ := OriginalFourMSignedOverlap.half_coordinate_pullback
    s.right s.outgoing hq (pow_ne_zero 2 hw) hsmall
  have hc : nativeHalfY s.right s.outgoing (w ^ 2) s.q ^ 2 =
      cubic .A x (nativeHalfX s.right s.outgoing (w ^ 2) s.q) := by
    change _ = legendre (parameter .A (x : ℂ)) _
    convert hcurve using 1
    rw [hwA]
  obtain ⟨hB, hD, _, _⟩ := OriginalFourMActualChart.chart_lifts hx hx1 hX hc hy
  have hslopes := transition_slopes hX
  have hs : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hl : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs
  refine ⟨⟨hB, (hslopes.1.comp s.q hder).congr_deriv ?_⟩,
    ⟨hD, (hslopes.2.comp s.q hder).congr_deriv ?_⟩⟩
  · rw [← hslopes.1.deriv, pulledDifferential, chartScale, differential]
    field_simp [hl] <;> ring
  · rw [← hslopes.2.deriv, pulledDifferential, chartScale, differential]
    field_simp [I_ne_zero] <;> ring

private def rawLocal (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  u / (scale c x i + loweringParameter c i * u)

private def freeCorrection (c : Chart) (i : Puncture) (b d : ℂ) : ℂ :=
  loweringParameter c i * (1 + b * d) / (2*b * d*(b + d)^2)

private def halfJacobian (c : Chart) (x : ℝ) (i : Puncture) (b : ℂ) : ℂ :=
  scaleRoot c x i / b ^ 3

/-- In common physical coordinates the regular discrepancy of the native
same-puncture free subtractions is exactly the difference of their two
lowering corrections. This applies to every physical puncture and any
pair of the three charts. -/
theorem physical_free_subtraction_difference (D : LatticeData) (hu : IsUnit D.G.det)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c C : Chart) (i : Puncture)
    (e E : Bool) {u v b d B H : ℂ}
    (hcu : scale c x i + loweringParameter c i * u ≠ 0)
    (hcv : scale c x i + loweringParameter c i * v ≠ 0)
    (hCu : scale C x i + loweringParameter C i * u ≠ 0)
    (hCv : scale C x i + loweringParameter C i * v ≠ 0)
    (huv : u ≠ v)
    (hb : b ^ 2 = 1 - loweringParameter c i * rawLocal c x i u)
    (hd : d ^ 2 = 1 - loweringParameter c i * rawLocal c x i v)
    (hB : B ^ 2 = 1 - loweringParameter C i * rawLocal C x i u)
    (hH : H ^ 2 = 1 - loweringParameter C i * rawLocal C x i v)
    (hb₀ : b ≠ 0) (hd₀ : d ≠ 0) (hB₀ : B ≠ 0) (hH₀ : H ≠ 0)
    (hbd : b + d ≠ 0) (hBH : B + H ≠ 0) :
    let J := halfJacobian c x i b * halfJacobian c x i d
    let K := halfJacobian C x i B * halfJacobian C x i H
    cauchy E E (rawLocal C x i u) (rawLocal C x i v) / K -
        cauchy e e (rawLocal c x i u) (rawLocal c x i v) / J =
      freeCorrection c i b d / J - freeCorrection C i B H / K := by
  have step (a : Chart) (f : Bool) {p q : ℂ}
      (hu₀ : scale a x i + loweringParameter a i * u ≠ 0)
      (hv₀ : scale a x i + loweringParameter a i * v ≠ 0)
      (hp : p ^ 2 = 1 - loweringParameter a i * rawLocal a x i u)
      (hq : q ^ 2 = 1 - loweringParameter a i * rawLocal a x i v)
      (hp₀ : p ≠ 0) (hq₀ : q ≠ 0) (hpq : p + q ≠ 0) :
      let J := halfJacobian a x i p * halfJacobian a x i q
      cauchy f f (rawLocal a x i u) (rawLocal a x i v) / J +
        freeCorrection a i p q / J = (u + v)/(2*(u - v)^2) := by
    dsimp only
    have hlocal := (OriginalFourMActualChart.puncture_lowering hx hx1 D hu a i 0 0).1
    have h1 : localCoordinate a x i (rawLocal a x i u) = u := hlocal u hu₀
    have h2 : localCoordinate a x i (rawLocal a x i v) = v := hlocal v hv₀
    have hsep : rawLocal a x i u ≠ rawLocal a x i v := by
      intro he
      exact huv (h1.symm.trans ((congrArg (localCoordinate a x i) he).trans h2))
    have hc := OriginalFourMActualChart.puncture_cauchy_correction hx hx1 a i
      hp hq hp₀ hq₀ hpq hsep
    dsimp only at hc
    rw [h1, h2] at hc
    have hroot : scaleRoot a x i ≠ 0 := by
      intro he
      have hs := (OriginalFourMActualChart.chosen_roots hx hx1 a i).1
      rw [he, zero_pow (by decide)] at hs
      exact scale_ne hx hx1 a i hs.symm
    have hJ : halfJacobian a x i p * halfJacobian a x i q ≠ 0 :=
      mul_ne_zero (div_ne_zero hroot (pow_ne_zero _ hp₀))
        (div_ne_zero hroot (pow_ne_zero _ hq₀))
    rw [← add_div, div_eq_iff hJ]
    simp only [cauchy, OriginalGaussianExternalSignedCandidate.G,
      OriginalGaussianExternalSignedCandidate.rho, ite_true, halfJacobian, freeCorrection]
    linear_combination -hc
  dsimp only
  have h := step c e hcu hcv hb hd hb₀ hd₀ hbd
  have h' := step C E hCu hCv hB hH hB₀ hH₀ hBH
  dsimp only at h h'
  linear_combination h' - h

#print axioms pulled_covariance_off_diagonal
#print axioms chart_product_charge_sum
#print axioms native_rank24_determinant
#print axioms native_chart_product
#print axioms chart_product_B_from_D
#print axioms pulled_sample_differentials
#print axioms physical_free_subtraction_difference

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChartProduct
