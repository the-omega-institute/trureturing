/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancellation of the native Gaussian discrepancy with the rank-24 charge sector. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedCovariance
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMShiftedTheta

/-! Finite Gaussian and charge-sector products in the original four-point charts. -/

set_option autoImplicit false

noncomputable section
open Complex Matrix
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChartProduct

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticeDiscriminantTheta (gramReal)
open LatticeDiscriminantShiftedTheta (sourceQuadratic)
open LatticeHalfFock (gramComplex)
open FourPoint.OriginalFourMActualChart (Chart parameter periodRoot)
open OriginalFourMPeriodSource (dPeriod dPeriod_ne_zero lipSign chart_source_exponents)
open OriginalFourMSignedOverlap (signedHalfSource covarianceMode)
open OriginalFourMShiftedTheta (chargeTheta chargeTheta_T chargeTheta_S chargeTheta_neg_source
  doubled sourceQuadratic_doubled fourierRow)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

private abbrev pA (x : ℝ) : ℂ := slitPeriod (parameter .A (x : ℂ))
private abbrev pPf (x : ℝ) : ℂ := slitPeriod (1 - (x : ℂ))
private abbrev pB (x : ℝ) : ℂ := slitPeriod (x : ℂ)
private abbrev pD (upperA : Bool) (x : ℝ) : ℂ := dPeriod upperA (parameter .D (x : ℂ))

private abbrev bLift (x : ℝ) : ℂ := -I * (Real.sqrt x : ℂ)
/-- The source vector in the shifted theta argument for period `p`. -/
abbrev thetaSource (D : LatticeData) (p : ℂ) (M : Fin D.rank → ℂ) :
    Fin D.rank → ℂ := (I / (2 * (Real.pi : ℂ) * p)) • M

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
      show quadraticSign D a * quadraticSign D a = 1 from
        LatticeTwistedGroundRealization.sign_square _, one_mul]

/-- A finite external sample uses the original two leg flags, half-coordinate,
and colour. The same puncture and colour may occur more than once. -/
structure Sample (D : LatticeData) where
  right : Bool
  outgoing : Bool
  q : ℂ
  colour : Fin D.rank

/-- The signed original A differential at a native sample. -/
def differential (D : LatticeData) (w : ℂ) (s : Sample D) : ℂ :=
  signedHalfSource s.right s.outgoing (s.q ^ 2) (w ^ 2)

/-- Collect the weighted signed sources by lattice colour. -/
def sourceVector (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (m : X → ℂ) (i : Fin D.rank) : ℂ :=
  ∑ j, if (s j).colour = i then weights j * m j else 0

/-- The Gram-weighted quadratic exponent for a finite covariance. -/
def gaussianExponent (D : LatticeData) {X : Type*} [Fintype X]
    (s : X → Sample D) (weights : X → ℂ) (K : X → X → ℂ) : ℂ :=
  (∑ i, ∑ j, (weights i * weights j) * gramComplex D (s i).colour (s j).colour * K i j) / 2

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
          gramComplex D *ᵥ sourceVector D s weights m) / 2 := by
  classical
  have hgram (j : X) (i : Fin D.rank) :
      ∑ k, gramComplex D i k * (if (s j).colour = k then weights j * m j else 0) =
        gramComplex D i (s j).colour * (weights j * m j) := by
    simp only [mul_ite, mul_zero]
    simp [eq_comm]
  have hvec (k : Fin D.rank) :
      (gramComplex D *ᵥ sourceVector D s weights m) k =
        ∑ j, gramComplex D k (s j).colour * (weights j * m j) := by
    simp only [mulVec, dotProduct, sourceVector, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hgram j k)
  have hsum :
      sourceVector D s weights m ⬝ᵥ gramComplex D *ᵥ sourceVector D s weights m =
        ∑ i, ∑ j, weights i * weights j * gramComplex D (s i).colour (s j).colour *
          (m i * m j) := by
    unfold dotProduct
    simp only [hvec, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ i, weights i * weights j * gramComplex D (s i).colour (s j).colour *
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
      (∑ i, ∑ j, (weights i * weights j) * gramComplex D (s i).colour (s j).colour *
          (c * (m i * m j))) = c * (sourceVector D s weights m ⬝ᵥ
            gramComplex D *ᵥ sourceVector D s weights m) := by
    rw [hsum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [gaussianExponent, mul_sub, Finset.sum_sub_distrib, hcorrection, sub_div]

/-- The original signed Gaussian covariance between two native samples. -/
def nativeCovariance (D : LatticeData) {X : Type*} (s : X → Sample D)
    (w : ℂ) (i j : X) : ℂ :=
  covarianceMode (s i).right (s j).right (s i).outgoing (s j).outgoing
    ((s i).q ^ 2) ((s j).q ^ 2) (w ^ 2)

/-- The inverse half-differential lift factor for the indicated chart. -/
def chartScale (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => 1
  | .B => (bLift x)⁻¹
  | .D => I⁻¹

/-- The period used in the normalization of each chart product. -/
def chartPeriod (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => pA x
  | .B => pB x
  | .D => pD upperA x

/-- The shifted theta parameter for each chart and chosen A side. -/
def chartTau (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => I * pD upperA x / pA x
  | .B => -1 / (I * pB x / pPf x)
  | .D => -1 / (I * pD upperA x / pA x)

/-- The actual periods are nonzero and their charge parameters lie in the
upper half-plane on the real overlap, for either choice of lip. -/
theorem chart_charge_data (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x)
    (hx₁ : x < 1) : chartPeriod upperA c x ≠ 0 ∧ 0 < (chartTau upperA c x).im := by
  let pA := slitPeriod (parameter .A (x : ℂ))
  let pB := slitPeriod (x : ℂ)
  let tB := Complex.I * pB / slitPeriod (1 - (x : ℂ))
  let tD := Complex.I * dPeriod upperA ((x : ℂ)⁻¹) / pA
  have hslit : (1 - (x : ℂ)) ∈ doubleSlit := by
    constructor
    · change 1 - (1 - (x : ℂ)) ∈ Complex.slitPlane
      rw [sub_sub_cancel]
      exact Complex.ofReal_mem_slitPlane.2 hx
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using sub_pos.mpr hx₁))
  have hpA : pA ≠ 0 := fun h => slitPeriod_ne_zero hslit.1 (by
    rw [OriginalFourMPeriodSource.chartB_pfaff_period hx]
    change periodRoot .A x * pA = 0
    rw [h, mul_zero])
  have hpB : pB ≠ 0 := slitPeriod_ne_zero hslit.2
  have hpD : dPeriod upperA ((x : ℂ)⁻¹) ≠ 0 := by
    simpa only [Complex.ofReal_inv] using dPeriod_ne_zero upperA ((one_lt_inv₀ hx).2 hx₁)
  have htB : 0 < tB.im := by
    simpa only [tB, pB, tau, sub_sub_cancel] using tau_im_pos hslit
  have htEq : tD = tB + lipSign upperA := by
    dsimp only [tD]
    rw [dPeriod, inv_inv]
    change Complex.I * ((tau (1 - (x : ℂ)) + lipSign upperA) * pA / Complex.I) / pA = _
    rw [tau, sub_sub_cancel]
    change Complex.I * ((tB + lipSign upperA) * pA / Complex.I) / pA = _
    field_simp [hpA, Complex.I_ne_zero]
  have htD : 0 < tD.im := by
    rw [htEq]
    cases upperA <;> simpa [lipSign, Complex.add_im] using htB
  have hinv {τ : ℂ} (h : 0 < τ.im) : 0 < (-1 / τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos h (Complex.normSq_pos.mpr fun hn => by simp [hn] at h)
  constructor
  · cases c
    · exact hpA
    · exact hpB
    · exact hpD
  · cases c
    · exact htD
    · exact hinv htB
    · exact hinv htD

/-- The complementary-period correction in the target chart source units. -/
def chartDifference (upperA : Bool) (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A => 0
  | .B => 1 / ((Real.pi : ℂ) * pPf x * pB x)
  | .D => 1 / ((Real.pi : ℂ) * pA x * pD upperA x)

/-- The native A differential scaled into the target chart units. -/
def pulledDifferential (D : LatticeData) (c : Chart) (x : ℝ) (w : ℂ)
    (s : Sample D) : ℂ := chartScale c x * differential D w s

/-- The covariance in the common A coordinates after the target period correction. -/
def pulledCovariance (D : LatticeData) {X : Type*} (s : X → Sample D)
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

private theorem normalize_complement (p q E δ : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    (q ^ (12 : ℕ))⁻¹ * Complex.exp (E - δ) *
        ((-I * (I * q / p)) ^ (12 : ℕ) * Complex.exp δ) =
      (p ^ (12 : ℕ))⁻¹ * Complex.exp E := by
  have hratio : -I * (I * q / p) = q / p := by
    rw [← mul_div_assoc, neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg]
  rw [hratio, div_pow, Complex.exp_sub]
  field_simp [Complex.exp_ne_zero, hp, hq]

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
  let δB := chartDifference upperA .B x * (MB ⬝ᵥ gramComplex D *ᵥ MB) / 2
  let δD := chartDifference upperA .D x * (MD ⬝ᵥ gramComplex D *ᵥ MD) / 2
  let tB := I * pB x / pPf x
  let tD := I * pD upperA x / pA x
  have hslit : (1 - (x : ℂ)) ∈ doubleSlit := by
    constructor
    · change 1 - (1 - (x : ℂ)) ∈ Complex.slitPlane
      rw [sub_sub_cancel]
      exact Complex.ofReal_mem_slitPlane.2 hx
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using sub_pos.mpr hx1))
  have hP : pPf x ≠ 0 := slitPeriod_ne_zero hslit.1
  have hB := slitPeriod_ne_zero (r := (x : ℂ)) (by
    change 1 - (x : ℂ) ∈ Complex.slitPlane
    exact hslit.2)
  have hp : pPf x = periodRoot .A x * pA x := OriginalFourMPeriodSource.chartB_pfaff_period hx
  have hA : pA x ≠ 0 := fun h => hP (by rw [hp, h, mul_zero])
  have hD₀ : pD upperA x ≠ 0 := by
    change dPeriod upperA ((x : ℂ)⁻¹) ≠ 0
    simpa only [ofReal_inv] using dPeriod_ne_zero upperA ((one_lt_inv₀ hx).2 hx1)
  have hs : (Real.sqrt x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'
  have hl : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have htB : 0 < tB.im := by
    simpa only [tau, sub_sub_cancel] using tau_im_pos hslit
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
  obtain ⟨heB, heD⟩ := chart_source_exponents upperA hx hx1 D MB MD
  rw [hzB] at heB
  rw [hzD] at heD
  change 2 * (Real.pi : ℂ) * I * (zA ⬝ᵥ gramComplex D *ᵥ zA) / tB = δB at heB
  change 2 * (Real.pi : ℂ) * I * (zA ⬝ᵥ gramComplex D *ᵥ zA) / tD = δD at heD
  have exponent (t : ℂ) :
      (Real.pi : ℂ) * I / t * sourceQuadratic (gramReal (doubled D)) zA =
        2 * (Real.pi : ℂ) * I * (zA ⬝ᵥ gramComplex D *ᵥ zA) / t := by
    rw [sourceQuadratic_doubled]
    ring
  have hd := chargeTheta_S D hu hD hr a tD htD zA
  have hb := chargeTheta_S D hu hD hr a tB htB zA
  rw [hzSD, exponent, heD] at hd
  rw [hzSB, chargeTheta_neg_source, exponent, heB] at hb
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
    rfl
  have hformB :
      chartProduct D hu s weights upperA x w .B a =
        ((pB x)^ (12 : ℕ))⁻¹ * Complex.exp (E - δB) *
          chargeTheta D hu a (-1 / tB) (thetaSource D (pB x) MB) := by
    unfold chartProduct pulledCovariance pulledDifferential
    dsimp only [chartPeriod, chartScale, chartDifference, chartTau]
    rw [gaussianExponent_sub]
    rfl
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

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChartProduct
