/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The true D-lip coefficients and crossing of four lowest-mode currents. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
import D5.S3.VertexAlgebra.TwistedGround.GaussElimination

/-! The fixed-charge D-lip comparison and three-channel crossing for four lowest currents. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open FourPoint.OriginalFourMActualChart
open FourPoint.OriginalFourMChargeNormal (projectOccupations)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalEntry physicalMean)
open OriginalFourMChartProduct (chartTau chartPeriod chart_charge_data)
open OriginalFourMSpatialWick (spatialCoefficient spatialCoefficient_split_marks)
open OriginalGaussianSourceRestriction
  (fourSupport CompactExternal compactExternal externalOccupation)
open OriginalChargedRowSource (affineCoefficient)
open NativeAffineExternalCoefficient (jetOccupation)
open OriginalFourMOccupationTransport (flags rawLocal halfJacobian inverseRoot_zero root_ne
  physicalSource)
open OriginalFourMPhysicalCovariance (relative jac slotCorrection physicalCovariance
  physical_covariance_swap)
open OriginalFourMSignedOverlap (chartCovariance chartW dLipMean_eq_chosen_chart_source)
open OriginalFourMDLipMean (dLipMean dLipCovariance)
open OriginalFourMDLipNome (dTau dNome)
open OriginalFourMPeriodSource (chartCorrection dPeriod)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod tau)

open private currentExponent marks four_mark_rescale spatial_zero slot currentSupport
  taggedCurrent current_occupation project_four_currents mark_occupation coefficient_zero
  from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private dDeterminant dMatrix dLinear dLipCovarianceEntry dLipMeanEntry from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private dW dCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
open private same_flags from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private rootZ from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart
open private affine_enlarge from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
open private mark_jet_eq_moment from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

private abbrev dOrder : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

private abbrev dColour (D : LatticeData) (colour : Fin 4 → Fin D.rank) :=
  colour ∘ dOrder

private abbrev dTag (D : LatticeData) (colour : Fin 4 → Fin D.rank) :=
  dOrder.symm.toEmbedding.trans (taggedCurrent D (dColour D colour))

private theorem dTag_leg (D : LatticeData) (colour : Fin 4 → Fin D.rank) (i : Fin 4) :
    (dTag D colour i).isRight = (flags .D (slot i)).1 := by
  fin_cases i <;> rfl

private theorem dTag_label (D : LatticeData) (colour : Fin 4 → Fin D.rank) (i : Fin 4) :
    Sum.elim (compactExternal D (currentSupport D (dColour D colour)))
      (compactExternal D (currentSupport D (dColour D colour))) (dTag D colour i) =
        ((flags .D (slot i)).2, colour i, 0) := by
  fin_cases i <;> rfl

private theorem d_occupation (D : LatticeData) (colour : Fin 4 → Fin D.rank) :
    (jetOccupation marks).embDomain (taggedCurrent D (dColour D colour)) =
      (jetOccupation marks).embDomain (dTag D colour) := by
  rw [Finsupp.embDomain_trans_apply]
  congr 1
  ext i
  obtain ⟨j, rfl⟩ := dOrder.symm.surjective i
  change jetOccupation marks (dOrder.symm j) =
    (jetOccupation marks).embDomain dOrder.symm.toEmbedding (dOrder.symm.toEmbedding j)
  rw [Finsupp.embDomain_apply_self, mark_occupation, mark_occupation]

private theorem true_lip_source {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (e : Bool) (u : ℂ) :
    dLipMean true e u (parameter .D (x : ℂ)) =
      OriginalFourMSignedOverlap.chosenChartSource .D x e u := by
  simpa only [Bool.true_or, ite_true, one_mul] using
    dLipMean_eq_chosen_chart_source hx hx₁ true e u

private theorem true_lip_covariance {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (l k e f : Bool) (u v : ℂ) :
    dLipCovariance true l k e f u v (parameter .D (x : ℂ)) =
      chartCovariance true .D x l k e f u v := by
  simp only [dLipCovariance, chartCovariance, dW, chartW, dCorrection, chartCorrection,
    true_lip_source hx hx₁]

private theorem d_chart_entry (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {i j : Fin 4} (hij : i ≠ j) :
    physicalEntry D true .D x slot colour i j 0 0 =
      (scaleRoot .D x (slot i))⁻¹ *
        dMatrix D true (compactExternal D (currentSupport D (dColour D colour)))
          (parameter .D (x : ℂ)) (dTag D colour i) (dTag D colour j) *
      (scaleRoot .D x (slot j))⁻¹ := by
  have hs : slot i ≠ slot j := by
    intro h
    apply hij
    fin_cases i <;> fin_cases j <;> simp_all [slot]
  have hcorr : slotCorrection .D x (slot i) (slot j) 0 0 = 0 := by
    rw [slotCorrection, ite_eq_right (fun h => hs (same_flags .D h))]
  simp only [physicalEntry, physicalCovariance, rawLocal, hcorr, sub_zero, jac,
    halfJacobian, inverseRoot_zero, one_pow, dMatrix, dTag_leg, dTag_label,
    dLipCovarianceEntry, coefficient_zero, LatticeHalfFock.gramComplex, Matrix.map_apply,
    true_lip_covariance hx hx₁, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem d_chart_mean (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (i : Fin 4) :
    physicalMean D q true .D x slot colour i 0 =
      (scaleRoot .D x (slot i))⁻¹ *
        ((bilinear D (unitCharge D (colour i)) q : ℂ) *
          dLinear D true (compactExternal D (currentSupport D (dColour D colour)))
            (parameter .D (x : ℂ)) (dTag D colour i)) := by
  have hp : chartPeriod true .D x = dPeriod true (parameter .D (x : ℂ)) := rfl
  simp only [physicalMean, physicalSource, rawLocal, halfJacobian, inverseRoot_zero,
    one_pow, dLinear, dTag_leg, dTag_label, dLipMeanEntry, coefficient_zero,
    true_lip_source hx hx₁, hp, div_eq_mul_inv]
  ring

private theorem d_chart_tau {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    chartTau true .D x = dTau true (parameter .D (x : ℂ)) := by
  have hp : slitPeriod (1 - parameter .D (x : ℂ)) ≠ 0 :=
    (chart_charge_data true .A hx hx₁).1
  unfold dTau
  change -1 / (Complex.I * dPeriod true (parameter .D (x : ℂ)) /
    slitPeriod (1 - parameter .D (x : ℂ))) = _
  rw [show Complex.I * dPeriod true (parameter .D (x : ℂ)) /
      slitPeriod (1 - parameter .D (x : ℂ)) =
      tau (1 - (parameter .D (x : ℂ))⁻¹) + OriginalFourMPeriodSource.lipSign true by
    unfold dPeriod
    field_simp [hp, Complex.I_ne_zero]]
  rw [div_eq_mul_inv, neg_one_mul]

private theorem d_chart_charge (D : LatticeData) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true .D x * (bilinear D q q : ℂ) / 2) =
      dNome true (parameter .D (x : ℂ)) ^ (chargeEnergy D q).toNat := by
  rw [dNome, ← Complex.exp_nat_mul, d_chart_tau hx hx₁]
  have he : (bilinear D q q : ℂ) = 2 * ((chargeEnergy D q).toNat : ℂ) := by
    have hn : ((chargeEnergy D q).toNat : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg hq
    exact_mod_cast ((two_chargeEnergy D q).symm.trans (congrArg (2 * ·) hn.symm))
  rw [he]
  congr 1
  ring

private theorem d_chart_normalization {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    (chartPeriod true .D x ^ (12 : ℕ))⁻¹ *
      (∏ i : Fin 4, relative .D (slot i) * (scaleRoot .D x (slot i))⁻¹) =
      (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3) *
        dDeterminant true (parameter .D (x : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h₁ : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  have hroot : rootZ x ≠ 0 := root_ne hx hx₁ .B .Q
  have hscale : (∏ i : Fin 4, relative .D (slot i) * (scaleRoot .D x (slot i))⁻¹) =
      Complex.I := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change 1 * (1 : ℂ)⁻¹ * (-1 * (Complex.I * rootZ x)⁻¹ *
      (-1 * Complex.I⁻¹ * (1 * (Complex.I / rootZ x)⁻¹))) = _
    simp only [one_mul, inv_one, mul_inv_rev, div_eq_mul_inv, inv_inv, Complex.inv_I]
    calc
      _ = (Complex.I ^ 2) * (-Complex.I) * ((rootZ x)⁻¹ * rootZ x) := by ring
      _ = _ := by rw [Complex.I_sq, inv_mul_cancel₀ hroot]; ring
  rw [hscale, dDeterminant]
  change _ * _ = _ * (((1 - (x : ℂ)⁻¹) ^ (3 : ℕ))⁻¹ *
    (chartPeriod true .D x ^ (12 : ℕ))⁻¹)
  have ht : (1 : ℂ) - (x : ℂ)⁻¹ = -(1 - (x : ℂ)) / (x : ℂ) := by
    field_simp [hxC]
    ring
  rw [ht]
  field_simp [hxC, h₁]

private def dLipChargeTerm (D : LatticeData) (b g d e : Exponent D)
    (q : Charge D) (t : ℂ) : ℂ :=
  let F := fourSupport D b g d e
  let label := compactExternal D F
  dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
    affineCoefficient (dMatrix D true label t)
      (fun i => (bilinear D (unitCharge D (Sum.elim label label i).2.1) q : ℂ) *
        dLinear D true label t i)
      (externalOccupation D F b g d e)

/-- The fixed-charge physical D coefficient equals the true-lip occupation projection
in native order P, R, Q, S. The occupation tags distinguish the four slots even when
their lattice colours coincide. -/
theorem chartD_four_current_fixed_charge
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    let osc := fun i : Fin 4 =>
      MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    (chartPeriod true .D x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (marks.map Sum.inr ++ marks.map Sum.inl)
        (physicalChargeSummand D slot colour true .D x q) 0 =
      (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 2) (osc 1) (osc 3)
          (fun b g d e => dLipChargeTerm D b g d e q (parameter .D (x : ℂ))) := by
  classical
  let t := parameter .D (x : ℂ)
  let cols := dColour D colour
  let label := compactExternal D (currentSupport D cols)
  let tag := dTag D colour
  let T := CompactExternal D (currentSupport D cols)
  let K : Matrix (T ⊕ T) (T ⊕ T) ℂ := dMatrix D true label t
  let eta := fun i =>
    (bilinear D (unitCharge D (Sum.elim label label i).2.1) q : ℂ) * dLinear D true label t i
  let B : Matrix (Fin 4) (Fin 4) ℂ := fun i j => K (tag i) (tag j)
  let nu : Fin 4 → ℂ := fun i => eta (tag i)
  let A : Matrix (Fin 4) (Fin 4) ℂ := fun i j => physicalEntry D true .D x slot colour i j 0 0 *
    relative .D (slot i) * relative .D (slot j)
  let mu := fun i => physicalMean D q true .D x slot colour i 0 * relative .D (slot i)
  let w := fun i => relative .D (slot i) * (scaleRoot .D x (slot i))⁻¹
  let d := jetOccupation marks
  have hA (i j : Fin 4) : A i j = A j i := by
    simp only [A, physicalEntry]
    rw [physical_covariance_swap true .D x (slot i) (slot j) 0 0,
      D.symmetric (colour i) (colour j)]
    ring
  have hOff (i j : Fin 4) (hij : i ≠ j) : A i j = w i * B i j * w j := by
    dsimp only [A, w, B, K, tag, label, cols, t]
    rw [d_chart_entry D colour hx hx₁ hij]
    ring
  have hMean (i : Fin 4) : mu i = w i * nu i := by
    dsimp only [mu, nu, eta, w, tag, label, cols, t]
    rw [d_chart_mean D colour q hx hx₁ i, dTag_label D colour]
    ring
  have hMark :
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (marks.map Sum.inr ++ marks.map Sum.inl)
        (physicalChargeSummand D slot colour true .D x q) 0 =
          dNome true t ^ (chargeEnergy D q).toNat * ((∏ i, w i) * affineCoefficient B nu d) := by
    rw [spatialCoefficient_split_marks _ marks (by decide : marks.Nodup), spatial_zero]
    have h := mark_jet_eq_moment D slot colour true .D x q marks (0 : Fin 4 → ℂ)
    simp only [Pi.zero_apply] at h
    rw [h, d_chart_charge D q hq hx hx₁]
    exact congrArg (_ * ·) (four_mark_rescale A B mu nu w hA hOff hMean)
  have hNative :
      dLipChargeTerm D (currentExponent D cols 0) (currentExponent D cols 1)
        (currentExponent D cols 2) (currentExponent D cols 3) q t =
      dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat * affineCoefficient B nu d := by
    unfold dLipChargeTerm
    dsimp only
    rw [current_occupation, d_occupation]
    exact congrArg (fun z => dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat * z)
      (affine_enlarge K eta tag d)
  dsimp only
  change (chartPeriod true .D x ^ (12 : ℕ))⁻¹ * spatialCoefficient _ _ _ 0 =
    _ * projectOccupations D 2 2 0 (-1)
      (MvPolynomial.monomial (currentExponent D cols 0) 1)
      (MvPolynomial.monomial (currentExponent D cols 1) 1)
      (MvPolynomial.monomial (currentExponent D cols 2) 1)
      (MvPolynomial.monomial (currentExponent D cols 3) 1) _
  rw [hMark, project_four_currents D cols, hNative]
  calc
    _ = ((chartPeriod true .D x ^ (12 : ℕ))⁻¹ * ∏ i, w i) *
          (dNome true t ^ (chargeEnergy D q).toNat * affineCoefficient B nu d) := by ring
    _ = _ := by
      rw [d_chart_normalization hx hx₁]
      ring

#print axioms chartD_four_current_fixed_charge

open Filter Set
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization (actual_twisted_ground_representation)
open LatticeTwistedGroundRealization.SignQuotient
  (ModTwoCharge reduceCharge mod_two_cocycle_symmetrization modTwoPairing complexSign_add)
open LatticeHalfFockChargedTensorCoefficients (groundRank)
open FourPoint.FourPointChannelCoefficients (loweringCutoff loweredLaurent loweringWeight laurent)
open OriginalFourMChargeCoset (slitDiagonal slitChannelA slitChannelB slitChannelD slitLowered
  quadraticSign quadraticSign_add fourierSign dLipChannel slit_AD_overlap identityK
  identityK_of_slitChart_crossing)
open OriginalFourMSectorContinuation (dLipChargeSector)
open OriginalFourMSpatialWick (physical_chart_jet_hasSum physical_chart_coefficient_overlap)
open OriginalFourPointChartGluing (U_A U_D)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (doubleSlit)

open private fourCurrentJet currentOscillator four_current_sector chartA_radius from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private dLipNumerator from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private slitLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms
open private quadraticSign_square from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

/-- The physical four-current coefficient on the true D lip is the literal
D-lip charge sector projected in the puncture order P, R, Q, S. -/
theorem chartD_four_current_sector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (colour : Fin 4 → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (a : ModTwoCharge D) :
    let osc := currentOscillator D colour
    fourCurrentJet D hu colour true .D x a =
      (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 2) (osc 1) (osc 3)
          (fun b g d e => dLipChargeSector D true a b g d e (parameter .D (x : ℂ))) := by
  classical
  let cols := dColour D colour
  let k := -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3
  let t := parameter .D (x : ℂ)
  change fourCurrentJet D hu colour true .D x a = k *
    projectOccupations D 2 2 0 (-1) (currentOscillator D cols 0) (currentOscillator D cols 1)
      (currentOscillator D cols 2) (currentOscillator D cols 3)
      (fun b g d e => dLipChargeSector D true a b g d e t)
  obtain ⟨hp, hτ⟩ := chart_charge_data true .D hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour true .D hx hx₁ hp hτ a
    (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
    (marks.map Sum.inr ++ marks.map Sum.inl)
  have hfixed (q : Charge D) :
      (chartPeriod true .D x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
          (marks.map Sum.inr ++ marks.map Sum.inl)
          (physicalChargeSummand D slot colour true .D x q) 0 = k *
        projectOccupations D 2 2 0 (-1) (currentOscillator D cols 0) (currentOscillator D cols 1)
          (currentOscillator D cols 2) (currentOscillator D cols 3)
          (fun b g d e => dLipChargeTerm D b g d e q t) :=
    chartD_four_current_fixed_charge D colour q (chargeEnergy_nonneg D hD q) hx hx₁
  rw [fourCurrentJet, ← hs.tsum_eq]
  simp_rw [hfixed, project_four_currents D cols]
  rw [tsum_mul_left]
  congr 1
  let f (q : Charge D) := dLipChargeTerm D (currentExponent D cols 0) (currentExponent D cols 1)
    (currentExponent D cols 2) (currentExponent D cols 3) q t
  let fibre : Set (Charge D) := {q | reduceCharge D q = a}
  calc
    _ = ∑' q, fibre.indicator f q := tsum_subtype fibre f
    _ = _ := by
      unfold dLipChargeSector
      apply tsum_congr
      intro q
      by_cases h : reduceCharge D q = a <;> simp [fibre, Set.indicator, f, dLipChargeTerm, h]

private theorem fourierSign_swap (D : LatticeData) (a b : ModTwoCharge D) :
    fourierSign D a b = fourierSign D b a := by
  unfold fourierSign
  rw [← mod_two_cocycle_symmetrization D a b, ← mod_two_cocycle_symmetrization D b a, add_comm]

private theorem translated_gauss_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (b c : ModTwoCharge D) :
    (∑ a, quadraticSign D (a + b) * fourierSign D a c) =
      (2 : ℂ) ^ (12 : ℕ) * (quadraticSign D c * fourierSign D c b) := by
  classical
  have hrank : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have hhalf : groundRank D hu = 12 := by omega
  have hGauss : (∑ a, quadraticSign D a) = (2 : ℂ) ^ (12 : ℕ) := by
    simpa only [quadraticSign, hhalf] using GaussElimination.actual_quadratic_gauss_sum D hu
  have hpair (a : ModTwoCharge D) :
      fourierSign D (a + b) c = fourierSign D a c * fourierSign D b c := by
    simp only [fourierSign, map_add, LinearMap.add_apply, complexSign_add]
  have hterm (a : ModTwoCharge D) :
      quadraticSign D (a + b) * fourierSign D a c =
        quadraticSign D (a + (b + c)) * (quadraticSign D c * fourierSign D c b) := by
    rw [← add_assoc, quadraticSign_add D (a + b) c, hpair, fourierSign_swap D c b]
    calc
      _ = (quadraticSign D c * quadraticSign D c) *
          (fourierSign D b c * fourierSign D b c) *
          (quadraticSign D (a + b) * fourierSign D a c) := by
            rw [quadraticSign_square, show fourierSign D b c * fourierSign D b c = 1 from
              LatticeTwistedGroundRealization.sign_square _, one_mul, one_mul]
      _ = _ := by ring
  simp_rw [hterm]
  have hTranslate : (∑ i, quadraticSign D (i + (b + c))) = ∑ i, quadraticSign D i :=
    Equiv.sum_comp (Equiv.addRight (b + c)) (quadraticSign D)
  rw [← Finset.sum_mul, hTranslate, hGauss]

/-- The continued A channel and the true D-lip channel agree on the real
overlap for four weight-two currents at total mode two. -/
theorem four_current_d_lip_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (hs : m + n + r = 2) (b : ModTwoCharge D)
    {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) :
    let osc := currentOscillator D colour
    slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .A (x : ℂ)) =
      dLipChannel D true 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .D (x : ℂ)) := by
  classical
  let osc := currentOscillator D colour
  let tA := parameter .A (x : ℂ)
  let tD := parameter .D (x : ℂ)
  let diagA (a : ModTwoCharge D) := slitDiagonal D 2 2 2 (osc 0) (osc 1) (osc 2) (osc 3) a tA
  let diagD (a : ModTwoCharge D) := dLipNumerator D true 2 2 2 (osc 0) (osc 2) (osc 1) (osc 3) a tD
  let kA := -Complex.I / ((x : ℂ) ^ 3 * (1 - (x : ℂ)))
  let kD := -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3
  let w := Complex.sqrt tA
  have hx₀ : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀.ne'
  have h₁ : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  have hwA : w ^ 2 = tA := Complex.cpow_nat_inv_pow tA (by decide : (2 : ℕ) ≠ 0)
  have hw : ‖w‖ < 1 := by
    have hnorm : ‖w‖ ^ 2 < 1 := by
      rw [← norm_pow, hwA]
      exact chartA_radius hx hx₁
    nlinarith [norm_nonneg w]
  have hAjet (a : ModTwoCharge D) :
      fourCurrentJet D hu colour true .A x a = kA * diagA a :=
    four_current_sector D hu hD colour colour true .A hx₀ hx₁ a kA
      (fun q hq =>
        OriginalFourMAFourCurrent.chartA_four_current_fixed_charge D colour q hq true hx hx₁)
  have hDjet (a : ModTwoCharge D) :
      fourCurrentJet D hu colour true .D x a = kD * diagD a :=
    chartD_four_current_sector D hu hD colour hx₀ hx₁ a
  let A (a : ModTwoCharge D) := (-tA) ^ (-(4 : ℤ)) * diagA a
  let L (a : ModTwoCharge D) := (-tD) ^ (-(4 : ℤ)) * diagD a
  have hLaurentA : (-tA) ^ (-(4 : ℤ)) = ((1 - (x : ℂ)) ^ 4)⁻¹ * (x : ℂ) ^ 4 := by
    have ht : -tA = (1 - (x : ℂ)) / (x : ℂ) := by
      change -(1 - (x : ℂ)⁻¹) = _
      field_simp [hxC]
      ring
    rw [ht, zpow_neg]
    change (((1 - (x : ℂ)) / (x : ℂ)) ^ (4 : ℕ))⁻¹ = _
    rw [div_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm]
  have hLaurentD : (-tD) ^ (-(4 : ℤ)) = (x : ℂ) ^ (4 : ℕ) := by
    change (-((x : ℂ)⁻¹)) ^ (-(4 : ℤ)) = _
    rw [zpow_neg]
    change ((-((x : ℂ)⁻¹)) ^ (4 : ℕ))⁻¹ = _
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, neg_sq, ← pow_mul, inv_pow, inv_inv]
  let k := -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 7
  have hk : k ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (pow_ne_zero _ h₁)) (pow_ne_zero _ hxC)
  have hAjet' (a : ModTwoCharge D) : fourCurrentJet D hu colour true .A x a = k * A a := by
    rw [hAjet]
    dsimp only [A]
    rw [hLaurentA]
    dsimp only [k, kA]
    field_simp [hxC, h₁]
  have hDjet' (a : ModTwoCharge D) : fourCurrentJet D hu colour true .D x a = k * L a := by
    rw [hDjet]
    dsimp only [L]
    rw [hLaurentD]
    dsimp only [k, kD]
    field_simp [hxC]
  have hFourier (a : ModTwoCharge D) :
      L a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ c, fourierSign D a c * A c := by
    have hover := (physical_chart_coefficient_overlap D hu hD h24 slot colour true hx₀ hx₁ hwA hw
      (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
      (marks.map Sum.inr ++ marks.map Sum.inl) a).1
    change fourCurrentJet D hu colour true .D x a =
      ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
        ∑ c, fourierSign D a c * fourCurrentJet D hu colour true .A x c at hover
    simp only [hAjet', hDjet'] at hover
    apply mul_left_cancel₀ hk
    calc
      _ = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (k * ∑ c, fourierSign D a c * A c) := by
        rw [hover]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by ring
  have hN : loweringCutoff 2 2 2 m n r = 1 := by unfold loweringCutoff; omega
  change slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) b tA =
    dLipChannel D true 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b tD
  rw [slitChannelA, dLipChannel, hN, hs]
  change _ = ∑ a, quadraticSign D (a + b) *
    loweredLaurent (2 + (2 : ℤ)) 2 1
      (fun ell u => dLipNumerator D true 2 2 (2 + (ell : ℤ)) (osc 0) (osc 2) (osc 1)
        ((OriginalFourMChargeCoset.oscillatorLower D ^ ell) (osc 3)) a (-u)) tD
  have hLower (a : ModTwoCharge D) :
      loweredLaurent (2 + (2 : ℤ)) 2 1
        (fun ell u => dLipNumerator D true 2 2 (2 + (ell : ℤ)) (osc 0) (osc 2) (osc 1)
          ((OriginalFourMChargeCoset.oscillatorLower D ^ ell) (osc 3)) a (-u)) tD = L a := by
    norm_num [loweredLaurent, loweringWeight, laurent, L, diagD, Module.End.one_apply]
  simp only [hLower, hFourier]
  change (∑ c, quadraticSign D c * fourierSign D c b * A c) =
    ∑ a, quadraticSign D (a + b) * (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ c, fourierSign D a c * A c)
  have h2 : (2 : ℂ) ^ (12 : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  symm
  calc
    _ = ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
        (∑ a, ∑ c, (quadraticSign D (a + b) * fourierSign D a c) * A c) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    _ = _ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_mul, translated_gauss_sum D hu h24 b c]
      calc
        _ = (((2 : ℂ) ^ (12 : ℕ))⁻¹ * (2 : ℂ) ^ (12 : ℕ)) *
            (quadraticSign D c * fourierSign D c b * A c) := by ring
        _ = _ := by rw [inv_mul_cancel₀ h2, one_mul]

#print axioms chartD_four_current_sector
#print axioms four_current_d_lip_crossing

/-- The real D-lip crossing determines an interior overlap of the actual
continued slit channels at four lowest currents. -/
theorem four_current_slit_ad_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (hs : m + n + r = 2) (b : ModTwoCharge D) :
    let osc := currentOscillator D colour
    ∃ y ∈ U_A ∩ U_D, ∀ᶠ z in 𝓝 y,
      slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .A z) =
        slitChannelD D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .D z) := by
  let osc := currentOscillator D colour
  dsimp only
  apply slit_AD_overlap D hD true 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b
    (t := 4 / 3) (by norm_num)
  filter_upwards [lt_mem_nhds (show (1 : ℝ) < 4 / 3 by norm_num),
    gt_mem_nhds (show (4 / 3 : ℝ) < 2 by norm_num)] with s h₁ h₂
  have h₀ : 0 < s := zero_lt_one.trans h₁
  have hx : (1 / 2 : ℝ) < s⁻¹ := by
    rw [← one_div s]
    apply (lt_div_iff₀ h₀).2
    linarith
  have hx₁ : s⁻¹ < 1 := (inv_lt_one₀ h₀).2 h₁
  simpa only [parameter, Complex.ofReal_inv, inv_inv] using
    four_current_d_lip_crossing D hu hD h24 colour m n r hs b hx hx₁

/-- The original three-channel identity for four lowest currents in a positive
unimodular rank-24 lattice, including the Leech lattice. -/
theorem four_current_identityK (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (hs : m + n + r = 2) :
    let osc := currentOscillator D colour
    identityK D hu 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) := by
  dsimp only
  apply identityK_of_slitChart_crossing D hu hD h24
  intro b
  dsimp only
  let x : ℝ := 3 / 4
  have hx : 1 / 2 < x := by norm_num [x]
  have hx₁ : x < 1 := by norm_num [x]
  obtain ⟨y, hy, hAD⟩ := four_current_slit_ad_overlap D hu hD h24 colour m n r hs b
  have hxSlit : (x : ℂ) ∈ doubleSlit := by
    refine ⟨?_, Complex.ofReal_mem_slitPlane.mpr (by norm_num [x])⟩
    change 1 - (x : ℂ) ∈ Complex.slitPlane
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.mpr (sub_pos.mpr hx₁)
  have hCast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s h
      simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using h
  refine ⟨(x : ℂ), y, hxSlit, hCast.frequently ?_, Or.inl ⟨hy, ?_⟩⟩
  · apply Filter.Eventually.frequently
    have hmode : m + n + r + 2 = (4 : ℤ) := by omega
    filter_upwards [(lt_mem_nhds hx).filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds hx₁).filter_mono nhdsWithin_le_nhds] with s hs₀ hs₁
    rw [hmode]
    change _ = (2 : ℂ) ^ (12 : ℕ) * (s : ℂ) ^ (4 : ℕ) * _
    exact OriginalFourMAFourCurrent.four_current_slit_crossing D hu hD h24 colour m n r hs b hs₀ hs₁
  · exact (hAD.filter_mono nhdsWithin_le_nhds).frequently

#print axioms four_current_slit_ad_overlap
#print axioms four_current_identityK

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent
