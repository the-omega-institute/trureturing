/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAFourCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAFourCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The A and B chart coefficients of four lowest-mode currents. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

/-! The fixed-charge comparison at the four actual A and B chart punctures. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open FourPoint.OriginalFourMActualChart
open FourPoint.OriginalFourMChargeNormal (projectOccupations)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalEntry physicalMean)
open OriginalFourMChartProduct (chartTau chartPeriod)
open OriginalFourMSpatialWick (spatialCoefficient spatialCoefficient_split_marks)
open OriginalFourMSectorContinuation (slitChargeTerm slitMatrix slitLinear)
open OriginalGaussianSourceRestriction
  (fourSupport CompactExternal compactExternal externalOccupation)
open OriginalNormalRowSource (restricted)
open OriginalChargedRowSource (affineCoefficient affineMoment affineMoment_zero affineMoment_step
  affineMoment_coefficient)
open NativeAffineExternalCoefficient (jetOccupation)
open FactorialFockMetric (weight)
open OriginalGaussianSewnAnalytic (coefficient)
open private affine_diagonal from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
open private affine_enlarge from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
open private take from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialTaylor
open private mark_jet_eq_moment from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

private abbrev currentExponent (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    (i : Fin 4) : Exponent D := Finsupp.single (colour i, 0) 1

private abbrev marks : List (Fin 4) := [0, 1, 2, 3]

private theorem mark_occupation (i : Fin 4) : jetOccupation marks i = 1 := by
  fin_cases i <;> simp [jetOccupation]

-- Every contraction removes a distinct occupied coordinate.
private theorem affineMoment_offDiagonal {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (mu : I → ℂ)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hOff : ∀ i j, i ≠ j → A i j = B i j)
    (d : I →₀ ℕ) (hsquarefree : ∀ i, d i ≤ 1) :
    affineMoment A mu d = affineMoment B mu d := by
  classical
  suffices ∀ n (r : I →₀ ℕ), r.degree = n → (∀ i, r i ≤ 1) →
      affineMoment A mu r = affineMoment B mu r from this d.degree d rfl hsquarefree
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r hr h01
    by_cases hz : r = 0
    · subst r
      simp only [affineMoment_zero]
    obtain ⟨i, hi⟩ := NativeGaussianMoment.occupation_nonzero r hz
    let t := r - Finsupp.single i 1
    have ht : t + Finsupp.single i 1 = r := Finsupp.sub_add_single_one_cancel hi
    have htd : t.degree + 1 = n := (NativeGaussianMoment.sub_single_degree r i hi).trans hr
    have ht01 (j : I) : t j ≤ 1 := by
      simp only [t, Finsupp.tsub_apply]
      exact (Nat.sub_le _ _).trans (h01 j)
    have hti : t i = 0 := by
      simp only [t, Finsupp.tsub_apply, Finsupp.single_eq_same]
      exact Nat.sub_eq_zero_of_le (h01 i)
    rw [← ht, affineMoment_step A mu hA, affineMoment_step B mu hB,
      ih t.degree (by omega) t rfl ht01]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [hti, Nat.cast_zero, zero_mul]
    · have hdeg : (t - Finsupp.single j 1).degree ≤ t.degree :=
        Finsupp.degree_mono tsub_le_self
      have hsub01 (k : I) : (t - Finsupp.single j 1 : I →₀ ℕ) k ≤ 1 := by
        rw [Finsupp.tsub_apply]
        exact (Nat.sub_le _ _).trans (ht01 k)
      rw [hOff i j hij, ih _ (by omega) (t - Finsupp.single j 1) rfl hsub01]

private theorem four_mark_rescale
    (A B : Matrix (Fin 4) (Fin 4) ℂ) (mu nu w : Fin 4 → ℂ)
    (hA : ∀ i j, A i j = A j i)
    (hOff : ∀ i j, i ≠ j → A i j = w i * B i j * w j)
    (hMean : ∀ i, mu i = w i * nu i) :
    affineMoment A mu (jetOccupation marks) =
      (∏ i, w i) * affineCoefficient B nu (jetOccupation marks) := by
  let d := jetOccupation marks
  have hw : weight d = 1 := by
    rw [FactorialFockMetric.weight_eq_prod d Finset.univ (Finset.subset_univ _)]
    simp only [d, mark_occupation, Nat.factorial_one, Finset.prod_const_one]
  have hp : d.prod (fun i n => w i ^ n) = ∏ i, w i := by
    rw [Finsupp.prod_fintype d (fun i n => w i ^ n) (fun i => pow_zero (w i))]
    simp only [d, mark_occupation, pow_one]
  let C : Matrix (Fin 4) (Fin 4) ℂ := fun i j => w i * B i j * w j
  have hs (i j : Fin 4) : C i j = C j i := by
    by_cases hij : i = j
    · subst j
      rfl
    · exact (hOff i j hij).symm.trans ((hA i j).trans (hOff j i (Ne.symm hij)))
  calc
    affineMoment A mu d = affineMoment C mu d :=
      affineMoment_offDiagonal A C mu hA hs hOff d (fun i => (mark_occupation i).le)
    _ = (∏ i, w i) * affineCoefficient B nu d := by
      rw [show mu = (fun i => w i * nu i) from funext hMean,
        affineMoment_coefficient, hw, Nat.cast_one, one_mul]
      change affineCoefficient (fun i j => w i * B i j * w j)
        (fun i => w i * nu i) d = _
      rw [affine_diagonal (Fin 4) B nu w d, hp]

private theorem spatial_zero {X : Type*} [DecidableEq X] (l : List X)
    (f : (X → ℂ) → ℂ) : spatialCoefficient (fun _ => 0) l f 0 = f 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [spatialCoefficient, ih]
    simp [take, coefficient]

private abbrev slot : Fin 4 → Puncture := ![.P, .Q, .R, .S]

private abbrev currentSupport (D : LatticeData) (colour : Fin 4 → Fin D.rank) :=
  fourSupport D (currentExponent D colour 0) (currentExponent D colour 1)
    (currentExponent D colour 2) (currentExponent D colour 3)

private def currentMark (D : LatticeData) (colour : Fin 4 → Fin D.rank) (i : Fin 4) :
    {b // b ∈ currentSupport D colour} :=
  ⟨(colour i, 0), by fin_cases i <;>
    simp [fourSupport, Finsupp.support_single]⟩

private def taggedCurrent (D : LatticeData) (colour : Fin 4 → Fin D.rank) :
    Fin 4 ↪ CompactExternal D (currentSupport D colour) ⊕
      CompactExternal D (currentSupport D colour) := by
  let tag : Fin 4 → CompactExternal D (currentSupport D colour) ⊕
      CompactExternal D (currentSupport D colour) :=
    ![.inl (.inl (currentMark D colour 0)),
    .inl (.inr (currentMark D colour 1)), .inr (.inl (currentMark D colour 2)),
    .inr (.inr (currentMark D colour 3))]
  refine ⟨tag, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [tag]

private theorem current_occupation (D : LatticeData) (colour : Fin 4 → Fin D.rank) :
    externalOccupation D (currentSupport D colour)
        (currentExponent D colour 0) (currentExponent D colour 1)
        (currentExponent D colour 2) (currentExponent D colour 3) =
      (jetOccupation marks).embDomain (taggedCurrent D colour) := by
  have hr (i : Fin 4) :
      restricted D (currentSupport D colour) (currentExponent D colour i) =
        Finsupp.single (currentMark D colour i) 1 := by
    ext a
    change Finsupp.single (colour i, 0) 1 a.val = Finsupp.single (currentMark D colour i) 1 a
    simp only [Finsupp.single_apply, ← Subtype.val_inj]
    rfl
  have e0 : taggedCurrent D colour 0 = .inl (.inl (currentMark D colour 0)) := rfl
  have e1 : taggedCurrent D colour 1 = .inl (.inr (currentMark D colour 1)) := rfl
  have e2 : taggedCurrent D colour 2 = .inr (.inl (currentMark D colour 2)) := rfl
  have e3 : taggedCurrent D colour 3 = .inr (.inr (currentMark D colour 3)) := rfl
  simp only [externalOccupation, hr, Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, jetOccupation,
    Finsupp.embDomain_add, Finsupp.embDomain_single, zero_add, e0, e1, e2, e3]
  ac_rfl

open OriginalFourMEnergyCoefficient (selector leftExponent doubledWeight)
open LatticeHalfFockChargedCoefficients (omega)
open LatticeHalfFockChargedTensorCoefficients (chargeNorm)

private theorem project_four_currents (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    let osc := fun i => MvPolynomial.monomial (currentExponent D colour i) (1 : ℂ)
    projectOccupations D 2 2 0 (-1) (osc 0) (osc 1) (osc 2) (osc 3) F =
      F (currentExponent D colour 0) (currentExponent D colour 1)
        (currentExponent D colour 2) (currentExponent D colour 3) := by
  classical
  dsimp only
  have hw (i : Fin 4) : weight (currentExponent D colour i) = 1 := by
    exact (Finsupp.prod_single_index (a := (colour i, 0)) (b := (1 : ℕ))
      (h := fun _ n => n.factorial) (by simp)).trans Nat.factorial_one
  have hd (i : Fin 4) : doubledWeight D (currentExponent D colour i) = 1 := by
    simp [Finsupp.weight_apply, Finsupp.sum_single_index, omega]
  have hz : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  norm_num [projectOccupations, MvPolynomial.support_monomial, MvPolynomial.coeff_monomial,
    hw, hd, hz, selector, leftExponent]

open OriginalFourMOccupationTransport (flags rawLocal halfJacobian inverseRoot_zero root_ne
  physicalSource)
open OriginalFourMPhysicalCovariance (relative jac slotCorrection physicalCovariance
  physical_covariance_swap)
open OriginalFourMSignedOverlap (chosen_chart_source_eq_native chart_covariance_eq_native)
open OriginalFourMSlitMean (slitCovarianceEntry slitMeanEntry slitCovariance_eq_native
  slitMean_eq_sourceMode)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod tau doubleSlit)
open D5.S3.Analytic.OriginalSlitNome (rank24Determinant slitNome)
open D5.S3.Analytic.OriginalHalfBinomialPfaffNome (negativeChartNome)
open OriginalFourMPeriodSource (dPeriod lipSign)
open private same_flags from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private leg from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
open private nomeOffZero from D5.S3.Analytic.OriginalSlitNome

-- Native input/output order, expressed in the common physical P,Q,R,S labels.
private def nativeOrder : Chart → Fin 4 ≃ Fin 4
  | .B => (Equiv.swap 0 1).trans (Equiv.swap 0 2)
  | _ => Equiv.refl _

private abbrev nativeColour (D : LatticeData) (colour : Fin 4 → Fin D.rank) (c : Chart) :=
  colour ∘ nativeOrder c

private abbrev chartTag (D : LatticeData) (colour : Fin 4 → Fin D.rank) (c : Chart) :=
  (nativeOrder c).symm.toEmbedding.trans (taggedCurrent D (nativeColour D colour c))

private theorem compact_current_leg (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    (c : Chart) (hc : c = .A ∨ c = .B) (i : Fin 4) :
    leg (chartTag D colour c i) = (flags c (slot i)).1 := by
  rcases hc with rfl | rfl <;> fin_cases i <;> rfl

private theorem compact_current_label (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    (c : Chart) (hc : c = .A ∨ c = .B) (i : Fin 4) :
    Sum.elim (compactExternal D (currentSupport D (nativeColour D colour c)))
      (compactExternal D (currentSupport D (nativeColour D colour c))) (chartTag D colour c i) =
        ((flags c (slot i)).2, colour i, 0) := by
  rcases hc with rfl | rfl <;> fin_cases i <;> rfl

private theorem chart_occupation (D : LatticeData) (colour : Fin 4 → Fin D.rank) (c : Chart) :
    (jetOccupation marks).embDomain (taggedCurrent D (nativeColour D colour c)) =
      (jetOccupation marks).embDomain (chartTag D colour c) := by
  rw [Finsupp.embDomain_trans_apply]
  congr 1
  ext i
  obtain ⟨j, rfl⟩ := (nativeOrder c).symm.surjective i
  change jetOccupation marks ((nativeOrder c).symm j) =
    (jetOccupation marks).embDomain (nativeOrder c).symm.toEmbedding
      ((nativeOrder c).symm.toEmbedding j)
  rw [Finsupp.embDomain_apply_self, mark_occupation, mark_occupation]

private theorem coefficient_zero (f : ℂ → ℂ) : coefficient 0 f = f 0 := by
  simp [coefficient]

private theorem chart_entry (D : LatticeData) (colour : Fin 4 → Fin D.rank)
    (upperA : Bool) (c : Chart) (hc : c = .A ∨ c = .B) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hr : ‖parameter c (x : ℂ)‖ < 1) {i j : Fin 4} (hij : i ≠ j) :
    physicalEntry D upperA c x slot colour i j 0 0 =
      (scaleRoot c x (slot i))⁻¹ *
        slitMatrix D (compactExternal D (currentSupport D (nativeColour D colour c)))
          (parameter c (x : ℂ))
          (chartTag D colour c i) (chartTag D colour c j) *
      (scaleRoot c x (slot j))⁻¹ := by
  have hs : slot i ≠ slot j := by
    intro h
    apply hij
    fin_cases i <;> fin_cases j <;> simp_all [slot]
  have hcorr : slotCorrection c x (slot i) (slot j) 0 0 = 0 := by
    rw [slotCorrection, ite_eq_right (fun h => hs (same_flags c h))]
  let a := flags c (slot i)
  let b := flags c (slot j)
  have hg := (chart_covariance_eq_native hx hx₁ upperA c hc a.1 b.1 a.2 b.2 hr).eq_of_nhds
  have hsmall : ‖(0 : ℂ)‖ + ‖parameter c (x : ℂ)‖ < 1 := by simpa using hr
  have hn := slitCovariance_eq_native a.1 b.1 a.2 b.2 hsmall hsmall
  have he : OriginalFourMSignedOverlap.chartCovariance upperA c x a.1 b.1 a.2 b.2 0 0 =
      OriginalFourMSlitMean.slitCovariance a.1 b.1 a.2 b.2 0 0 (parameter c (x : ℂ)) :=
    hg.trans hn.symm
  simp only [physicalEntry, physicalCovariance, rawLocal, zero_div, hcorr, sub_zero, jac,
    halfJacobian, inverseRoot_zero, one_pow, div_one, slitMatrix, compact_current_leg D colour c hc,
    compact_current_label D colour c hc, slitCovarianceEntry, coefficient_zero,
    LatticeHalfFock.gramComplex, Matrix.map_apply]
  change _ * (OriginalFourMSignedOverlap.chartCovariance upperA c x a.1 b.1 a.2 b.2 0 0 /
      (scaleRoot c x (slot i) * scaleRoot c x (slot j))) = _
  rw [he, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem chart_mean (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D)
    (upperA : Bool) (c : Chart) (hc : c = .A ∨ c = .B) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hr : ‖parameter c (x : ℂ)‖ < 1) (i : Fin 4) :
    physicalMean D q upperA c x slot colour i 0 =
      (scaleRoot c x (slot i))⁻¹ *
        ((bilinear D (unitCharge D (colour i)) q : ℂ) *
          slitLinear D (compactExternal D (currentSupport D (nativeColour D colour c)))
            (parameter c (x : ℂ)) (chartTag D colour c i)) := by
  let a := flags c (slot i)
  have hg := (chosen_chart_source_eq_native hx hx₁ c hc a.2 hr).eq_of_nhds
  have hsmall : ‖(0 : ℂ)‖ + ‖parameter c (x : ℂ)‖ < 1 := by simpa using hr
  have he : OriginalFourMSignedOverlap.chosenChartSource c x a.2 0 =
      OriginalFourMSlitMean.slitMean a.2 0 (parameter c (x : ℂ)) :=
    hg.trans (slitMean_eq_sourceMode a.2 hsmall).symm
  have hp : chartPeriod upperA c x = slitPeriod (parameter c (x : ℂ)) := by
    rcases hc with rfl | rfl <;> rfl
  simp only [physicalMean, physicalSource, rawLocal, zero_div, halfJacobian, inverseRoot_zero,
    one_pow, div_one, slitLinear, compact_current_leg D colour c hc,
    compact_current_label D colour c hc, slitMeanEntry, coefficient_zero, hp]
  change -_ * (OriginalFourMSignedOverlap.legSign a.1 *
    OriginalFourMSignedOverlap.chosenChartSource c x a.2 0 / _) / _ = _
  rw [he]
  simp only [div_eq_mul_inv]
  ring

private theorem chartA_radius {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) :
    ‖parameter .A (x : ℂ)‖ < 1 := by
  have hx₀ : 0 < x := by linarith
  have ha : 1 < x⁻¹ := (one_lt_inv₀ hx₀).2 hx₁
  have hb : x⁻¹ < 2 :=
    (inv_lt_comm₀ hx₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa only [one_div] using hx)
  rw [parameter, ← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr ha)]
  linarith

private theorem chartA_nome (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    Complex.exp (Complex.I * (Real.pi : ℂ) * chartTau upperA .A x) =
      slitNome (parameter .A (x : ℂ)) := by
  classical
  let r := parameter .A (x : ℂ)
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hr : r = ((1 - x⁻¹ : ℝ) : ℂ) := by simp [r, parameter]
  have hrlt : 1 - x⁻¹ < 0 := sub_neg.mpr ((one_lt_inv₀ hx).2 hx₁)
  have hrne : r ≠ 0 := by
    rw [hr]
    exact Complex.ofReal_ne_zero.mpr hrlt.ne
  have hrslit : r ∉ doubleSlit := by
    intro h
    have h' := Complex.mem_slitPlane_iff.mp h.2
    rw [hr] at h'
    simp only [Complex.ofReal_re, Complex.ofReal_im, ne_self_iff_false, or_false,
      not_lt.mpr hrlt.le] at h'
  have hpfaff : r / (r - 1) = 1 - (x : ℂ) := by
    change (1 - (x : ℂ)⁻¹) / (1 - (x : ℂ)⁻¹ - 1) = _
    rw [show 1 - (x : ℂ)⁻¹ - 1 = -(x : ℂ)⁻¹ by ring]
    field_simp [hxC]
    ring
  have hp : slitPeriod r ≠ 0 := (OriginalFourMChartProduct.chart_charge_data upperA .A hx hx₁).1
  have ht : chartTau upperA .A x = tau (1 - (x : ℂ)) + lipSign upperA := by
    change Complex.I * dPeriod upperA ((x : ℂ)⁻¹) / slitPeriod r = _
    rw [dPeriod, inv_inv]
    change Complex.I * ((tau (1 - (x : ℂ)) + lipSign upperA) * slitPeriod r / Complex.I) /
      slitPeriod r = _
    field_simp [Complex.I_ne_zero, hp]
  change _ = slitNome r
  rw [ht, slitNome, ite_eq_right hrne, nomeOffZero, ite_eq_right hrslit, negativeChartNome, hpfaff,
    mul_add, Complex.exp_add]
  cases upperA <;> simp [lipSign, mul_comm Complex.I (Real.pi : ℂ),
    Complex.exp_pi_mul_I, Complex.exp_neg_pi_mul_I]

private theorem chartB_nome (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    Complex.exp (Complex.I * (Real.pi : ℂ) * chartTau upperA .B x) =
      slitNome (parameter .B (x : ℂ)) := by
  have hslit : (x : ℂ) ∈ doubleSlit := by
    refine ⟨?_, Complex.ofReal_mem_slitPlane.2 hx⟩
    change 1 - (x : ℂ) ∈ Complex.slitPlane
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.2 (sub_pos.mpr hx₁)
  rw [show parameter .B (x : ℂ) = x from rfl,
    D5.S3.Analytic.OriginalSlitNome.slitNome_eq_exp hslit]
  congr 1
  congr 1
  change -1 / (Complex.I * slitPeriod (x : ℂ) / slitPeriod (1 - (x : ℂ))) =
    Complex.I * slitPeriod (1 - (x : ℂ)) / slitPeriod (x : ℂ)
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, Complex.inv_I, neg_one_mul, mul_neg,
    neg_neg]
  ring

private theorem chart_charge (D : LatticeData) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) (c : Chart) (x : ℝ)
    (hn : Complex.exp (Complex.I * (Real.pi : ℂ) * chartTau upperA c x) =
      slitNome (parameter c (x : ℂ))) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) =
      slitNome (parameter c (x : ℂ)) ^ (chargeEnergy D q).toNat := by
  rw [← hn, ← Complex.exp_nat_mul]
  have henergy : (bilinear D q q : ℂ) = 2 * ((chargeEnergy D q).toNat : ℂ) := by
    have hn : ((chargeEnergy D q).toNat : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg hq
    exact_mod_cast ((two_chargeEnergy D q).symm.trans (congrArg (2 * ·) hn.symm))
  rw [henergy]
  congr 1
  ring

open private rootB rootZ from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart

private theorem chartA_scale_product {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    (∏ i : Fin 4, (scaleRoot .A x (slot i))⁻¹) = -Complex.I / (1 - (x : ℂ)) := by
  have ha : rootB x ≠ 0 := root_ne hx hx₁ .A .P
  have hb : rootZ x ≠ 0 := root_ne hx hx₁ .A .R
  have hs : rootB x ^ 2 = 1 - (x : ℂ) := (chosen_roots hx hx₁ .A .P).1
  rw [← hs]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (rootB x)⁻¹ * ((Complex.I * rootB x)⁻¹ * ((rootZ x)⁻¹ * ((rootZ x)⁻¹)⁻¹)) = _
  rw [inv_inv, inv_mul_cancel₀ hb, mul_one, mul_inv_rev, Complex.inv_I]
  field_simp [ha]

private theorem chartA_normalization (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    (chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
      (∏ i : Fin 4, (scaleRoot .A x (slot i))⁻¹) =
      (-Complex.I / ((x : ℂ)^3 * (1 - (x : ℂ)))) *
        rank24Determinant (parameter .A (x : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [chartA_scale_product hx hx₁, rank24Determinant]
  have hr : 1 - parameter .A (x : ℂ) = (x : ℂ)⁻¹ := by simp [parameter]
  rw [hr, inv_pow, inv_inv]
  change _ * _ = _ * ((x : ℂ)^3 * (chartPeriod upperA .A x ^ (12 : ℕ))⁻¹)
  have hxc₁ : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  field_simp [hxC, hxc₁]

private theorem chartB_radius {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    ‖parameter .B (x : ℂ)‖ < 1 := by
  simpa [parameter, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using hx₁

private theorem chartB_normalization (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    (chartPeriod upperA .B x ^ (12 : ℕ))⁻¹ *
      (∏ i : Fin 4, relative .B (slot i) * (scaleRoot .B x (slot i))⁻¹) =
      (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)) *
        rank24Determinant (parameter .B (x : ℂ)) := by
  have hs : rootZ x ^ 2 = (x : ℂ) := (chosen_roots hx hx₁ .B .Q).1
  have h₁ : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hscale : (∏ i : Fin 4, relative .B (slot i) * (scaleRoot .B x (slot i))⁻¹) =
      -Complex.I / (x : ℂ) := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change 1 * Complex.I⁻¹ * (1 * (rootZ x)⁻¹ *
      (1 * (Complex.I * rootZ x)⁻¹ * (-1 * Complex.I⁻¹))) = _
    rw [div_eq_mul_inv, ← hs, ← inv_pow]
    simp only [one_mul, neg_one_mul, mul_inv_rev, Complex.inv_I, neg_neg]
    calc
      _ = (Complex.I * Complex.I * Complex.I) * (rootZ x)⁻¹ ^ 2 := by ring
      _ = _ := by rw [← pow_two, Complex.I_sq, neg_one_mul]
  rw [hscale, rank24Determinant]
  change (slitPeriod (x : ℂ) ^ (12 : ℕ))⁻¹ * (-Complex.I / (x : ℂ)) =
    (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)) *
      (((1 - (x : ℂ)) ^ (3 : ℕ))⁻¹ * (slitPeriod (x : ℂ) ^ (12 : ℕ))⁻¹)
  field_simp [hxC, h₁]


private theorem four_current_fixed_charge
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) (c : Chart) (hc : c = .A ∨ c = .B)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (hr : ‖parameter c (x : ℂ)‖ < 1)
    (hn : Complex.exp (Complex.I * (Real.pi : ℂ) * chartTau upperA c x) =
      slitNome (parameter c (x : ℂ))) (k : ℂ)
    (hk : (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        (∏ i : Fin 4, relative c (slot i) * (scaleRoot c x (slot i))⁻¹) =
      k * rank24Determinant (parameter c (x : ℂ))) :
    let osc := fun i =>
      MvPolynomial.monomial (currentExponent D (nativeColour D colour c) i) (1 : ℂ)
    (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (marks.map Sum.inr ++ marks.map Sum.inl)
        (physicalChargeSummand D slot colour upperA c x q) 0 =
      k * projectOccupations D 2 2 0 (-1) (osc 0) (osc 1) (osc 2) (osc 3)
        (fun b g d e => slitChargeTerm D b g d e q (parameter c (x : ℂ))) := by
  classical
  let r := parameter c (x : ℂ)
  let cols := nativeColour D colour c
  let label := compactExternal D (currentSupport D cols)
  let tag := chartTag D colour c
  let T := CompactExternal D (currentSupport D cols)
  let K : Matrix (T ⊕ T) (T ⊕ T) ℂ := slitMatrix D label r
  let eta := fun t =>
    (bilinear D (unitCharge D (Sum.elim label label t).2.1) q : ℂ) * slitLinear D label r t
  let B : Matrix (Fin 4) (Fin 4) ℂ := fun i j => K (tag i) (tag j)
  let nu : Fin 4 → ℂ := fun i => eta (tag i)
  let A : Matrix (Fin 4) (Fin 4) ℂ := fun i j => physicalEntry D upperA c x slot colour i j 0 0 *
    relative c (slot i) * relative c (slot j)
  let mu := fun i => physicalMean D q upperA c x slot colour i 0 * relative c (slot i)
  let w := fun i => relative c (slot i) * (scaleRoot c x (slot i))⁻¹
  let d := jetOccupation marks
  have hA (i j : Fin 4) : A i j = A j i := by
    simp only [A, physicalEntry]
    rw [physical_covariance_swap upperA c x (slot i) (slot j) 0 0,
      D.symmetric (colour i) (colour j)]
    ring
  have hOff (i j : Fin 4) (hij : i ≠ j) : A i j = w i * B i j * w j := by
    dsimp only [A, w, B, K, tag, label, cols, r]
    rw [chart_entry D colour upperA c hc hx hx₁ hr hij]
    ring
  have hMean (i : Fin 4) : mu i = w i * nu i := by
    dsimp only [mu, nu, eta, w, tag, label, cols, r]
    rw [chart_mean D colour q upperA c hc hx hx₁ hr i, compact_current_label D colour c hc]
    ring
  have hMark :
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (marks.map Sum.inr ++ marks.map Sum.inl)
        (physicalChargeSummand D slot colour upperA c x q) 0 =
          slitNome r ^ (chargeEnergy D q).toNat * ((∏ i, w i) * affineCoefficient B nu d) := by
    rw [spatialCoefficient_split_marks _ marks (by decide : marks.Nodup), spatial_zero]
    have h := mark_jet_eq_moment D slot colour upperA c x q marks (0 : Fin 4 → ℂ)
    simp only [Pi.zero_apply] at h
    rw [h, chart_charge D q hq upperA c x hn]
    exact congrArg (_ * ·) (four_mark_rescale A B mu nu w hA hOff hMean)
  have hNative :
      slitChargeTerm D (currentExponent D cols 0) (currentExponent D cols 1)
        (currentExponent D cols 2) (currentExponent D cols 3) q r =
      rank24Determinant r * slitNome r ^ (chargeEnergy D q).toNat * affineCoefficient B nu d := by
    unfold slitChargeTerm
    dsimp only
    rw [current_occupation, chart_occupation]
    exact congrArg (fun z => rank24Determinant r * slitNome r ^ (chargeEnergy D q).toNat * z)
      (affine_enlarge K eta tag d)
  dsimp only
  change (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ * spatialCoefficient _ _ _ 0 =
    _ * projectOccupations D 2 2 0 (-1) _ _ _ _ _
  rw [hMark, project_four_currents D cols, hNative]
  calc
    _ = ((chartPeriod upperA c x ^ (12 : ℕ))⁻¹ * ∏ i, w i) *
          (slitNome r ^ (chargeEnergy D q).toNat * affineCoefficient B nu d) := by ring
    _ = _ := by
      rw [hk]
      ring

/-- The fixed-charge physical A coefficient for four lowest currents equals
the native slit occupation projection. At rank 24 these currents have full
weight two at each puncture. -/
theorem chartA_four_current_fixed_charge
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) :
    let slot : Fin 4 → Puncture := ![.P, .Q, .R, .S]
    let l : List (Fin 4) := [0, 1, 2, 3]
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    (chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (l.map Sum.inr ++ l.map Sum.inl) (physicalChargeSummand D slot colour upperA .A x q) 0 =
      (-Complex.I / ((x : ℂ)^3 * (1 - (x : ℂ)))) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 1) (osc 2) (osc 3)
          (fun b g d e => slitChargeTerm D b g d e q (parameter .A (x : ℂ))) := by
  have hx₀ : 0 < x := by linarith
  exact four_current_fixed_charge D colour q hq upperA .A (.inl rfl) hx₀ hx₁
    (chartA_radius hx hx₁) (chartA_nome upperA hx₀ hx₁) _
    (by simpa only [relative, one_mul] using chartA_normalization upperA hx₀ hx₁)

/-- The fixed-charge physical B coefficient equals the native projection in
puncture order Q, R, P, S. The relative sign at S is included in the scalar. -/
theorem chartB_four_current_fixed_charge
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) :
    let slot : Fin 4 → Puncture := ![.P, .Q, .R, .S]
    let l : List (Fin 4) := [0, 1, 2, 3]
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    (chartPeriod upperA .B x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
        (l.map Sum.inr ++ l.map Sum.inl) (physicalChargeSummand D slot colour upperA .B x q) 0 =
      (-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)) *
        projectOccupations D 2 2 0 (-1) (osc 1) (osc 2) (osc 0) (osc 3)
          (fun b g d e => slitChargeTerm D b g d e q (parameter .B (x : ℂ))) := by
  exact four_current_fixed_charge D colour q hq upperA .B (.inr rfl) hx hx₁
    (chartB_radius hx hx₁) (chartB_nome upperA hx hx₁) _
    (chartB_normalization upperA hx hx₁)

#print axioms chartA_four_current_fixed_charge
#print axioms chartB_four_current_fixed_charge

open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient
  (ModTwoCharge reduceCharge mod_two_cocycle_symmetrization)
open FourPoint.FourPointChannelCoefficients (loweringCutoff loweredLaurent loweringWeight laurent)
open OriginalFourMChargeCoset (slitDiagonal slitChannelA slitChannelB slitLowered
  quadraticSign fourierSign oscillatorLower)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSpatialWick (physical_chart_jet_hasSum physical_chart_coefficient_overlap)
open OriginalFourMChartProduct (chart_charge_data)
open OriginalFourMSectorContinuation (slitChargeSector)
open private slitLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

private abbrev currentOscillator (D : LatticeData) (colour : Fin 4 → Fin D.rank) (i : Fin 4) :
    Oscillator D := MvPolynomial.monomial (currentExponent D colour i) 1

private abbrev fourCurrentJet (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin 4 → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ) (a : ModTwoCharge D) :=
  spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
    (marks.map Sum.inr ++ marks.map Sum.inl)
    (fun z => physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0

private theorem four_current_sector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (colour cols : Fin 4 → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (a : ModTwoCharge D) (k : ℂ)
    (hfixed : ∀ q : Charge D, 0 ≤ chargeEnergy D q →
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
          (marks.map Sum.inr ++ marks.map Sum.inl)
          (physicalChargeSummand D slot colour upperA c x q) 0 =
      k * projectOccupations D 2 2 0 (-1) (currentOscillator D cols 0)
        (currentOscillator D cols 1) (currentOscillator D cols 2) (currentOscillator D cols 3)
        (fun b g d e => slitChargeTerm D b g d e q (parameter c (x : ℂ)))) :
    fourCurrentJet D hu colour upperA c x a =
      k * slitDiagonal D 2 2 2 (currentOscillator D cols 0) (currentOscillator D cols 1)
        (currentOscillator D cols 2) (currentOscillator D cols 3) a (parameter c (x : ℂ)) := by
  classical
  obtain ⟨hp, hτ⟩ := chart_charge_data upperA c hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp hτ a
    (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
    (marks.map Sum.inr ++ marks.map Sum.inl)
  rw [fourCurrentJet, ← hs.tsum_eq]
  simp_rw [fun q => hfixed q (chargeEnergy_nonneg D hD q), project_four_currents D cols]
  rw [tsum_mul_left]
  congr 1
  change _ = projectOccupations D 2 2 0 (-1) _ _ _ _
    (fun b g d e => slitChargeSector D a b g d e (parameter c (x : ℂ)))
  rw [project_four_currents D cols, slitChargeSector]
  let f (q : Charge D) := slitChargeTerm D (currentExponent D cols 0) (currentExponent D cols 1)
    (currentExponent D cols 2) (currentExponent D cols 3) q (parameter c (x : ℂ))
  let fibre : Set (Charge D) := {q | reduceCharge D q = a}
  calc
    _ = ∑' q, fibre.indicator f q := tsum_subtype fibre f
    _ = _ := by
      apply tsum_congr
      intro q
      by_cases h : reduceCharge D q = a <;> simp [fibre, Set.indicator, f, h]

/-- Real A–B crossing of the continued native channels for four weight-two
currents and total mode two, with the charge signs of the slit channels. -/
theorem four_current_slit_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (hs : m + n + r = 2) (a : ModTwoCharge D)
    {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) :
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) a
        (parameter .A (x : ℂ)) =
      (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (4 : ℕ) *
        slitChannelB D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a
          (parameter .B (x : ℂ)) := by
  classical
  dsimp only
  let osc := currentOscillator D colour
  let tA := parameter .A (x : ℂ)
  let tB := parameter .B (x : ℂ)
  let diagA (b : ModTwoCharge D) := slitDiagonal D 2 2 2 (osc 0) (osc 1) (osc 2) (osc 3) b tA
  let B := slitDiagonal D 2 2 2 (osc 1) (osc 2) (osc 0) (osc 3) a tB
  let A := ∑ b, quadraticSign D b * fourierSign D b a * diagA b
  let kA := -Complex.I / ((x : ℂ) ^ 3 * (1 - (x : ℂ)))
  let kB := -Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)
  have hx₀ : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀.ne'
  have h₁ : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne')
  let w := Complex.sqrt tA
  have hwA : w ^ 2 = tA := Complex.cpow_nat_inv_pow tA (by decide : (2 : ℕ) ≠ 0)
  have hw : ‖w‖ < 1 := by
    have hnorm : ‖w‖ ^ 2 < 1 := by
      rw [← norm_pow, hwA]
      exact chartA_radius hx hx₁
    nlinarith [norm_nonneg w]
  have hperiod : (periodRoot .A x ^ (12 : ℕ))⁻¹ = (x : ℂ) ^ 6 := by
    have hroot : periodRoot .A x ^ 2 = (x : ℂ)⁻¹ := by
      have h := (chosen_roots hx₀ hx₁ .A .P).2
      change periodRoot .A x ^ 2 = 1 - (1 - (x : ℂ)⁻¹) at h
      simpa only [sub_sub_cancel] using h
    rw [show (12 : ℕ) = 2 * 6 by decide, pow_mul, hroot, inv_pow, inv_inv]
  have hAjet (b : ModTwoCharge D) :
      fourCurrentJet D hu colour true .A x b = kA * diagA b :=
    four_current_sector D hu hD colour colour true .A hx₀ hx₁ b kA
      (fun q hq => chartA_four_current_fixed_charge D colour q hq true hx hx₁)
  have hBjet : fourCurrentJet D hu colour true .B x a = kB * B :=
    four_current_sector D hu hD colour (nativeColour D colour .B) true .B hx₀ hx₁ a kB
      (fun q hq => chartB_four_current_fixed_charge D colour q hq true hx₀ hx₁)
  have hover := (physical_chart_coefficient_overlap D hu hD h24 slot colour true hx₀ hx₁ hwA hw
    (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
    (marks.map Sum.inr ++ marks.map Sum.inl) a).2
  change fourCurrentJet D hu colour true .B x a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
    (((2 : ℂ) ^ (12 : ℕ))⁻¹ *
      ∑ b, fourierSign D a b * quadraticSign D b * fourCurrentJet D hu colour true .A x b) at hover
  have hfourier (b : ModTwoCharge D) : fourierSign D a b = fourierSign D b a := by
    unfold fourierSign
    rw [← mod_two_cocycle_symmetrization D a b, ← mod_two_cocycle_symmetrization D b a, add_comm]
  have hsum : (∑ b, fourierSign D a b * quadraticSign D b * (kA * diagA b)) = kA * A := by
    rw [show A = _ from rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hfourier]; ring
  rw [hBjet, hperiod] at hover
  simp only [hAjet, hsum] at hover
  have hLaurent : (-tA) ^ (-(4 : ℤ)) = ((1 - (x : ℂ)) ^ 4)⁻¹ * (x : ℂ) ^ 4 := by
    have ht : -tA = (1 - (x : ℂ)) / (x : ℂ) := by
      change -(1 - (x : ℂ)⁻¹) = _
      field_simp [hxC]
      ring
    rw [ht, zpow_neg]
    change (((1 - (x : ℂ)) / (x : ℂ)) ^ (4 : ℕ))⁻¹ = _
    rw [div_pow, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm]
  have hA : slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) a tA =
      (-tA) ^ (-(4 : ℤ)) * A := by
    rw [hs]
    norm_num [slitChannelA, slitLaurent, A, diagA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hN : loweringCutoff 2 2 2 m n r = 1 := by
    unfold loweringCutoff
    omega
  have hB : slitChannelB D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a tB =
      ((x : ℂ) ^ 4)⁻¹ * B := by
    rw [slitChannelB, hs, hN]
    norm_num [slitLowered, loweredLaurent, loweringWeight, laurent, B, tB, parameter,
      Module.End.one_apply, zpow_neg, neg_pow]
  change slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) a tA =
    (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (4 : ℕ) *
      slitChannelB D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a tB
  rw [hA, hB, hLaurent]
  have hkB : kB ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (pow_ne_zero _ h₁)) hxC
  apply mul_left_cancel₀ hkB
  calc
    _ = (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ) *
        (((2 : ℂ) ^ (12 : ℕ))⁻¹ * (kA * A))) := by
      dsimp only [kA, kB]
      field_simp [hxC, h₁]
    _ = _ := by
      rw [← hover]
      field_simp [hxC]

#print axioms four_current_slit_crossing

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent
