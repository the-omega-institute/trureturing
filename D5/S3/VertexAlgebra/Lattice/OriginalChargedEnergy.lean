/- GID: D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform polynomial energy bounds for the original neutral and charged lattice fields. -/

import D5.S3.VertexAlgebra.Energy.OriginalNeutralEnergy

/-! Uniform analytic estimates on the original finite charge/oscillator carrier.

The new estimates use the full integer-frequency factorial form after inverse
colour substitution, including interference between different original colours.
The literal two-branch normal-product recursion gives finite general-mode bounds;
the intervening negative-current strip has zero derivative multiplier. No current
factors are commuted. Exact orthogonal energy recombination uses the actual
Sugawara zero mode with both complex inverse laws.

proof_shape: neutral_energy_bound: content; charged_energy_bound: content
admission_basis: escape-witness
escape_witness: The mixed-direction finite Fock inequality and the uniform
finite normal-product word estimate lie on the neutral and charged proof paths.
The charged theorem additionally consumes the original positive quadratic
identity and the opposite-charge adjoint at the actual shifted output energy.
These are analytic energy bounds, not a construction of smeared closed fields,
strong locality, string theory or an AdS/CFT correspondence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator Matrix
open ComplexConjugate

namespace D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open SourceBPZ.OriginalMatterHermitian SourceBPZ.OriginalSourcePairing
open SourceBPZ.TransverseHermitian OriginalGram
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualGeneratorLocality
open private Hm_finsum_right Hm_finset_sum_left Hm_finset_sum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

variable {D : LatticeData}

open private original_nonnegative normD_sq normD_smul from
  D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy

open private neutralConstant neutralConstant_pos original_neutral_grade_le Hm_cauchy_schwarz energy_bound_of_grades original_neutral_energy_le from
  D5.S3.VertexAlgebra.Energy.OriginalNeutralEnergy

private theorem charged_weight (hD : (gramReal D).PosDef) (a : Charge D)
    (ha : a ≠ 0) :
    0 < (chargeEnergy D a).toNat ∧
      ((chargeEnergy D a).toNat : ℤ) = bilinear D a a / 2 := by
  have hn := chargeEnergy_nonneg D hD a
  have hz := (chargeEnergy_eq_zero_iff D hD a).not.mpr ha
  constructor
  · omega
  · exact Int.toNat_of_nonneg hn

private theorem kappa_creationSeries (a : Charge D) :
    PowerSeries.map (MvPolynomial.map (starRingEnd ℂ)) (creationSeries D a) =
      creationSeries D a := by
  ext q
  simp only [PowerSeries.coeff_map, creationSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_sum, Algebra.smul_def]

private theorem kappa_creationExponential (a : Charge D) :
    PowerSeries.map (MvPolynomial.map (starRingEnd ℂ)) (creationExponential D a) =
      creationExponential D a := by
  have hs : PowerSeries.HasSubst (creationSeries D a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have hm := PowerSeries.map_subst (h := MvPolynomial.map (starRingEnd ℂ)) hs
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (MvPolynomial.map (starRingEnd ℂ)) (creationExponential D a) =
    (PowerSeries.map (MvPolynomial.map (starRingEnd ℂ))
      (PowerSeries.exp (Oscillator D))).subst
        (PowerSeries.map (MvPolynomial.map (starRingEnd ℂ)) (creationSeries D a)) at hm
  rw [hm, PowerSeries.map_exp, kappa_creationSeries]
  rfl

private theorem kappa_creationCoeff (a : Charge D) (t : ℤ) :
    kappaOsc (creationCoeff D a t) = creationCoeff D a t := by
  unfold creationCoeff
  split_ifs
  · simp [kappaOsc]
  · change (MvPolynomial.map (starRingEnd ℂ))
      (PowerSeries.coeff _ (creationExponential D a)) = _
    rw [← PowerSeries.coeff_map, kappa_creationExponential]

private theorem kappa_translationVariable (a : Charge D) (x : Index D) :
    Polynomial.map (MvPolynomial.map (starRingEnd ℂ)) (translationVariable D a x.1 x.2) =
      translationVariable D a x.1 x.2 := by
  simp [translationVariable, Algebra.smul_def]

private theorem kappa_translatedPolynomial (a : Charge D) (p : Oscillator D) :
    Polynomial.map (MvPolynomial.map (starRingEnd ℂ)) (translatedPolynomial D a p) =
      translatedPolynomial D a (kappaOsc p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [translatedPolynomial]
  | add p q hp hq =>
      simp only [translatedPolynomial, map_add, Polynomial.map_add,
        kappaOsc_add] at hp hq ⊢
      rw [hp, hq]
  | mul_X p x hp =>
      simp only [kappaOsc_mul, kappaOsc_X, translatedPolynomial, map_mul,
        Polynomial.map_mul, MvPolynomial.eval₂Hom_X'] at hp ⊢
      rw [hp, kappa_translationVariable]

private theorem kappa_translated_coeff (a : Charge D) (p : Oscillator D) (j : ℕ) :
    (translatedPolynomial D a (kappaOsc p)).coeff j =
      kappaOsc ((translatedPolynomial D a p).coeff j) := by
  rw [← kappa_translatedPolynomial, Polynomial.coeff_map]
  rfl

private theorem kappa_translated_support (a : Charge D) (p : Oscillator D) :
    (translatedPolynomial D a (kappaOsc p)).support = (translatedPolynomial D a p).support := by
  classical
  ext j
  simp only [Polynomial.mem_support_iff, kappa_translated_coeff]
  have hk : Function.Involutive (@kappaOsc D) := kappaOsc_involutive
  exact hk.injective.ne_iff' (by simp [kappaOsc])

private theorem kappa_epsilon (a b : Charge D) : conj (epsilon D a b) = epsilon D a b := by
  unfold epsilon paritySign
  split_ifs <;> simp

private theorem kappa_rawSingle (a : Charge D) (k : ℤ) (b : Charge D)
    (p : Oscillator D) :
    kappaCarrier (rawSingle D a k b p) = rawSingle D a k b (kappaOsc p) := by
  classical
  simp only [rawSingle, kappaCarrier_smul, kappa_epsilon, kappaCarrier_single,
    kappa_translated_support, kappa_translated_coeff]
  congr 2
  change (MvPolynomial.map (starRingEnd ℂ)) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change kappaOsc (_ • _) = _
  rw [smul_eq_mul, kappaOsc_mul, kappa_creationCoeff, smul_eq_mul]

private theorem kappa_rawCoeff (a : Charge D) (k : ℤ) (v : Carrier D) :
    kappaCarrier (rawCoeff D a k v) = rawCoeff D a k (kappaCarrier v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, kappaCarrier_add, hv, hw]
  | single b p =>
      rw [kappaCarrier_single, (actual_creation_coefficient_transport D a a).2.2.1,
        (actual_creation_coefficient_transport D a a).2.2.1]
      exact kappa_rawSingle a k b p

private theorem Hm_rawCoeff (a : Charge D) (k : ℤ) (u v : Carrier D) :
    Hm (D := D) (rawCoeff D a k u) v =
      paritySign (chargeEnergy D a) * Hm (D := D) u (rawCoeff D (-a) (-k-bilinear D a a) v) := by
  unfold Hm
  rw [kappa_rawCoeff, theta_rawCoeff, SourceBPZ.ChargedRawTranspose.sourcePairing_rawCoeff]
  rw [bilinear_neg_neg]
  rfl

private theorem Hm_charged_circle (a : Charge D) (m : ℤ) (u v : Carrier D) :
    Hm (D := D) (((actualField D a)[[m + chargeEnergy D a - 1]]) u) v =
      Hm (D := D) u (paritySign (chargeEnergy D a) •
        (((actualField D (-a))[[-m + chargeEnergy D a - 1]]) v)) := by
  have he := two_chargeEnergy D a
  have hi : -(-(m + chargeEnergy D a - 1)-1)-bilinear D a a =
      -(-m + chargeEnergy D a - 1)-1 := by omega
  have h := Hm_rawCoeff (D := D) a (-(m + chargeEnergy D a - 1)-1) u v
  rw [hi] at h
  simpa only [Hm_smul_right, actual_modes] using h

private theorem actual_phase (a : Charge D) :
    epsilon D a (-a) = paritySign (chargeEnergy D a) := by
  have hn : lowerCocycleExponent D a (-a) = -lowerCocycleExponent D a a := by
    simp [lowerCocycleExponent, Finset.sum_neg_distrib, add_comm]
  rw [epsilon, hn, chargeEnergy_cocycle]
  simp only [paritySign, even_neg]

private theorem Hm_charged_mode (a : Charge D) (n : ℤ) (u v : Carrier D) :
    Hm (D := D) (((actualField D a)[[n]]) u) v =
      Hm (D := D) u (paritySign (chargeEnergy D a) •
        (((actualField D (-a))[[2 * chargeEnergy D a - n - 2]]) v)) := by
  have he := two_chargeEnergy D a
  have hi : -(-n-1)-bilinear D a a = -(2*chargeEnergy D a-n-2)-1 := by omega
  have h := Hm_rawCoeff (D := D) a (-n-1) u v
  rw [hi] at h
  simpa only [Hm_smul_right, actual_modes] using h

private def oppositeField (a : Charge D) : VertexOperator ℂ (Carrier D) :=
  paritySign (chargeEnergy D a) • actualField D (-a)

private theorem opposite_coeff (a : Charge D) (n : ℤ) (v : Carrier D) :
    ((oppositeField a)[[n]]) v =
      paritySign (chargeEnergy D a) • (((actualField D (-a))[[n]]) v) := by
  change ((VertexOperator.ncoeff (paritySign (chargeEnergy D a) • actualField D (-a))) n) v = _
  rw [map_smul]
  rfl

private theorem raising_modes_finite (F : VertexOperator ℂ (Carrier D))
    (n : ℤ) (v : Carrier D) :
    Function.HasFiniteSupport (fun r : ℕ => ((F[[n+r]]) v)) := by
  classical
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (F v)).order - n).toNat, ?_⟩
  intro r hr
  contrapose! hr
  have hz : ((F[[n+r]]) v) = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private def normalLeft (a : Charge D) (v : Carrier D) (r : ℕ) : Carrier D :=
  ((actualField D a)[[-(r : ℤ)-1]])
    (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)

private def normalRight (a : Charge D) (v : Carrier D) (r : ℕ) : Carrier D :=
  ((oppositeField a)[[2*chargeEnergy D a-2-r]])
    (((actualField D a)[[(r : ℤ)]]) v)

private theorem normalLeft_finite (a : Charge D) (v : Carrier D) :
    Function.HasFiniteSupport (normalLeft a v) := by
  refine (raising_modes_finite (oppositeField a) (2*chargeEnergy D a-1) v).subset ?_
  intro r hr
  contrapose! hr
  simp only [Function.mem_support, not_not] at hr ⊢
  simp [normalLeft, hr]

private theorem normalRight_finite (a : Charge D) (v : Carrier D) :
    Function.HasFiniteSupport (normalRight a v) := by
  refine (raising_modes_finite (actualField D a) 0 v).subset ?_
  intro r hr
  contrapose! hr
  simp only [Function.mem_support, not_not] at hr ⊢
  simp only [zero_add] at hr
  unfold normalRight
  rw [hr, map_zero]

private theorem normalLeft_pairing (a : Charge D) (v : Carrier D) (r : ℕ) :
    Hm (D := D) v (normalLeft a v r) =
      Hm (D := D) (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)
        (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v) := by
  unfold normalLeft
  rw [Hm_hermitian v, Hm_charged_mode]
  have he : 2*chargeEnergy D a - (-(r : ℤ)-1) - 2 =
      2*chargeEnergy D a-1+r := by omega
  rw [he, ← opposite_coeff, ← Hm_hermitian]

private theorem normalRight_pairing (a : Charge D) (v : Carrier D) (r : ℕ) :
    Hm (D := D) v (normalRight a v r) =
      Hm (D := D) (((actualField D a)[[(r : ℤ)]]) v)
        (((actualField D a)[[(r : ℤ)]]) v) := by
  unfold normalRight
  rw [opposite_coeff]
  have he : 2*chargeEnergy D a-2-r = 2*chargeEnergy D a-r-2 := by omega
  rw [he, ← Hm_charged_mode]

private def neutralState (a : Charge D) : Carrier D :=
  mu D (Finsupp.single a 1) (-1)
    (paritySign (chargeEnergy D a) • Finsupp.single (-a) 1)

private theorem neutralState_field (a : Charge D) :
    Y D (neutralState a) =
      (FieldNormalProduct.normalMinusOne (actualField D a) (oppositeField a)).1 := by
  unfold neutralState oppositeField
  rw [LatticeActualStateFieldCalculus.minus_one_product_field, stateField_ground,
    map_smul, stateField_ground]

private theorem neutralState_original (a : Charge D) :
    neutralState a = Finsupp.single 0 (creationCoeff D a (2*chargeEnergy D a)) := by
  unfold neutralState mu
  rw [stateField_ground, actual_modes, map_smul, LatticeActualOrderedProducts.raw_ground]
  rw [show -(-1 : ℤ)-1 = 0 by omega,
    LatticeFiniteNegativeGeneration.bilinear_neg_right, actual_phase]
  rw [smul_smul, paritySign_square, one_smul]
  simp only [add_neg_cancel]
  congr 2
  have he := two_chargeEnergy D a
  omega

private theorem charged_normal_quadratic (a : Charge D) (v : Carrier D) :
    Hm (D := D) v (((Y D (neutralState a))[[2*chargeEnergy D a-1]]) v) =
      (∑ᶠ r : ℕ, Hm (D := D) (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)
        (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)) +
      (∑ᶠ r : ℕ, Hm (D := D) (((actualField D a)[[(r : ℤ)]]) v)
        (((actualField D a)[[(r : ℤ)]]) v)) := by
  have he := (FieldNormalProduct.normalMinusOne (actualField D a) (oppositeField a)).2
    (2*chargeEnergy D a-1) v
  have hi (r : ℕ) : 2*chargeEnergy D a-1-r-1 = 2*chargeEnergy D a-2-r := by omega
  simp_rw [hi] at he
  rw [neutralState_field, he]
  change Hm (D := D) v ((∑ᶠ r : ℕ, normalLeft a v r) + (∑ᶠ r : ℕ, normalRight a v r)) = _
  rw [Hm_add_right, Hm_finsum_right _ (normalLeft_finite a v),
    Hm_finsum_right _ (normalRight_finite a v)]
  simp_rw [normalLeft_pairing, normalRight_pairing]

private theorem charged_annihilating_square_le (hD : (gramReal D).PosDef)
    (a : Charge D) (r : ℕ) (v : Carrier D) :
    normD (((actualField D a)[[(r : ℤ)]]) v) ^ 2 ≤
      (Hm (D := D) v (((Y D (neutralState a))[[2*chargeEnergy D a-1]]) v)).re := by
  rw [normD_sq hD, charged_normal_quadratic, Complex.add_re]
  have leftFinite := raising_modes_finite (oppositeField a) (2*chargeEnergy D a-1) v
  have rightFinite := raising_modes_finite (actualField D a) 0 v
  have lp : Function.HasFiniteSupport (fun r : ℕ =>
      Hm (D := D) (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)
        (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)) := by
    refine leftFinite.subset ?_
    intro r hr
    contrapose! hr
    simp only [Function.mem_support, not_not] at hr ⊢
    simp only [hr, Hm_zero_left]
  have rp : Function.HasFiniteSupport (fun r : ℕ =>
      Hm (D := D) (((actualField D a)[[(r : ℤ)]]) v)
        (((actualField D a)[[(r : ℤ)]]) v)) := by
    refine rightFinite.subset ?_
    intro r hr
    contrapose! hr
    simp only [Function.mem_support, not_not] at hr ⊢
    simp only [zero_add] at hr
    simp only [hr, Hm_zero_left]
  change _ ≤ Complex.reAddGroupHom _ + Complex.reAddGroupHom _
  rw [Complex.reAddGroupHom.map_finsum lp, Complex.reAddGroupHom.map_finsum rp]
  have hrp : Function.HasFiniteSupport (fun r : ℕ =>
      (Hm (D := D) (((actualField D a)[[(r : ℤ)]]) v)
        (((actualField D a)[[(r : ℤ)]]) v)).re) :=
    rp.subset (by intro r hr; contrapose! hr; simp_all)
  have hs := single_le_finsum r hrp (fun j => original_nonnegative hD
    (((actualField D a)[[(j : ℤ)]]) v))
  have hl : 0 ≤ ∑ᶠ r : ℕ, (Hm (D := D) (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)
        (((oppositeField a)[[2*chargeEnergy D a-1+r]]) v)).re :=
    finsum_nonneg (fun _ => original_nonnegative hD _)
  exact hs.trans (le_add_of_nonneg_left hl)

private def chargedConstant (a : Charge D) : ℝ :=
  Real.sqrt (neutralConstant (creationCoeff D a (2*chargeEnergy D a)))

private theorem chargedConstant_pos (a : Charge D) : 0 < chargedConstant a :=
  Real.sqrt_pos.mpr (neutralConstant_pos _)

private theorem charged_mode_grade (a : Charge D) (E m : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    ((actualField D a)[[m+chargeEnergy D a-1]]) v ∈ grade D (E-m) := by
  have hs : Finsupp.single a (1 : Oscillator D) ∈ grade D (chargeEnergy D a) := by
    rw [grade_eq_span]
    apply Submodule.subset_span
    refine ⟨(a,0), ?_, ?_⟩
    · simp [energy, oscillatorEnergy]
    · simp [carrierBasis_apply]
  have hg := LatticeCoefficientEnergy.actual_mode_grade D (chargeEnergy D a) E
    (m+chargeEnergy D a-1) (Finsupp.single a 1) v hs hv
  rw [stateField_ground] at hg
  convert hg using 1 <;> congr 1 <;> omega

private theorem charged_positive_mode_grade_le (hD : (gramReal D).PosDef)
    (a : Charge D) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((actualField D a)[[r]]) v) ≤
      chargedConstant a * ((E : ℝ)+1)^(2*(chargeEnergy D a).toNat) * normD v := by
  let d := (chargeEnergy D a).toNat
  have hd : (d : ℤ)=chargeEnergy D a := Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a)
  have hw : (2*chargeEnergy D a).toNat=2*d := by omega
  have hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1)
      (creationCoeff D a (2*chargeEnergy D a)) (2*d) := by
    intro e he
    have hh := (actual_creation_coefficient_transport D a a).1 (2*chargeEnergy D a) he
    simpa only [Finsupp.weight_apply, hw, LatticeGeneratingFieldLocality.oscillatorWeight]
      using hh
  have hz := original_neutral_grade_le hD _ (2*d) hp E v hv
  have hn : ((Y D (neutralState a))[[2*chargeEnergy D a-1]]) v =
      ((Y D (Finsupp.single 0 (creationCoeff D a (2*chargeEnergy D a))))
        [[((2*d : ℕ) : ℤ)-1]]) v := by
    have hi : 2*chargeEnergy D a-1=((2*d : ℕ) : ℤ)-1 := by push_cast; omega
    rw [neutralState_original, hi]
  have hq := charged_annihilating_square_le hD a r v
  rw [hn] at hq
  have hcs := (Complex.re_le_norm _).trans (Hm_cauchy_schwarz hD v
    (((Y D (Finsupp.single 0 (creationCoeff D a (2*chargeEnergy D a))))
      [[((2*d : ℕ) : ℤ)-1]]) v))
  have hnormv : 0 ≤ normD v := Real.sqrt_nonneg _
  have hs : normD (((actualField D a)[[r]]) v)^2 ≤
      normD v * (neutralConstant (creationCoeff D a (2*chargeEnergy D a)) *
        ((E : ℝ)+1)^(2*(2*d)) * normD v) :=
    hq.trans (hcs.trans (mul_le_mul_of_nonneg_left hz hnormv))
  have hconst : chargedConstant a ^ 2 =
      neutralConstant (creationCoeff D a (2*chargeEnergy D a)) :=
    Real.sq_sqrt (neutralConstant_pos _).le
  have hsq : (chargedConstant a * ((E : ℝ)+1)^(2*d) * normD v)^2 =
      normD v * (neutralConstant (creationCoeff D a (2*chargeEnergy D a)) *
        ((E : ℝ)+1)^(2*(2*d)) * normD v) := by
    rw [mul_pow, mul_pow, hconst, ← pow_mul, Nat.mul_comm (2*d) 2]
    ring
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (chargedConstant_pos a).le (by positivity)) hnormv)).mp
      (hs.trans_eq hsq.symm)

private def totalChargedConstant (a : Charge D) : ℝ :=
  chargedConstant a + chargedConstant (-a)

private theorem totalChargedConstant_pos (a : Charge D) : 0 < totalChargedConstant a :=
  add_pos (chargedConstant_pos a) (chargedConstant_pos (-a))

private theorem charged_all_modes_grade_le (hD : (gramReal D).PosDef)
    (a : Charge D) (ha : a ≠ 0) (m : ℤ) (E : ℕ) (v : Carrier D)
    (hv : v ∈ grade D (E : ℤ)) :
    normD (((actualField D a)[[m+chargeEnergy D a-1]]) v) ≤
      totalChargedConstant a * (1+|(m : ℝ)|)^(2*(chargeEnergy D a).toNat) *
        ((E : ℝ)+1)^(2*(chargeEnergy D a).toNat) * normD v := by
  let d := (chargeEnergy D a).toNat
  let N := 2*d
  let C := totalChargedConstant a
  have hn : 0 ≤ chargeEnergy D a := chargeEnergy_nonneg D hD a
  have hd : (d : ℤ)=chargeEnergy D a := Int.toNat_of_nonneg hn
  have hpos : 0 < chargeEnergy D a := by
    have hp := (charged_weight hD a ha).1
    omega
  have hC : 0 ≤ C := (totalChargedConstant_pos a).le
  have hCa : chargedConstant a ≤ C := le_add_of_nonneg_right (chargedConstant_pos (-a)).le
  have hCb : chargedConstant (-a) ≤ C := le_add_of_nonneg_left (chargedConstant_pos a).le
  have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
  by_cases hm : 0 ≤ m+chargeEnergy D a-1
  · have hr : (((m+chargeEnergy D a-1).toNat : ℕ) : ℤ)=m+chargeEnergy D a-1 :=
      Int.toNat_of_nonneg hm
    have hh := charged_positive_mode_grade_le hD a (m+chargeEnergy D a-1).toNat E v hv
    rw [hr] at hh
    have hmode : 1 ≤ (1+|(m : ℝ)|)^N :=
      one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])
    have hc : chargedConstant a ≤ C*(1+|(m : ℝ)|)^N :=
      hCa.trans (by nlinarith [mul_nonneg hC (sub_nonneg.mpr hmode)])
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by positivity)) hvn)
  · have hm' : m ≤ -chargeEnergy D a := by omega
    let u := ((actualField D a)[[m+chargeEnergy D a-1]]) v
    let F := ((E : ℤ)-m).toNat
    have hF : (F : ℤ)=(E : ℤ)-m := Int.toNat_of_nonneg (by omega)
    have hu : u ∈ grade D (F : ℤ) := by
      rw [hF]
      exact charged_mode_grade a E m v hv
    have hneg : chargeEnergy D (-a)=chargeEnergy D a := by
      simp [chargeEnergy, bilinear_neg_neg]
    have hj : 0 ≤ -m+chargeEnergy D a-1 := by omega
    have hj' : (((-m+chargeEnergy D a-1).toNat : ℕ) : ℤ)=
        -m+chargeEnergy D a-1 := Int.toNat_of_nonneg hj
    have hb : normD (((actualField D (-a))[[-m+chargeEnergy D a-1]]) u) ≤
        chargedConstant (-a)*((F : ℝ)+1)^N*normD u := by
      simpa only [hj', hneg] using
        charged_positive_mode_grade_le hD (-a) (-m+chargeEnergy D a-1).toNat F u hu
    have hphase : ‖paritySign (chargeEnergy D a)‖=1 := by
      unfold paritySign
      split_ifs <;> simp
    have hdual : normD u ≤ chargedConstant (-a)*((F : ℝ)+1)^N*normD v := by
      by_cases hz : normD u=0
      · rw [hz]
        exact mul_nonneg (mul_nonneg (chargedConstant_pos (-a)).le (by positivity)) hvn
      have hup : 0 < normD u := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      have hs : normD u^2 ≤ normD v *
          normD (((actualField D (-a))[[-m+chargeEnergy D a-1]]) u) := by
        rw [normD_sq hD]
        calc
          _ = (Hm v (paritySign (chargeEnergy D a) •
              (((actualField D (-a))[[-m+chargeEnergy D a-1]]) u))).re :=
            congrArg Complex.re (Hm_charged_circle a m v u)
          _ ≤ normD v * normD (paritySign (chargeEnergy D a) •
              (((actualField D (-a))[[-m+chargeEnergy D a-1]]) u)) :=
            (Complex.re_le_norm _).trans (Hm_cauchy_schwarz hD _ _)
          _ = _ := by rw [normD_smul hD, hphase, one_mul]
      have hc : normD u * normD u ≤
          (chargedConstant (-a)*((F : ℝ)+1)^N*normD v)*normD u := by
        calc
          _ = normD u^2 := (pow_two _).symm
          _ ≤ normD v *
              normD (((actualField D (-a))[[-m+chargeEnergy D a-1]]) u) := hs
          _ ≤ normD v * (chargedConstant (-a)*((F : ℝ)+1)^N*normD u) :=
            mul_le_mul_of_nonneg_left hb hvn
          _ = _ := by ring
      exact (mul_le_mul_iff_left₀ hup).mp hc
    have hFr : (F : ℝ)=(E : ℝ)-(m : ℝ) := by exact_mod_cast hF
    have hmr : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
    have hscale : (F : ℝ)+1 ≤ (1+|(m : ℝ)|)*((E : ℝ)+1) := by
      rw [hFr, abs_of_nonpos hmr]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) E) (neg_nonneg.mpr hmr)]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (F : ℝ)+1) hscale N
    calc
      _ ≤ chargedConstant (-a)*((F : ℝ)+1)^N*normD v := hdual
      _ ≤ C*((1+|(m : ℝ)|)*((E : ℝ)+1))^N*normD v :=
        mul_le_mul_of_nonneg_right (mul_le_mul hCb hpow (by positivity) hC) hvn
      _ = _ := by rw [mul_pow]; ring

private theorem original_charged_energy_le (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (a : Charge D) (ha : a ≠ 0) (m : ℤ) (v : Carrier D) :
    let d := (chargeEnergy D a).toNat
    normD (((actualField D a)[[m+(d : ℤ)-1]]) v) ≤
      totalChargedConstant a * (1+|(m : ℝ)|)^(2*d) *
        normD (((1+sugawaraMode D H 0)^(2*d)) v) := by
  dsimp only
  have hd : ((chargeEnergy D a).toNat : ℤ)=chargeEnergy D a :=
    Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a)
  rw [hd]
  apply energy_bound_of_grades hD H hHG hGH _ (-m)
    (totalChargedConstant a * (1+|(m : ℝ)|)^(2*(chargeEnergy D a).toNat))
    (mul_nonneg (totalChargedConstant_pos a).le (by positivity)) _ _ _ v
  · intro E u hu
    simpa only [sub_eq_add_neg] using charged_mode_grade a E m u hu
  · exact fun E u hu => charged_all_modes_grade_le hD a ha m E u hu

/-- Uniform energy control for every original weighted-homogeneous neutral state. -/
theorem neutral_energy_bound (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (p : Oscillator D) (w : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w) :
    ∃ K : ℝ, 0 < K ∧ ∀ v : Carrier D,
      normD (((Y D (Finsupp.single 0 p))[[(w : ℤ)-1]]) v) ≤
        K * normD (((1+sugawaraMode D H 0)^(2*w)) v) := by
  exact ⟨neutralConstant p, neutralConstant_pos p,
    fun v => original_neutral_energy_le hD H hHG hGH p w hp v⟩

/-- The literal charged lattice field has one polynomial energy bound in all
integer circle modes and on all original finite mixed states. -/
theorem charged_energy_bound (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (a : Charge D) (ha : a ≠ 0) :
    let d := (chargeEnergy D a).toNat
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier D),
      normD (((actualField D a)[[m+(d : ℤ)-1]]) v) ≤
        C * (1+|(m : ℝ)|)^(2*d) *
          normD (((1+sugawaraMode D H 0)^(2*d)) v) := by
  exact ⟨totalChargedConstant a, totalChargedConstant_pos a,
    fun m v => original_charged_energy_le hD H hHG hGH a ha m v⟩

#check @neutral_energy_bound
#print axioms neutral_energy_bound
#check @charged_energy_bound
#print axioms charged_energy_bound

#check @original_charged_energy_le
#print axioms original_charged_energy_le

#check @charged_positive_mode_grade_le
#print axioms charged_positive_mode_grade_le

#check @charged_weight
#check @Hm_charged_circle
#check @actual_phase
#check @neutralState_original
#check @charged_normal_quadratic
#check @charged_annihilating_square_le

#print axioms charged_weight
#print axioms Hm_charged_circle
#print axioms actual_phase
#print axioms neutralState_original
#print axioms charged_normal_quadratic
#print axioms charged_annihilating_square_le

#check (∀ (D : LatticeData) (_hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_hHG : H * gramComplex D = 1) (_hGH : gramComplex D * H = 1)
    (a : Charge D) (_ha : a ≠ 0),
    let d : ℕ := (chargeEnergy D a).toNat
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier D),
      normD (D := D) (((actualField D a)[[m + (d : ℤ) - 1]]) v) ≤
        C * ((1 : ℝ) + |(m : ℝ)|) ^ (2*d) *
          normD (D := D) (((1 + sugawaraMode D H 0) ^ (2*d)) v) : Prop)

end D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
