/- GID: D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/OriginalChargedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integer charged fields and the canonical matter Hermitian norm. -/

import D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
import D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-! Canonical integer-frequency prerequisites for the original charged fields. -/

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
open private Hm_finsum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

variable {D : LatticeData}

private theorem full_frame_matrix (hD : (gramReal D).PosDef) :
    (RC D hD)ᵀ * gramComplex D * RC D hD = 1 := by
  have hG : (SC D hD)ᵀ * SC D hD = gramComplex D := by
    ext i j
    exact SC_gram D hD i j
  rw [← hG]
  calc
    _ = (SC D hD * RC D hD)ᵀ * (SC D hD * RC D hD) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [SC_mul_RC]; simp

private def fullFrame (hD : (gramReal D).PosDef) : RealOrthonormalFrame D D.rank where
  B j i := RC D hD i j
  real_B j i := by simp [RC]
  orthonormal j k := by
    have h := congrFun (congrFun (full_frame_matrix hD) j) k
    change (∑ i, (∑ l, RC D hD l j * (D.G l i : ℂ)) * RC D hD i k) = _ at h
    rw [Matrix.one_apply] at h
    change (∑ i, ∑ l, RC D hD i j * (D.G i l : ℂ) * RC D hD l k) = _
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul] at h
    exact h

private def fullOscillatorEquiv (hD : (gramReal D).PosDef) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv
    (fun _ => RC D hD) (fun _ => SC D hD)
    (fun _ => RC_mul_SC D hD) (fun _ => SC_mul_RC D hD)

private theorem fullFrame_phi (hD : (gramReal D).PosDef) :
    phi (fullFrame hD) = (fullOscillatorEquiv hD).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro x
  rfl

private theorem fullFrame_surjective (hD : (gramReal D).PosDef) :
    Function.Surjective (transverseEmbed (fullFrame hD)) := by
  intro v
  let x : Charge D →₀ Oscillator D :=
    v.mapRange (fullOscillatorEquiv hD).symm (map_zero _)
  refine ⟨x, ?_⟩
  apply Finsupp.ext
  intro a
  change phi (fullFrame hD) ((fullOscillatorEquiv hD).symm (v a)) = v a
  rw [fullFrame_phi]
  exact (fullOscillatorEquiv hD).apply_symm_apply (v a)

private theorem original_positive (hD : (gramReal D).PosDef) {v : Carrier D}
    (hv : v ≠ 0) : (Hm (D := D) v v).im = 0 ∧ 0 < (Hm (D := D) v v).re := by
  obtain ⟨x, rfl⟩ := fullFrame_surjective hD v
  apply Hm_self_strict_positive
  intro hx
  apply hv
  simp [hx, transverseEmbed]

private theorem original_nonnegative (hD : (gramReal D).PosDef) (v : Carrier D) :
    0 ≤ (Hm (D := D) v v).re := by
  by_cases hv : v = 0
  · subst v
    simp [Hm]
  · exact (original_positive hD hv).2.le

private theorem original_ground_pairing (hD : (gramReal D).PosDef) (a b : Charge D) :
    Hm (D := D) (Finsupp.single a 1) (Finsupp.single b 1) =
      if a = b then 1 else 0 := by
  have he := source_delta_delta_eq_factorial (fullFrame hD) a b
    (1 : Polynomial D.rank) 1
  have hi : FactorialFockMetric.inner (1 : Polynomial D.rank) 1 = 1 := by
    have h := FactorialFockMetric.inner_monomial_left
      (0 : Occupation D.rank) (1 : ℂ) (1 : Polynomial D.rank)
    simpa [FactorialFockMetric.weight] using h
  simpa only [delta, map_one, hi] using he

private def normD (v : Carrier D) : ℝ := Real.sqrt (Hm (D := D) v v).re

private theorem normD_sq (hD : (gramReal D).PosDef) (v : Carrier D) :
    normD v ^ 2 = (Hm (D := D) v v).re :=
  Real.sq_sqrt (original_nonnegative hD v)

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

#check @original_positive
#check @original_ground_pairing
#check @charged_weight
#check @Hm_charged_circle
#check @actual_phase
#check @neutralState_original
#check @charged_normal_quadratic
#check @charged_annihilating_square_le

#print axioms fullFrame_surjective
#print axioms original_positive
#print axioms original_ground_pairing
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
