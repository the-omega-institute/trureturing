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
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.LatticeActualConformalState
import Mathlib.Data.Nat.Choose.Bounds

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
open private Hm_finsum_right Hm_finset_sum_left Hm_finset_sum_right from
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

open private target target_creation rescale_monomial rescale_coeff frequencyAmplitude
  frequencyAmplitude_real frequencyAmplitude_square from
  D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian

private def fockInner {t : ℕ} (P Q : Polynomial t) : ℂ :=
  FactorialFockMetric.inner (rescale t P) (rescale t Q)

private def fockQ {t : ℕ} (P : Polynomial t) : ℝ := (fockInner P P).re

private theorem fockInner_coeff {t : ℕ} (P Q : Polynomial t) :
    fockInner P Q = ∑ e ∈ P.support,
      (exactWeight e : ℂ) * conj (P.coeff e) * Q.coeff e := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [fockInner, FactorialFockMetric.inner, map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro e he
  change FactorialFockMetric.inner (rescale t (MvPolynomial.monomial e (P.coeff e)))
    (rescale t Q) = _
  rw [rescale_monomial, FactorialFockMetric.inner_monomial_left,
    rescale_coeff, map_mul, frequencyAmplitude_real]
  calc
    _ = (FactorialFockMetric.weight e : ℂ) *
        (frequencyAmplitude e * frequencyAmplitude e) * conj (P.coeff e) * Q.coeff e := by ring
    _ = _ := by rw [frequencyAmplitude_square]; simp only [exactWeight, Nat.cast_mul]

private theorem fockQ_coeff {t : ℕ} (P : Polynomial t) :
    fockQ P = ∑ e ∈ P.support, (exactWeight e : ℝ) * Complex.normSq (P.coeff e) := by
  rw [fockQ, fockInner, rescaled_inner_coeff_sum]
  simp

private def frequencyNumber {t : ℕ} (r : ℕ) (P : Polynomial t) : Polynomial t :=
  ∑ i : Fin t, ((r : ℂ) + 1) • (MvPolynomial.X (i,r) * MvPolynomial.pderiv (i,r) P)

private theorem frequencyNumber_coeff {t : ℕ} (r : ℕ) (P : Polynomial t)
    (e : Occupation t) :
    (frequencyNumber r P).coeff e =
      ((∑ i : Fin t, e (i,r) * (r+1) : ℕ) : ℂ) * P.coeff e := by
  classical
  have hx (i : Fin t) :
      (MvPolynomial.X (i,r) * MvPolynomial.pderiv (i,r) P).coeff e =
        (e (i,r) : ℂ) * P.coeff e := by
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [MvPolynomial.coeff_smul]
      by_cases h : d = e
      · subst d; simp
      · simp [MvPolynomial.coeff_monomial, h]
    | add P Q hP hQ => simp [mul_add, hP, hQ]
  simp only [frequencyNumber, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, hx,
    smul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem frequency_occupation_le {t : ℕ} (r : ℕ) (e : Occupation t) :
    ∑ i : Fin t, e (i,r) * (r+1) ≤
      Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e := by
  classical
  let s : Finset (Fin t × ℕ) := Finset.univ ×ˢ {r}
  let f : Fin t × ℕ → ℕ := fun x => e x * (x.2+1)
  have hs : (∑ x ∈ s, f x) = ∑ i : Fin t, e (i,r) * (r+1) := by
    simp [s, f]
  have he : (∑ x ∈ e.support ∪ s, f x) =
      Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e := by
    rw [Finsupp.weight_apply]
    change _ = ∑ x ∈ e.support, e x * (x.2+1)
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro x hx hxe
    simp [Finsupp.notMem_support_iff.mp hxe]
  rw [← hs, ← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by
    intro x _ _; exact Nat.zero_le _)

private theorem fock_derivative_sum {t : ℕ} (r : ℕ) (P : Polynomial t) :
    (∑ i : Fin t, fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) =
      ∑ e ∈ P.support, (exactWeight e : ℝ) * Complex.normSq (P.coeff e) *
        (∑ i : Fin t, e (i,r) * (r+1) : ℕ) := by
  classical
  have ha (i : Fin t) :
      fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) =
        (fockInner (MvPolynomial.X (i,r) *
          (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) P).re := by
    have h := target_creation (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) P i r
    change fockInner _ _ = ((r : ℂ)+1) *
      fockInner (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)
        (MvPolynomial.pderiv (i,r) P) at h
    rw [h]
    simp only [fockQ, fockInner, FactorialFockMetric.inner, map_smul,
      inner_smul_left, inner_smul_right]
  simp_rw [ha]
  have he : (∑ i : Fin t, fockInner (MvPolynomial.X (i,r) *
      (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) P) =
      fockInner (frequencyNumber r P) P := by
    simp only [frequencyNumber, fockInner, FactorialFockMetric.inner, map_sum,
      mul_smul_comm, sum_inner]
  rw [← Complex.re_sum, he]
  have hc : conj (fockInner P (frequencyNumber r P)) =
      fockInner (frequencyNumber r P) P := inner_conj_symm _ _
  rw [← hc, Complex.conj_re, fockInner_coeff]
  rw [Complex.re_sum]
  simp only [frequencyNumber_coeff]
  apply Finset.sum_congr rfl
  intro e he
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem fock_derivative_sum_le {t : ℕ} (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    (∑ i : Fin t, fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) ≤
      (F : ℝ) * fockQ P := by
  rw [fock_derivative_sum, fockQ_coeff, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hf : ((∑ i : Fin t, e (i,r) * (r+1) : ℕ) : ℝ) ≤ F := by
    exact_mod_cast (frequency_occupation_le r e).trans (hP e he)
  have hp : 0 ≤ (exactWeight e : ℝ) * Complex.normSq (P.coeff e) :=
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  nlinarith

private def fockEmbedding (t : ℕ) : Polynomial t →ₗ[ℂ] FactorialFockMetric.Hilbert (Fin t × ℕ) :=
  (FactorialFockMetric.embedding (Fin t × ℕ)).comp (rescale t).toLinearMap

private theorem fockQ_norm {t : ℕ} (P : Polynomial t) :
    fockQ P = ‖fockEmbedding t P‖ ^ 2 := by
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (fockEmbedding t P)).symm

private def fockD {t : ℕ} (a : Fin t → ℂ) (r : ℕ) :
    Derivation ℂ (Polynomial t) (Polynomial t) :=
  ∑ i : Fin t, conj (a i) • (((r : ℂ)+1) • MvPolynomial.pderiv (i,r))

private theorem fockD_apply {t : ℕ} (a : Fin t → ℂ) (r : ℕ) (P : Polynomial t) :
    fockD a r P = ∑ i : Fin t, conj (a i) •
      (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) := by
  unfold fockD
  change (Derivation.coeFnAddMonoidHom _) P = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 4000000 in
-- Elaborating the finite Hilbert-space Cauchy--Schwarz application unfolds two linear maps.
private theorem fock_directional_annihilate_le {t : ℕ} (a : Fin t → ℂ)
    (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    fockQ (fockD a r P) ≤ (∑ i, Complex.normSq (a i)) * F * fockQ P := by
  classical
  let V (i : Fin t) := fockEmbedding t (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)
  have hn : ‖fockEmbedding t (fockD a r P)‖ ≤ ∑ i : Fin t, ‖a i‖ * ‖V i‖ := by
    rw [fockD_apply, map_sum]
    simpa only [V, map_smul, norm_smul, Complex.norm_conj] using
      norm_sum_le Finset.univ (fun i : Fin t => conj (a i) • V i)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin t => ‖a i‖) (fun i : Fin t => ‖V i‖)
  have hs : (∑ i : Fin t, ‖V i‖ ^ 2) ≤ (F : ℝ) * fockQ P := by
    simpa only [V, ← fockQ_norm] using fock_derivative_sum_le r F P hP
  rw [fockQ_norm]
  calc
    _ ≤ (∑ i : Fin t, ‖a i‖ * ‖V i‖) ^ 2 := by
      nlinarith [norm_nonneg (fockEmbedding t (fockD a r P)),
        Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (norm_nonneg (a i))
          (norm_nonneg (V i)))]
    _ ≤ (∑ i : Fin t, ‖a i‖ ^ 2) * ∑ i : Fin t, ‖V i‖ ^ 2 := hc
    _ ≤ (∑ i : Fin t, ‖a i‖ ^ 2) * ((F : ℝ) * fockQ P) :=
      mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by simp only [Complex.normSq_eq_norm_sq]; ring

private def fockVariable {t : ℕ} (a : Fin t → ℂ) (r : ℕ) : Polynomial t :=
  ∑ i : Fin t, a i • MvPolynomial.X (i,r)

private theorem fock_directional_pairing {t : ℕ} (a : Fin t → ℂ) (r : ℕ)
    (P Q : Polynomial t) :
    fockInner (fockVariable a r * P) Q = fockInner P (fockD a r Q) := by
  classical
  have hx (i : Fin t) : fockInner (MvPolynomial.X (i,r) * P) Q =
      ((r : ℂ)+1) * fockInner P (MvPolynomial.pderiv (i,r) Q) :=
    target_creation P Q i r
  simp only [fockVariable, Finset.sum_mul, smul_mul_assoc, fockD_apply,
    fockInner, FactorialFockMetric.inner, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  change (∑ i : Fin t, conj (a i) * fockInner (MvPolynomial.X (i,r) * P) Q) =
    ∑ i : Fin t, conj (a i) * (((r : ℂ)+1) * fockInner P (MvPolynomial.pderiv (i,r) Q))
  simp only [hx]

private theorem fockD_variable {t : ℕ} (a : Fin t → ℂ) (r : ℕ) :
    fockD a r (fockVariable a r) =
      (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) •
        (1 : Polynomial t) := by
  classical
  rw [fockD_apply]
  have hd (i : Fin t) : MvPolynomial.pderiv (i,r) (fockVariable a r) =
      a i • (1 : Polynomial t) := by
    simp [fockVariable, MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq,
      eq_comm]
  simp_rw [hd, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem fock_creation_square {t : ℕ} (a : Fin t → ℂ) (r : ℕ) (P : Polynomial t) :
    fockQ (fockVariable a r * P) = fockQ (fockD a r P) +
      ((r : ℝ)+1) * (∑ i : Fin t, Complex.normSq (a i)) * fockQ P := by
  have hadj : fockInner P (fockVariable a r * fockD a r P) =
      fockInner (fockD a r P) (fockD a r P) := by
    have h := congrArg conj (fock_directional_pairing a r (fockD a r P) P)
    simpa only [fockInner, FactorialFockMetric.inner, inner_conj_symm] using h
  unfold fockQ
  rw [fock_directional_pairing, (fockD a r).leibniz, fockD_variable]
  have hm : P •
      (((((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ))) •
        (1 : Polynomial t)) =
      (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) • P := by
    simp [smul_eq_mul]
  rw [hm]
  have he : fockInner P
      (fockVariable a r • fockD a r P +
        (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) • P) =
      fockInner P (fockVariable a r * fockD a r P) +
        (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) * fockInner P P := by
    rw [show fockVariable a r • fockD a r P = fockVariable a r * fockD a r P from
      smul_eq_mul _ _]
    simp only [fockInner, FactorialFockMetric.inner, map_add, map_smul,
      inner_add_right, inner_smul_right]
  rw [he, hadj]
  simp [Complex.mul_re, Complex.mul_im]

private theorem fock_directional_create_le {t : ℕ} (a : Fin t → ℂ)
    (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    fockQ (fockVariable a r * P) ≤
      (∑ i, Complex.normSq (a i)) * ((F : ℝ)+r+1) * fockQ P := by
  rw [fock_creation_square]
  have h := fock_directional_annihilate_le a r F P hP
  nlinarith

private def fullU (hD : (gramReal D).PosDef) : Oscillator D ≃ₐ[ℂ] Oscillator D :=
  (fullOscillatorEquiv hD).symm

private theorem fullU_X (hD : (gramReal D).PosDef) (x : Index D) :
    fullU hD (MvPolynomial.X x) =
      OriginalCurrentMetric.variableImage (fun _ => SC D hD) x :=
  OriginalCurrentMetric.substitution_X (fun _ => SC D hD) x

private theorem fullU_positive (hD : (gramReal D).PosDef) (i : Fin D.rank)
    (b : Charge D) (r : ℕ) (p : Oscillator D) :
    fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b ((r : ℤ)+1) p) =
      fockD (fun j => SC D hD j i) r (fullU hD p) := by
  classical
  let d : Derivation ℂ (Oscillator D) (Oscillator D) :=
    ((r : ℂ)+1) • LatticeActualAnnihilation.annihilationDerivation D i r
  have hd (q : Oscillator D) : fockD (fun j => SC D hD j i) r q =
      ((r : ℂ)+1) • OriginalCurrentMetric.lowering (fun _ => SC D hD) i r q := by
    rw [fockD_apply, OriginalCurrentMetric.lowering_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hr : conj (SC D hD j i) = SC D hD j i := by simp [SC]
    rw [hr, smul_smul, smul_smul]
    congr 1
    ring
  have hx (x : Index D) :
      fullU hD (d (MvPolynomial.X x)) =
        fockD (fun j => SC D hD j i) r (fullU hD (MvPolynomial.X x)) := by
    rcases x with ⟨j,s⟩
    rw [fullU_X, hd, OriginalCurrentMetric.lowering_variableImage, SC_gram]
    simp only [d, Derivation.coe_smul, Pi.smul_apply,
      LatticeActualAnnihilation.annihilation_apply, LatticeActualAnnihilation.annihilate_X]
    split_ifs <;> simp
  have hp : fullU hD (d p) = fockD (fun j => SC D hD j i) r (fullU hD p) := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.derivation_C, map_zero,
        show fullU hD (MvPolynomial.C c) = MvPolynomial.C c from (fullU hD).commutes c,
        MvPolynomial.derivation_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p x hp =>
      rw [d.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      rw [hp, hx, (fockD (fun j => SC D hD j i) r).leibniz]
      simp only [smul_eq_mul]
  rw [neutralPolynomialMode_positive]
  simpa only [d, Derivation.coe_smul, Pi.smul_apply,
    LatticeActualAnnihilation.annihilation_apply, LinearMap.smul_apply] using hp

private theorem fullU_negative (hD : (gramReal D).PosDef) (i : Fin D.rank)
    (b : Charge D) (r : ℕ) (p : Oscillator D) :
    fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b (-(r : ℤ)-1) p) =
      fockVariable (fun j => SC D hD j i) r * fullU hD p := by
  rw [neutralPolynomialMode_negative, LinearMap.mulLeft_apply, map_mul, fullU_X]
  rfl

private theorem fullU_direction_norm (hD : (gramReal D).PosDef) (i : Fin D.rank) :
    (∑ j : Fin D.rank, Complex.normSq (SC D hD j i)) = (D.G i i : ℝ) := by
  have h := congrFun (congrFun (S_transpose_mul D hD) i) i
  change (∑ j : Fin D.rank, S D hD j i * S D hD j i) = (D.G i i : ℝ) at h
  simpa [SC, Complex.normSq_apply, pow_two] using h

private theorem Hm_single_coordinates (hD : (gramReal D).PosDef)
    (a b : Charge D) (p q : Oscillator D) :
    Hm (D := D) (Finsupp.single a p) (Finsupp.single b q) =
      if a = b then fockInner (fullU hD p) (fullU hD q) else 0 := by
  have hs (p : Oscillator D) : phi (fullFrame hD) (fullU hD p) = p := by
    rw [fullFrame_phi]
    exact (fullOscillatorEquiv hD).apply_symm_apply p
  have h := source_delta_delta_eq_factorial (fullFrame hD) a b (fullU hD p) (fullU hD q)
  simpa only [delta, hs, fockInner] using h

open private homogeneous_substitution from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

private theorem fullU_homogeneous (hD : (gramReal D).PosDef) (p : Oscillator D) (n : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p n) :
    MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) (fullU hD p) n := by
  apply homogeneous_substitution (fun x : Index D => x.2+1) (fun x : Index D => x.2+1)
    (OriginalCurrentMetric.variableImage (fun _ => SC D hD)) _ hp
  intro x
  unfold OriginalCurrentMetric.variableImage
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ (fun x : Index D => x.2+1)
    (x.2+1)).smul_mem _ (MvPolynomial.isWeightedHomogeneous_X ℂ _ (i,x.2))

private theorem fullU_grade_support (hD : (gramReal D).PosDef) (E : ℕ)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (b : Charge D)
    (e : Occupation D.rank) (he : e ∈ (fullU hD (v b)).support) :
    Finsupp.weight (fun x : Index D => x.2+1) e ≤ E := by
  have hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1)
      (v b) ((E : ℤ)-chargeEnergy D b).toNat := by
    intro f hf
    have hg : energy D (b,f) = E := by
      by_contra hn
      exact hf ((mem_grade_iff D (E : ℤ) v).mp hv (b,f) hn)
    dsimp [energy, oscillatorEnergy] at hg
    omega
  have hu := fullU_homogeneous hD (v b) _ hp
  have hw := hu (MvPolynomial.mem_support_iff.mp he)
  have hq := chargeEnergy_nonneg D hD b
  omega

private theorem original_positive_current_sector_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ))
    (b : Charge D) :
    (Hm (D := D)
      (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) (Finsupp.single b (v b)))
      (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) (Finsupp.single b (v b)))).re ≤
      (D.G i i : ℝ) * E * (Hm (D := D) (Finsupp.single b (v b)) (Finsupp.single b (v b))).re := by
  simp only [neutralMode_single, Hm_single_coordinates hD, ite_true]
  change fockQ (fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode
    D i b ((r : ℤ)+1) (v b))) ≤ (D.G i i : ℝ) * E * fockQ (fullU hD (v b))
  rw [fullU_positive]
  have h := fock_directional_annihilate_le (fun j => SC D hD j i) r E (fullU hD (v b))
    (fullU_grade_support hD E v hv b)
  rw [fullU_direction_norm] at h
  exact h

private theorem original_negative_current_sector_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ))
    (b : Charge D) :
    (Hm (D := D)
      (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) (Finsupp.single b (v b)))
      (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) (Finsupp.single b (v b)))).re ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) *
        (Hm (D := D) (Finsupp.single b (v b)) (Finsupp.single b (v b))).re := by
  simp only [neutralMode_single, Hm_single_coordinates hD, ite_true]
  change fockQ (fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode
    D i b (-(r : ℤ)-1) (v b))) ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) * fockQ (fullU hD (v b))
  rw [fullU_negative]
  have h := fock_directional_create_le (fun j => SC D hD j i) r E (fullU hD (v b))
    (fullU_grade_support hD E v hv b)
  rw [fullU_direction_norm] at h
  exact h

private theorem normD_sector_sum (hD : (gramReal D).PosDef) (s : Finset (Charge D))
    (f : Charge D → Oscillator D) :
    normD (∑ b ∈ s, Finsupp.single b (f b)) ^ 2 =
      ∑ b ∈ s, normD (Finsupp.single b (f b)) ^ 2 := by
  classical
  rw [normD_sq hD, Hm_finset_sum_left, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Hm_finset_sum_right, normD_sq hD]
  congr 1
  apply Finset.sum_eq_single b
  · intro c hc hcb
    rw [Hm_single_coordinates hD, if_neg (Ne.symm hcb)]
  · exact fun h => (h hb).elim

private theorem current_norm_sector_sum (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (m : ℤ) (v : Carrier D) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ^ 2 =
      ∑ b ∈ v.support,
        normD (LatticeFiniteNegativeGeneration.neutralMode D i m (Finsupp.single b (v b))) ^ 2 := by
  classical
  have he : (∑ b ∈ v.support, Finsupp.single b (v b)) = v := v.sum_single
  have hmode : LatticeFiniteNegativeGeneration.neutralMode D i m v =
      ∑ b ∈ v.support, Finsupp.single b
        (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b m (v b)) := by
    conv_lhs => rw [← he, map_sum]
    simp only [neutralMode_single]
  rw [hmode, normD_sector_sum hD]
  simp only [neutralMode_single]

private theorem original_positive_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) v) ^ 2 ≤
      (D.G i i : ℝ) * E * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  simpa only [normD_sq hD] using original_positive_current_sector_le hD i r E v hv b

private theorem original_negative_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) v) ^ 2 ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  simpa only [normD_sq hD] using original_negative_current_sector_le hD i r E v hv b

open private Matrix.PosSemidef.preInnerProductSpace from Mathlib.Analysis.Matrix.PosDef

private theorem original_gram_charge_square_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (b : Charge D) :
    (bilinear D (unitCharge D i) b : ℝ) ^ 2 ≤
      2 * (D.G i i : ℝ) * (chargeEnergy D b : ℝ) := by
  classical
  let c : PreInnerProductSpace.Core ℝ (Fin D.rank → ℝ) :=
    hD.posSemidef.preInnerProductSpace
  let u : Fin D.rank → ℝ := fun j => (unitCharge D i j : ℝ)
  let q : Fin D.rank → ℝ := fun j => (b j : ℝ)
  have hb (a b : Charge D) :
      ((gramReal D) *ᵥ (fun j => (b j : ℝ))) ⬝ᵥ (fun j => (a j : ℝ)) =
        (bilinear D a b : ℝ) := by
    simp only [gramReal, Matrix.mulVec, dotProduct, Matrix.map_apply,
      bilinear, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc := @InnerProductSpace.Core.inner_mul_inner_self_le ℝ (Fin D.rank → ℝ) _ _ _ c u q
  change ‖((gramReal D) *ᵥ q) ⬝ᵥ u‖ * ‖((gramReal D) *ᵥ u) ⬝ᵥ q‖ ≤
    (((gramReal D) *ᵥ u) ⬝ᵥ u) * (((gramReal D) *ᵥ q) ⬝ᵥ q) at hc
  dsimp only [u, q] at hc
  rw [hb, hb, hb, hb, LatticeFiniteNegativeGeneration.bilinear_symmetric D b (unitCharge D i)] at hc
  have hu : bilinear D (unitCharge D i) (unitCharge D i) = D.G i i := by
    simp [bilinear, unitCharge]
  have he : (bilinear D b b : ℝ) = 2 * (chargeEnergy D b : ℝ) := by
    exact_mod_cast (two_chargeEnergy D b).symm
  rw [hu, he, Real.norm_eq_abs, ← sq, sq_abs] at hc
  nlinarith only [hc]

private theorem chargeEnergy_le_grade (E : ℕ) (v : Carrier D)
    (hv : v ∈ grade D (E : ℤ)) (b : Charge D) (hb : v b ≠ 0) :
    chargeEnergy D b ≤ E := by
  obtain ⟨e, he⟩ := MvPolynomial.exists_coeff_ne_zero hb
  have hg : energy D (b,e) = E := by
    by_contra hn
    exact he ((mem_grade_iff D (E : ℤ) v).mp hv (b,e) hn)
  dsimp [energy] at hg
  omega

private theorem normD_real_smul_sq (hD : (gramReal D).PosDef) (c : ℝ) (v : Carrier D) :
    normD ((c : ℂ) • v) ^ 2 = c ^ 2 * normD v ^ 2 := by
  rw [normD_sq hD, normD_sq hD, Hm_smul_left, Hm_smul_right]
  simp [Complex.mul_re, Complex.mul_im, pow_two, mul_assoc]

private theorem original_zero_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i 0 v) ^ 2 ≤
      (2 * (D.G i i : ℝ) * E) * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hz : LatticeFiniteNegativeGeneration.neutralMode D i 0 (Finsupp.single b (v b)) =
      (((bilinear D (unitCharge D i) b : ℝ) : ℂ)) • Finsupp.single b (v b) := by
    rw [neutralMode_single]
    simp [LatticeFiniteNegativeGeneration.neutralPolynomialMode, Finsupp.smul_single]
  rw [hz, normD_real_smul_sq hD]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc := original_gram_charge_square_le hD i b
  have he : (chargeEnergy D b : ℝ) ≤ E := by
    exact_mod_cast chargeEnergy_le_grade E v hv b (Finsupp.mem_support_iff.mp hb)
  have hg : 0 ≤ (D.G i i : ℝ) := hD.posSemidef.diag_nonneg
  exact hc.trans (mul_le_mul_of_nonneg_left he (by positivity))

private theorem original_current_energy_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (m : ℤ) (E F M : ℕ) (hEF : (E : ℤ)-m=F)
    (hE : E ≤ M) (hF : F ≤ M) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ≤
      Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v := by
  have hg : 0 ≤ (D.G i i : ℝ) := hD.posSemidef.diag_nonneg
  have hEM : (E : ℝ) ≤ M := by exact_mod_cast hE
  have hFM : (F : ℝ) ≤ M := by exact_mod_cast hF
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hs : normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ^ 2 ≤
      (3 * (D.G i i : ℝ) * ((M : ℝ)+1)^2) * normD v ^ 2 := by
    cases m with
    | ofNat k =>
      cases k with
      | zero =>
        have h := original_zero_current_le hD i E v hv
        apply h.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hh : 2*(E : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
        nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
      | succ r =>
        have h := original_positive_current_le hD i r E v hv
        rw [show Int.ofNat (Nat.succ r) = (r : ℤ)+1 from rfl]
        apply h.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hh : (E : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
        nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
    | negSucc r =>
      have h := original_negative_current_le hD i r E v hv
      rw [show Int.negSucc r = -(r : ℤ)-1 by omega]
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have he : (E : ℝ)+r+1 = F := by exact_mod_cast (show E+r+1=F by omega)
      rw [he]
      have hh : (F : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
      nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
  have hr : (Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v)^2 =
      (3 * (D.G i i : ℝ) * ((M : ℝ)+1)^2) * normD v ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hx : 0 ≤ normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) :=
    Real.sqrt_nonneg _
  have hy : 0 ≤ Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ hx hy).mp (hs.trans_eq hr.symm)

private def originalCore (hD : (gramReal D).PosDef) :
    InnerProductSpace.Core ℂ (Carrier D) where
  inner := Hm
  conj_inner_symm x y := (Hm_hermitian x y).symm
  re_inner_nonneg := original_nonnegative hD
  add_left := Hm_add_left
  smul_left x y c := Hm_smul_left c x y
  definite x hx := by
    by_contra hn
    have hp := (original_positive hD hn).2
    rw [hx] at hp
    exact (lt_irrefl 0) hp

private theorem normD_add_le (hD : (gramReal D).PosDef) (u v : Carrier D) :
    normD (u+v) ≤ normD u + normD v := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  exact norm_add_le u v

private theorem normD_smul (hD : (gramReal D).PosDef) (c : ℂ) (v : Carrier D) :
    normD (c • v) = ‖c‖ * normD v := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  letI := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := Carrier D)
  exact norm_smul c v

private theorem normD_sum_le (hD : (gramReal D).PosDef) {ι : Type*}
    (s : Finset ι) (f : ι → Carrier D) :
    normD (∑ i ∈ s, f i) ≤ ∑ i ∈ s, normD (f i) := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  exact norm_sum_le s f

private def wordWeight (ω : List (Index D)) : ℕ :=
  (ω.map (fun x => x.2+1)).sum

open private word_off_energy from D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
open private word_charge chargeSpace from D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
open private wordMap wordCoeff from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

private theorem word_mode_grade (ω : List (Index D)) (E n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    ((wordField D 0 ω)[[n]]) v ∈ grade D (E + wordWeight ω - n - 1) := by
  classical
  rw [grade_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨β,d⟩, he, rfl⟩ := hx
    rw [carrierBasis_apply]
    obtain ⟨p,hp⟩ := word_charge D 0 β ω n (MvPolynomial.monomial d 1)
    have hsingle : ((wordField D 0 ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1)) = Finsupp.single β p := by
      simpa using hp.symm
    rw [mem_grade_iff]
    intro a ha
    by_cases hb : β = a.1
    · have hc := word_off_energy D 0 β ω n a.2 d
      change energy D (β,d) = E at he
      have hw : (ω.map (fun x => (x.2+1 : ℤ))).sum = (wordWeight ω : ℤ) := by
        simp [wordWeight, Nat.cast_list_sum, List.map_map, Function.comp_def]
      have hh : (CanonicalOccupationSewing.level D a.2 : ℤ) ≠
          (CanonicalOccupationSewing.level D d : ℤ) +
            (ω.map (fun x => (x.2+1 : ℤ))).sum - n - 1 - bilinear D 0 β := by
        simp only [bilinear, Pi.zero_apply, Int.cast_zero, zero_mul,
          Finset.sum_const_zero, sub_zero, hw]
        simp only [energy, hb] at he ha
        dsimp [CanonicalOccupationSewing.level]
        omega
      have hz := hc hh
      change ((((wordField D 0 ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1))) (0+β)).coeff a.2 = 0 at hz
      simpa [hb] using hz
    · rw [hsingle]
      simp [Finsupp.single_apply, hb]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (grade D _).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (grade D _).smul_mem c ih

private theorem negative_grade_eq_zero (hD : (gramReal D).PosDef) (E : ℤ)
    (hE : E < 0) (v : Carrier D) (hv : v ∈ grade D E) : v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  change (v a.1).coeff a.2 = 0
  apply (mem_grade_iff D E v).mp hv a
  have hn := chargeEnergy_nonneg D hD a.1
  dsimp [energy]
  omega

open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField

private theorem derivative_zero_strip (i : Fin D.rank) (r : ℕ) (m : ℤ)
    (hm : 0 ≤ m) (hr : m < r) :
    ((FieldNormalProduct.dividedDerivative r
      (LatticeFiniteNegativeGeneration.neutralField D i))[[m]]) = 0 := by
  rw [derivative_modes D (i,r)]
  obtain ⟨q,hq⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m-1+(r : ℤ) by omega)
  rw [hq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show q < r by omega)]
  simp

private theorem current_mode_grade (i : Fin D.rank) (E m : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    LatticeFiniteNegativeGeneration.neutralMode D i m v ∈ grade D (E-m) := by
  have hs : LatticeActualConformalState.currentState D i ∈ grade D 1 := by
    rw [grade_eq_span]
    apply Submodule.subset_span
    refine ⟨(0,Finsupp.single (i,0) 1), ?_, ?_⟩
    · simp [energy, oscillatorEnergy, Finsupp.weight_single]
    · simp [carrierBasis_apply, LatticeActualConformalState.currentState,
        MvPolynomial.X]
  have hg := LatticeCoefficientEnergy.actual_mode_grade D 1 E m
    (LatticeActualConformalState.currentState D i) v hs hv
  rw [LatticeActualConformalState.current_state_field,
    LatticeSugawaraCurrents.neutralField_ncoeff] at hg
  convert hg using 1 <;> congr 1 <;> omega

private def wordLeft (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[-(q : ℤ)-1]])
    (((wordField D 0 ω)[[n+q]]) v)

private def wordRight (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((wordField D 0 ω)[[n-q-1]])
    (((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[q]]) v)

private theorem wordLeft_vanish (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : F < q+x.2+1) : wordLeft x ω n v q = 0 := by
  have hg := word_mode_grade ω E (n+q) v hv
  have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by
    simp [wordWeight]
  have hz := negative_grade_eq_zero hD _ (by rw [hw] at hEF; push_cast at hEF; omega)
    _ hg
  simp [wordLeft, hz]

private theorem wordRight_strip (x : Index D) (ω : List (Index D))
    (n : ℤ) (v : Carrier D) (q : ℕ) (hq : q < x.2) :
    wordRight x ω n v q = 0 := by
  have hz := derivative_zero_strip (D := D) x.1 x.2 q (by omega) (by omega)
  simp [wordRight, hz]

private theorem wordRight_vanish (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E : ℕ) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : E+x.2 < q) : wordRight x ω n v q = 0 := by
  have hg := current_mode_grade x.1 E ((q : ℤ)-x.2) v hv
  have hz := negative_grade_eq_zero hD _ (by omega) _ hg
  dsimp [wordRight]
  rw [derivative_modes D x, LinearMap.smul_apply, hz, smul_zero, map_zero]

/-- Exact finite recursion of the literal normal product, at a general mode.
The derivative strip remains in the second finite range with zero summands. -/
private theorem word_cons_finite (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    ((wordField D 0 (x::ω))[[n]]) v =
      (∑ q ∈ Finset.range (F+1), wordLeft x ω n v q) +
      ∑ q ∈ Finset.range (E+x.2+1), wordRight x ω n v q := by
  classical
  rw [wordField, (FieldNormalProduct.normalMinusOne _ _).2]
  congr 1
  · change (∑ᶠ q, wordLeft x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordLeft_vanish hD x ω E F n hEF v hv q (by
      have hn' : F+1 ≤ q := by simpa using hn
      omega))
  · change (∑ᶠ q, wordRight x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordRight_vanish hD x ω E n v hv q (by
      have hn' : E+x.2+1 ≤ q := by simpa using hn
      omega))

private def derivativeConstant (r : ℕ) : ℝ :=
  ((r : ℝ)+1)^r / (r.factorial : ℝ)

private theorem derivativeConstant_nonneg (r : ℕ) : 0 ≤ derivativeConstant r := by
  unfold derivativeConstant
  positivity

private theorem choose_energy_le (r M t : ℕ) (ht : t ≤ M+r) :
    (t.choose r : ℝ) ≤ derivativeConstant r * ((M : ℝ)+1)^r := by
  have ht' : (t : ℝ) ≤ ((r : ℝ)+1)*((M : ℝ)+1) := by
    have hh : (t : ℝ) ≤ (M : ℝ)+r := by exact_mod_cast ht
    nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) r]
  calc
    _ ≤ (t : ℝ)^r / (r.factorial : ℝ) := Nat.choose_le_pow_div r t
    _ ≤ (((r : ℝ)+1)*((M : ℝ)+1))^r / (r.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ht' r) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; unfold derivativeConstant; ring

open private signed_derivative_choose from
  D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

private theorem derivative_negative_coeff_le (r M q : ℕ) (hq : q+r ≤ M+r) :
    ‖((Ring.choose (-(-(q : ℤ)-1)-1+r) r : ℤ) : ℂ)‖ ≤
      derivativeConstant r * ((M : ℝ)+1)^r := by
  rw [show -(-(q : ℤ)-1)-1+r = ((q+r : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simpa only [Int.cast_natCast, Complex.norm_natCast] using choose_energy_le r M (q+r) hq

private theorem derivative_positive_coeff_le (r M q : ℕ) (hq : q ≤ M+r) :
    ‖((Ring.choose (-(q : ℤ)-1+r) r : ℤ) : ℂ)‖ ≤
      derivativeConstant r * ((M : ℝ)+1)^r := by
  rw [signed_derivative_choose]
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast] using choose_energy_le r M q hq

private def wordOrder (ω : List (Index D)) : ℕ := wordWeight ω + ω.length

private def wordConstant : List (Index D) → ℝ
  | [] => 1
  | x::ω => ((x.2 : ℝ)+2) * derivativeConstant x.2 *
      Real.sqrt (3*(D.G x.1 x.1 : ℝ)) * wordConstant ω

private theorem wordConstant_nonneg (ω : List (Index D)) :
    0 ≤ wordConstant ω := by
  induction ω with
  | nil => norm_num [wordConstant]
  | cons x ω ih =>
    dsimp [wordConstant]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (derivativeConstant_nonneg _)) (Real.sqrt_nonneg _)) ih

/-- The actual nested neutral word is uniformly bounded between any two
nonnegative grades; no charge, support-size or oscillator-degree factor occurs. -/
private theorem original_word_energy_le (hD : (gramReal D).PosDef)
    (ω : List (Index D)) : ∀ (E F M : ℕ) (n : ℤ),
    (E : ℤ)+wordWeight ω-n-1=F → E ≤ M → F ≤ M →
    ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
      normD (((wordField D 0 ω)[[n]]) v) ≤
        wordConstant ω * ((M : ℝ)+1)^(wordOrder ω) * normD v := by
  induction ω with
  | nil =>
    intro E F M n hEF hE hF v hv
    rw [wordField, actual_zero, identity_modes]
    split_ifs with hn
    · simp [wordConstant, wordOrder, wordWeight]
    · simp [wordConstant, wordOrder, wordWeight, normD, Real.sqrt_nonneg]
  | cons x ω ih =>
    intro E F M n hEF hE hF v hv
    classical
    let b : ℝ := (M : ℝ)+1
    let A := derivativeConstant x.2
    let L := Real.sqrt (3*(D.G x.1 x.1 : ℝ))
    let K := wordConstant ω
    let P := wordOrder ω
    let T := A*L*K*b^(x.2+1+P)*normD v
    have hA : 0 ≤ A := derivativeConstant_nonneg _
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hK : 0 ≤ K := wordConstant_nonneg _
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by simp [wordWeight]
    have hp : wordOrder (x::ω) = x.2+2+P := by
      dsimp [wordOrder, P]
      rw [hw]
      omega
    have hleft (q : ℕ) : normD (wordLeft x ω n v q) ≤ T := by
      by_cases hq : F < q+x.2+1
      · rw [wordLeft_vanish hD x ω E F n hEF v hv q hq]
        simpa [normD] using hT
      have hq' : q+x.2+1 ≤ F := by omega
      let G := F-(q+x.2+1)
      have hG : G ≤ M := by dsimp [G]; omega
      have htail : (E : ℤ)+wordWeight ω-(n+q)-1=G := by
        rw [hw] at hEF
        dsimp [G]
        push_cast at hEF
        omega
      have hg : ((wordField D 0 ω)[[n+q]]) v ∈ grade D (G : ℤ) := by
        rw [← htail]
        exact word_mode_grade ω E (n+q) v hv
      have ht := ih E G M (n+q) htail hE hG v hv
      have hc := original_current_energy_le hD x.1 (-(q : ℤ)-1-x.2) G F M
        (by dsimp [G]; omega) hG hF _ hg
      have ha := derivative_negative_coeff_le x.2 M q (by omega)
      rw [wordLeft, derivative_modes D x, LinearMap.smul_apply, normD_smul hD]
      calc
        _ ≤ (A*b^x.2) * (L*b*normD (((wordField D 0 ω)[[n+q]]) v)) :=
          mul_le_mul ha hc (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (A*b^x.2) * (L*b*(K*b^P*normD v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht (mul_nonneg hL hb)) (by positivity)
        _ = T := by dsimp [T]; rw [pow_add, pow_add, pow_one]; ring
    have hright (q : ℕ) : normD (wordRight x ω n v q) ≤ T := by
      by_cases hs : q < x.2
      · rw [wordRight_strip x ω n v q hs]
        simpa [normD] using hT
      by_cases hq : E+x.2 < q
      · rw [wordRight_vanish hD x ω E n v hv q hq]
        simpa [normD] using hT
      let G := E-(q-x.2)
      have hG : G ≤ M := by dsimp [G]; omega
      have hcurr : (E : ℤ)-((q : ℤ)-x.2)=G := by dsimp [G]; omega
      have hg : LatticeFiniteNegativeGeneration.neutralMode D x.1
          ((q : ℤ)-x.2) v ∈ grade D (G : ℤ) := by
        rw [← hcurr]
        exact current_mode_grade x.1 E _ v hv
      have htail : (G : ℤ)+wordWeight ω-(n-q-1)-1=F := by
        rw [hw] at hEF
        push_cast at hEF
        omega
      have ht := ih G F M (n-q-1) htail hG hF _ hg
      have hc := original_current_energy_le hD x.1 ((q : ℤ)-x.2) E G M
        hcurr hE hG v hv
      have ha := derivative_positive_coeff_le x.2 M q (by omega)
      rw [wordRight, derivative_modes D x, LinearMap.smul_apply, map_smul,
        normD_smul hD]
      calc
        _ ≤ (A*b^x.2) * (K*b^P*
            normD (LatticeFiniteNegativeGeneration.neutralMode D x.1 ((q : ℤ)-x.2) v)) :=
          mul_le_mul ha ht (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (A*b^x.2) * (K*b^P*(L*b*normD v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity)
        _ = T := by dsimp [T]; rw [pow_add, pow_add, pow_one]; ring
    have hsumL : (∑ q ∈ Finset.range (F+1), normD (wordLeft x ω n v q)) ≤
        ((F : ℝ)+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (F+1), T := Finset.sum_le_sum (fun q _ => hleft q)
        _ = _ := by simp
    have hsumR : (∑ q ∈ Finset.range (E+x.2+1), normD (wordRight x ω n v q)) ≤
        ((E : ℝ)+x.2+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (E+x.2+1), T := Finset.sum_le_sum (fun q _ => hright q)
        _ = _ := by simp
    have hcount : ((F : ℝ)+1)+((E : ℝ)+x.2+1) ≤ ((x.2 : ℝ)+2)*b := by
      have he : (E : ℝ) ≤ M := by exact_mod_cast hE
      have hf : (F : ℝ) ≤ M := by exact_mod_cast hF
      dsimp [b]
      nlinarith [Nat.cast_nonneg (α := ℝ) x.2, Nat.cast_nonneg (α := ℝ) M]
    rw [word_cons_finite hD x ω E F n hEF v hv]
    calc
      _ ≤ normD (∑ q ∈ Finset.range (F+1), wordLeft x ω n v q) +
          normD (∑ q ∈ Finset.range (E+x.2+1), wordRight x ω n v q) := normD_add_le hD _ _
      _ ≤ ((F : ℝ)+1)*T + ((E : ℝ)+x.2+1)*T :=
        add_le_add ((normD_sum_le hD _ _).trans hsumL) ((normD_sum_le hD _ _).trans hsumR)
      _ = (((F : ℝ)+1)+((E : ℝ)+x.2+1))*T := by ring
      _ ≤ (((x.2 : ℝ)+2)*b)*T := mul_le_mul_of_nonneg_right hcount hT
      _ = _ := by
        rw [hp]
        change (((x.2 : ℝ)+2)*b)*T =
          (((x.2 : ℝ)+2)*A*L*K)*b^(x.2+2+P)*normD v
        dsimp [T]
        rw [show x.2+2+P = (x.2+1+P)+1 by omega, pow_succ]
        ring

private theorem wordOrder_le (ω : List (Index D)) : wordOrder ω ≤ 2*wordWeight ω := by
  have hh : ω.length ≤ wordWeight ω := by
    induction ω with
    | nil => simp [wordWeight]
    | cons x ω ih => simp only [List.length_cons, wordWeight, List.map_cons,
        List.sum_cons] at *; omega
  unfold wordOrder
  omega

private theorem occurrence_weight (e : Index D →₀ ℕ) :
    wordWeight (occurrences D e) = Finsupp.weight (fun x : Index D => x.2+1) e := by
  exact LatticeHalfFockFiniteCorrection.wordWeight_occurrences D e

private def neutralConstant (p : Oscillator D) : ℝ :=
  1 + ∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e)

private theorem neutralConstant_pos (p : Oscillator D) : 0 < neutralConstant p := by
  have hn : 0 ≤ ∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e) :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (norm_nonneg _) (wordConstant_nonneg _))
  unfold neutralConstant
  linarith

private theorem neutral_polynomial_expansion (p : Oscillator D) (n : ℤ) (v : Carrier D) :
    ((Y D (Finsupp.single 0 p))[[n]]) v =
      ∑ e ∈ p.support, p.coeff e • (((wordField D 0 (occurrences D e))[[n]]) v) := by
  have hp : p = ∑ e ∈ p.support, p.coeff e • MvPolynomial.monomial e 1 := by
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using MvPolynomial.as_sum p
  rw [Y_single]
  conv_lhs => rw [hp]
  simp only [map_sum, map_smul, polynomialField_monomial, Finset.sum_apply,
    LinearMap.sum_apply, Pi.smul_apply, LinearMap.smul_apply]

/-- One constant controls every original mixed state in every nonnegative grade. -/
private theorem original_neutral_grade_le (hD : (gramReal D).PosDef)
    (p : Oscillator D) (w : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w)
    (E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((Y D (Finsupp.single 0 p))[[(w : ℤ)-1]]) v) ≤
      neutralConstant p * ((E : ℝ)+1)^(2*w) * normD v := by
  classical
  let B := ((E : ℝ)+1)^(2*w)*normD v
  have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (e : Index D →₀ ℕ) (he : e ∈ p.support) :
      normD (p.coeff e • (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v)) ≤
        (‖p.coeff e‖ * wordConstant (occurrences D e))*B := by
    have hw : wordWeight (occurrences D e) = w := by
      rw [occurrence_weight]
      exact hp (MvPolynomial.mem_support_iff.mp he)
    have ho : wordOrder (occurrences D e) ≤ 2*w := by
      simpa only [hw] using wordOrder_le (occurrences D e)
    have hpow : ((E : ℝ)+1)^(wordOrder (occurrences D e)) ≤ ((E : ℝ)+1)^(2*w) :=
      pow_le_pow_right₀ (by have hn := Nat.cast_nonneg (α := ℝ) E; linarith) ho
    have hword := original_word_energy_le hD (occurrences D e) E E E ((w : ℤ)-1)
      (by rw [hw]; omega) le_rfl le_rfl v hv
    have hword' : normD (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v) ≤
        wordConstant (occurrences D e)*((E : ℝ)+1)^(2*w)*normD v :=
      hword.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (wordConstant_nonneg _)) hvn)
    rw [normD_smul hD]
    exact (mul_le_mul_of_nonneg_left hword' (norm_nonneg _)).trans_eq (by dsimp [B]; ring)
  rw [neutral_polynomial_expansion]
  calc
    _ ≤ ∑ e ∈ p.support,
        normD (p.coeff e • (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v)) :=
      normD_sum_le hD _ _
    _ ≤ ∑ e ∈ p.support, (‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      Finset.sum_le_sum hterm
    _ = (∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (1+∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by dsimp [neutralConstant, B]; ring

#check @original_neutral_grade_le
#print axioms original_neutral_grade_le

#check @original_word_energy_le
#print axioms original_word_energy_le

#check @word_mode_grade
#print axioms word_mode_grade
#check @derivative_zero_strip
#print axioms derivative_zero_strip
#check @word_cons_finite
#print axioms word_cons_finite

#check @original_gram_charge_square_le
#check @original_zero_current_le
#check @original_current_energy_le
#print axioms original_gram_charge_square_le
#print axioms original_zero_current_le
#print axioms original_current_energy_le

#check @original_positive_current_le
#check @original_negative_current_le
#print axioms original_positive_current_le
#print axioms original_negative_current_le

#check @original_positive_current_sector_le
#check @original_negative_current_sector_le
#print axioms original_positive_current_sector_le
#print axioms original_negative_current_sector_le

#check @fock_directional_annihilate_le
#check @fock_directional_create_le
#print axioms fock_directional_annihilate_le
#print axioms fock_directional_create_le

#check @fock_derivative_sum
#check @fock_derivative_sum_le
#print axioms fock_derivative_sum_le

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
