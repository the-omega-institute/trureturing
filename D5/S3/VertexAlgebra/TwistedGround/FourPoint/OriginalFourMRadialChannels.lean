/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialChannels
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialChannels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original A and B Laurent readouts of the physical signed projector. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialScalars
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

/-! The real overlap identifies the marked projector with the original
sector Laurent functions in both native coordinates. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMRadialChannels

open Complex MvPolynomial Metric
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeDiscriminantTheta (gramReal)
open LatticeHalfFockChargedCoefficients (omega)
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMActualChart (Chart Puncture parameter relativeB scaleRoot chosen_roots)
open OriginalFourMChargeCoset (oscillatorLower fourierSign quadraticSign slitChannelA slitChannelB)
open OriginalFourMChargeNormal (sewnChargeTerm compact_charge_normal)
open OriginalFourMSewnProjection (radial_chart_signed_projector)
open OriginalFourMRadialScalars (radial_factors radial_chart_factors)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSlitMean (slitMeanEntry slitCovarianceEntry)
open OriginalFourMSectorContinuation (slitChargeTerm slitChargeSector slitChargeTerm_eq_native)
open OriginalGaussianSourceRestriction (compactExternal fourSupport)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain)
open private ball_subset_slitDomain from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open D5.S3.Analytic.OriginalSlitNome (slitNome slitNome_norm_lt_one rank24Determinant)
open D5.S3.Analytic.OriginalHalfBinomialNome (Q0)
open FourPoint.FourPointChannelCoefficients (loweringWeight loweringCutoff)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open private wordScale incomingScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private chartTau from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private relative relative_same_slot from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private chartDetectorCutoff creationWord modesBounded punctureWords
  firstLeft secondLeft firstRight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMProjectionModes (physical_chart_coefficient_overlap_normalized)
open private slitDiagonal slitLaurent slitLowered from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms
open private slitMatrix slitLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private inverseScaleProduct neg_one_zpow_even_shift from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialScalars
open private scale_ne from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

private theorem radial_term_hasSum (D : LatticeData) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (a : ModTwoCharge D) (d g r s : Exponent D)
    {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} => sewnChargeTerm D d g r s q.val w)
      (slitChargeSector D a d g r s (w ^ 2)) := by
  classical
  let t := w ^ 2
  let e := compactExternal D (fourSupport D d g r s)
  have ht : t ∈ slitDomain := ball_subset_slitDomain (by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg w) hw (by decide))
  obtain ⟨b, hb, hbound⟩ := (compact_charge_normal D hD d g r s
    {t} isCompact_singleton rank24Determinant slitNome
    differentiableOn_singleton differentiableOn_singleton
    (by intro u hu; simpa only [Set.mem_singleton_iff.mp hu] using slitNome_norm_lt_one ht)
    (slitMatrix D e) (slitLinear D e)
    (fun _ _ => differentiableOn_singleton) (fun _ => differentiableOn_singleton)).1
  have hsum : Summable (fun q : Charge D => slitChargeTerm D d g r s q t) :=
    hb.of_norm_bounded fun q => hbound q t (Set.mem_singleton t)
  have hvalue : (∑' q : {q : Charge D // reduceCharge D q = a}, slitChargeTerm D d g r s q.val t) =
      slitChargeSector D a d g r s t := by
    refine (tsum_subtype {q : Charge D | reduceCharge D q = a}
      (fun q => slitChargeTerm D d g r s q t)).trans ?_
    unfold slitChargeSector
    apply tsum_congr
    intro q
    by_cases hq : reduceCharge D q = a <;> simp [Set.indicator, hq]
  rw [← hvalue]
  exact (hsum.subtype (fun q => reduceCharge D q = a)).hasSum.congr_fun fun q =>
    (slitChargeTerm_eq_native D hD h24 d g r s q.val hw).symm

private theorem radial_projector_hasSum (D : LatticeData) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (a : ModTwoCharge D) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      projectOccupations D H K 0 (s - H - K + 1) P Q R S
        (fun d g r s => sewnChargeTerm D d g r s q.val w))
      (slitDiagonal D H K s P Q R S a (w ^ 2)) := by
  classical
  unfold projectOccupations slitDiagonal
  dsimp only
  refine hasSum_sum fun i _ => hasSum_sum fun j _ => HasSum.mul_left _ ?_
  refine hasSum_sum fun d _ => hasSum_sum fun g _ => hasSum_sum fun r _ =>
    hasSum_sum fun s _ => HasSum.mul_left _ ?_
  exact radial_term_hasSum D hD h24 a _ _ _ _ hw

private def wordDegree (D : LatticeData) (xs : List (Index D)) : ℤ :=
  (xs.map fun i => (omega D i : ℤ)).sum

private theorem creationWord_degree (D : LatticeData) (xs : List (Index D)) :
    (creationWord D xs).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (wordDegree D xs) := by
  induction xs with
  | nil => exact isWeightedHomogeneous_one ℂ _
  | cons i xs ih => exact (isWeightedHomogeneous_X ℂ _ i).mul ih

private theorem creationWord_ne_zero (D : LatticeData) (xs : List (Index D)) :
    creationWord D xs ≠ 0 := by
  induction xs with
  | nil => exact one_ne_zero
  | cons i xs ih => exact mul_ne_zero (X_ne_zero i) ih

private theorem wordDegree_eq (D : LatticeData) (xs : List (Index D)) (d : ℤ)
    (h : (creationWord D xs).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d) :
    wordDegree D xs = d := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun h => creationWord_ne_zero D xs (support_eq_empty.mp h))
  exact ((creationWord_degree D xs) (mem_support_iff.mp he)).symm.trans
    (h (mem_support_iff.mp he))

private theorem wordScale_eq (D : LatticeData) (c : Chart) (s : Puncture)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (xs : List (Index D)) :
    wordScale D c x s xs = (scaleRoot c x s)⁻¹ ^ wordDegree D xs := by
  induction xs with
  | nil => simp [wordScale, wordDegree]
  | cons i xs ih =>
    change incomingScale c x s i.2 * wordScale D c x s xs =
      (scaleRoot c x s)⁻¹ ^ ((omega D i : ℤ) + wordDegree D xs)
    have hroot : scaleRoot c x s ≠ 0 := fun h => scale_ne hx hx₁ c s (by
      rw [← (chosen_roots hx hx₁ c s).1, h, zero_pow (by decide)])
    rw [zpow_add₀ (inv_ne_zero hroot), ih, incomingScale, ← zpow_natCast]
    rfl

private theorem puncture_relative_product (D : LatticeData) {X : Type*}
    (c : Chart) (s : Puncture) (slot : X → Puncture) (mode : X → Index D)
    (marks : List X) (hslot : ∀ i ∈ marks, slot i = s) :
    (marks.map fun i => relative c (slot i)).prod =
      relative c s ^ wordDegree D (marks.map mode) := by
  have hn : relative c s ≠ 0 := fun h => by
    simpa [h] using relative_same_slot c s
  induction marks with
  | nil => simp [wordDegree]
  | cons i marks ih =>
    have hi := hslot i (by simp)
    have hrest : ∀ j ∈ marks, slot j = s := fun j hj => hslot j (List.mem_cons_of_mem _ hj)
    change relative c (slot i) * (marks.map fun i => relative c (slot i)).prod =
      relative c s ^ ((omega D (mode i) : ℤ) + wordDegree D (marks.map mode))
    rw [hi, ih hrest, zpow_add₀ hn, zpow_natCast, omega, pow_add, pow_mul,
      relative_same_slot, one_pow, pow_one, one_mul]

private theorem loweringWeight_eq (s : ℤ) (j : ℕ) :
    loweringWeight s j = (-1 : ℂ) ^ (s + 2) * ((-1 : ℂ) ^ j / (j.factorial : ℂ)) := by
  rw [loweringWeight, show s + (j : ℤ) + 2 = (s + 2) + j by ring,
    zpow_add₀ (by norm_num), zpow_natCast, div_eq_mul_inv, mul_assoc]

private abbrev Word (D : LatticeData) {X : Type*} (mode : X → Index D)
    (marks : Puncture → List X) (s : Puncture) : Oscillator D :=
  creationWord D ((marks s).map mode)

private abbrev MarkedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    {X : Type*} [Fintype X] [DecidableEq X] (slot : X → Puncture) (mode : X → Index D)
    (marks : Puncture → List X) (upperA : Bool) (x : ℝ) (c : Chart) (a : ModTwoCharge D) : ℂ :=
  let l := (punctureWords marks).flatMap Prod.snd
  spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
    (l.map Sum.inr ++ l.map Sum.inl) (fun z =>
      physicalProduct D hu slot (fun i => (mode i).1) upperA x c a
        (z ∘ Sum.inl) (z ∘ Sum.inr)) 0

/-- The two literal marked Taylor coefficients are the corresponding
original Laurent-sector values times their exact chart factors. -/
theorem radial_AB_laurent_readouts (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (a : ModTwoCharge D)
    (M H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1)
    (upperA : Bool) {wA wB : ℂ} (hwA : ‖wA‖ < 1) (hwB : ‖wB‖ < 1)
    (hsA : wA ^ 2 = parameter .A (x : ℂ)) (hsB : wB ^ 2 = parameter .B (x : ℂ))
    (hNomeA : exp ((Real.pi : ℂ) * I * chartTau upperA .A x) = Q0 (wA ^ 2))
    (hNomeB : exp ((Real.pi : ℂ) * I * chartTau upperA .B x) = Q0 (wB ^ 2))
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ M)
    (marks : Puncture → List X) (hslot : ∀ s i, i ∈ marks s → slot i = s)
    (hl : ((punctureWords marks).flatMap Prod.snd).Nodup)
    (hbox : ∀ c s, modesBounded D M (inverseLoweredWord D c x s ((marks s).map mode)))
    (hsupp : ∀ s j, modesBounded D M ((oscillatorLower D ^ j) (Word D mode marks s)))
    (hP : (Word D mode marks .P).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (Word D mode marks .Q).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (Word D mode marks .R).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (Word D mode marks .S).IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    let P := Word D mode marks .P
    let Q := Word D mode marks .Q
    let R := Word D mode marks .R
    let S := Word D mode marks .S
    let s := m + n + r
    let common := -I * ((x : ℂ) ^ (-s - 5) * (1 - (x : ℂ)) ^ (3 : ℕ))
    MarkedCoefficient D hu slot mode marks upperA x .A a =
      common * slitLaurent D H K s P Q R S a (parameter .A (x : ℂ)) ∧
    MarkedCoefficient D hu slot mode marks upperA x .B a =
      (x : ℂ) ^ (6 : ℕ) * common * (x : ℂ) ^ (s + 2) *
        slitChannelB D H K L m n r P Q R S a (parameter .B (x : ℂ)) := by
  classical
  dsimp only
  let P := Word D mode marks .P
  let Q := Word D mode marks .Q
  let R := Word D mode marks .R
  let S := Word D mode marks .S
  let s := m + n + r
  let N : ℤ := H + K + L - s - 2
  let l := (punctureWords marks).flatMap Prod.snd
  let scale := fun c p => wordScale D c x p ((marks p).map mode)
  let scalar := fun c => (l.map fun i => relative c (slot i)).prod *
    (1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
      (scale c .P * scale c .Q * scale c .R * scale c .S)
  have hx₀ : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx₀.ne'
  have h1C : (1 - (x : ℂ)) ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one.mpr hx₁.ne).symm
  have hprod (c : Chart) :
      (l.map fun i => relative c (slot i)).prod =
        relative c .P ^ (2 * (H : ℤ) - 3) * relative c .Q ^ (2 * (K : ℤ) - 3) *
        relative c .R ^ (2 * (L : ℤ) - 3) * relative c .S ^ (2 * N - 3) := by
    simp only [l, punctureWords, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.prod_append, puncture_relative_product D c _ slot mode _ (hslot _),
      wordDegree_eq D _ _ hP, wordDegree_eq D _ _ hQ, wordDegree_eq D _ _ hR,
      wordDegree_eq D _ (2 * N - 3) hS]
    ring
  have hprodA : (l.map fun i => relative .A (slot i)).prod = 1 := by rw [hprod]; simp [relative]
  have hprodB : (l.map fun i => relative .B (slot i)).prod = -1 := by
    rw [hprod]
    simp only [relative, relativeB, one_zpow, one_mul]
    rw [show 2 * N - 3 = 1 + 2 * (N - 2) by ring, neg_one_zpow_even_shift, zpow_one]
  have hscale (c : Chart) :
      scale c .P * scale c .Q * scale c .R * scale c .S =
        inverseScaleProduct c x H K L N := by
    simp only [scale, wordScale_eq D c _ hx₀ hx₁, wordDegree_eq D _ _ hP, wordDegree_eq D _ _ hQ,
      wordDegree_eq D _ _ hR, wordDegree_eq D _ (2 * N - 3) hS, inverseScaleProduct]
  have hsign (J : ℕ) : (-1 : ℂ) ^ (J : ℤ) * (-1 : ℂ) ^ (J : ℤ) = 1 := by
    rw [← zpow_add₀ (by norm_num), show (J : ℤ) + J = 0 + 2 * J by ring,
      neg_one_zpow_even_shift, zpow_zero]
  have hA := radial_chart_signed_projector D hu hD h24 a M H K L 0 m n r hx₀ hx₁
    upperA .A (Or.inl rfl) hwA hsA hNomeA slot mode bound marks hslot hl (hbox .A) hsupp hP hQ hR hS
  have hB := radial_chart_signed_projector D hu hD h24 a M K L H 0 m n r hx₀ hx₁
    upperA .B (Or.inr rfl) hwB hsB hNomeB slot mode bound marks hslot hl (hbox .B) hsupp hQ hR hP
    (by convert hS using 2 <;> ring)
  have hA' := (radial_projector_hasSum D hD h24 a H K s P Q R S hwA).mul_left (scalar .A)
  have hB' := (hasSum_sum (s := Finset.range (loweringCutoff H K L m n r)) fun j _ =>
    (radial_projector_hasSum D hD h24 a K L (s + j) Q R P ((oscillatorLower D ^ j) S) hwB).mul_left
      ((-1 : ℂ) ^ j / (j.factorial : ℂ))).mul_left (scalar .B)
  have hAeq : (-1 : ℂ) ^ (K : ℤ) * MarkedCoefficient D hu slot mode marks upperA x .A a =
      scalar .A * slitDiagonal D H K s P Q R S a (wA ^ 2) := by
    apply hA.unique
    simpa [hsA, scalar, chartDetectorCutoff, l, scale, P, Q, R, S, s, Finset.range_one,
      firstLeft, secondLeft, firstRight] using hA'
  have hBeq : (-1 : ℂ) ^ (L : ℤ) * MarkedCoefficient D hu slot mode marks upperA x .B a =
      scalar .B * ∑ j ∈ Finset.range (loweringCutoff H K L m n r),
        ((-1 : ℂ) ^ j / (j.factorial : ℂ)) *
          slitDiagonal D K L (s + j) Q R P ((oscillatorLower D ^ j) S) a (wB ^ 2) := by
    apply hB.unique
    have hcut : chartDetectorCutoff .B K L H m n r = loweringCutoff H K L m n r := by
      unfold chartDetectorCutoff loweringCutoff
      exact congrArg Int.toNat (by omega)
    have hsc : scale .B .Q * scale .B .R * scale .B .P * scale .B .S =
        scale .B .P * scale .B .Q * scale .B .R * scale .B .S := by ring
    refine hB'.congr_fun ?_
    intro q
    dsimp only [firstLeft, secondLeft, firstRight, scalar, Nat.cast_zero, zero_add]
    rw [hcut, hsc, hsB]
    simp only [Nat.cast_zero, zero_add, l, s, P, Q, R, S]
  have hr := radial_chart_factors hx₀ hx₁ H K L N
  have hf := radial_factors H K L s N rfl hxC h1C
  have hargA : -parameter .A (x : ℂ) = (1 - (x : ℂ)) / (x : ℂ) := by
    simp only [parameter]
    field_simp
    ring
  have hBpow : (x : ℂ) ^ (3 - (K : ℤ) - L) =
      (x : ℂ) ^ (6 : ℕ) * (x : ℂ) ^ (-(K : ℤ) - L - 3) := by
    rw [← zpow_natCast, ← zpow_add₀ hxC]
    congr 1
    ring
  constructor
  · have h := congrArg ((-1 : ℂ) ^ (K : ℤ) * ·) hAeq
    rw [← mul_assoc, hsign, one_mul, hsA] at h
    rw [h, ← mul_assoc, show (-1 : ℂ) ^ (K : ℤ) * scalar .A =
      (-1 : ℂ) ^ (K : ℤ) * (1 - parameter .A (x : ℂ)) ^ (3 : ℕ) *
        inverseScaleProduct .A x H K L N by simp only [scalar, hprodA, hscale, one_mul]; ring,
      hr.1, hf.1, slitLaurent, hargA, show -((H : ℤ) + K) = -(H : ℤ) - K by ring]
    ring
  · have h := congrArg ((-1 : ℂ) ^ (L : ℤ) * ·) hBeq
    rw [← mul_assoc, hsign, one_mul, hsB] at h
    rw [h, ← mul_assoc, show (-1 : ℂ) ^ (L : ℤ) * scalar .B =
      (-1 : ℂ) ^ (L : ℤ) * (-(1 - parameter .B (x : ℂ)) ^ (3 : ℕ)) *
        inverseScaleProduct .B x H K L N by simp only [scalar, hprodB, hscale]; ring,
      hr.2, hBpow]
    have he : (-1 : ℂ) ^ (H + N) * ((x : ℂ) ^ (6 : ℕ) *
        (x : ℂ) ^ (-(K : ℤ) - L - 3)) * (1 - (x : ℂ)) ^ (3 : ℕ) =
        (x : ℂ) ^ (6 : ℕ) * ((-1 : ℂ) ^ (H + N) *
          (x : ℂ) ^ (-(K : ℤ) - L - 3) * (1 - (x : ℂ)) ^ (3 : ℕ)) := by ring
    rw [he, hf.2.1]
    simp only [slitChannelB, slitLowered, slitLaurent, loweringWeight_eq, ← mul_assoc, Finset.mul_sum,
      parameter, show -((K : ℤ) + L) = -(K : ℤ) - L by ring]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The physical rank-24 Fourier equality gives the original A/B crossing
with the signed monomial in the common x coordinate. -/
theorem radial_AB_slit_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (b : ModTwoCharge D)
    (M H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1)
    (upperA : Bool) {wA wB : ℂ} (hwA : ‖wA‖ < 1) (hwB : ‖wB‖ < 1)
    (hsA : wA ^ 2 = parameter .A (x : ℂ)) (hsB : wB ^ 2 = parameter .B (x : ℂ))
    (hNomeA : exp ((Real.pi : ℂ) * I * chartTau upperA .A x) = Q0 (wA ^ 2))
    (hNomeB : exp ((Real.pi : ℂ) * I * chartTau upperA .B x) = Q0 (wB ^ 2))
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ M)
    (marks : Puncture → List X) (hslot : ∀ s i, i ∈ marks s → slot i = s)
    (hl : ((punctureWords marks).flatMap Prod.snd).Nodup)
    (hbox : ∀ c s, modesBounded D M (inverseLoweredWord D c x s ((marks s).map mode)))
    (hsupp : ∀ s j, modesBounded D M ((oscillatorLower D ^ j) (Word D mode marks s)))
    (hP : (Word D mode marks .P).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (Word D mode marks .Q).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (Word D mode marks .R).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (Word D mode marks .S).IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    slitChannelA D H K (m + n + r) (Word D mode marks .P) (Word D mode marks .Q)
        (Word D mode marks .R) (Word D mode marks .S) b (parameter .A (x : ℂ)) =
      (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n + r + 2) *
        slitChannelB D H K L m n r (Word D mode marks .P) (Word D mode marks .Q)
          (Word D mode marks .R) (Word D mode marks .S) b (parameter .B (x : ℂ)) := by
  classical
  let P := Word D mode marks .P
  let Q := Word D mode marks .Q
  let R := Word D mode marks .R
  let S := Word D mode marks .S
  let s := m + n + r
  let common := -I * ((x : ℂ) ^ (-s - 5) * (1 - (x : ℂ)) ^ (3 : ℕ))
  let jet := MarkedCoefficient D hu slot mode marks upperA x
  let l := (punctureWords marks).flatMap Prod.snd
  have hx₀ : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx₀.ne'
  have h1C : (1 - (x : ℂ)) ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one.mpr hx₁.ne).symm
  have hcommon : common ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero (zpow_ne_zero _ hxC) (pow_ne_zero _ h1C))
  have readout (a : ModTwoCharge D) :=
    radial_AB_laurent_readouts D hu hD h24 a M H K L m n r hx hx₁
      upperA hwA hwB hsA hsB hNomeA hNomeB slot mode bound marks hslot hl hbox hsupp hP hQ hR hS
  have hcross := (physical_chart_coefficient_overlap_normalized D hu hD h24
    slot (fun i => (mode i).1) upperA hx₀ hx₁ hsA hwA
    (Sum.elim (fun i => (mode i).2) (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl) b).2
  change (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * jet .B b =
    ∑ a, fourierSign D b a * quadraticSign D a * jet .A a at hcross
  have hA (a : ModTwoCharge D) : jet .A a =
      common * slitLaurent D H K s P Q R S a (parameter .A (x : ℂ)) := (readout a).1
  have hB : jet .B b = (x : ℂ) ^ (6 : ℕ) * common * (x : ℂ) ^ (s + 2) *
      slitChannelB D H K L m n r P Q R S b (parameter .B (x : ℂ)) := (readout b).2
  rw [hB] at hcross
  simp_rw [hA] at hcross
  apply mul_left_cancel₀ hcommon
  calc
    _ = ∑ a, fourierSign D b a * quadraticSign D a *
          (common * slitLaurent D H K s P Q R S a (parameter .A (x : ℂ))) := by
      rw [slitChannelA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hF : fourierSign D b a = fourierSign D a b := by
        unfold fourierSign
        rw [← mod_two_cocycle_symmetrization D b a,
          ← mod_two_cocycle_symmetrization D a b, add_comm]
      rw [hF]
      ring
    _ = _ := hcross.symm.trans (by field_simp [hxC]; ring)

#print axioms radial_AB_laurent_readouts
#print axioms radial_AB_slit_crossing


open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (exists_lowering_cutoff)

private def modeCeiling (D : LatticeData) (P : Oscillator D) : ℕ :=
  P.vars.sup Prod.snd

private theorem modesBounded_of_ceiling (D : LatticeData) (P : Oscillator D) {M : ℕ}
    (hM : modeCeiling D P ≤ M) : modesBounded D M P := by
  intro d hd i hi
  exact (Finset.le_sup ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)).trans hM

private theorem exists_nat_bound {X : Type*} [Fintype X] (f : X → ℕ) :
    ∃ M, ∀ i, f i ≤ M :=
  ⟨Finset.univ.sup f, fun i => Finset.le_sup (f := f) (Finset.mem_univ i)⟩

/-- Word representatives require no supplied mode box or choice of marks.
The charge-sector crossing holds for every signed triple of original modes. -/
theorem radial_AB_word_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (b : ModTwoCharge D)
    (H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1)
    (upperA : Bool) {wA wB : ℂ} (hwA : ‖wA‖ < 1) (hwB : ‖wB‖ < 1)
    (hsA : wA ^ 2 = parameter .A (x : ℂ)) (hsB : wB ^ 2 = parameter .B (x : ℂ))
    (hNomeA : exp ((Real.pi : ℂ) * I * chartTau upperA .A x) = Q0 (wA ^ 2))
    (hNomeB : exp ((Real.pi : ℂ) * I * chartTau upperA .B x) = Q0 (wB ^ 2))
    (words : Puncture → List (Index D))
    (hP : (creationWord D (words .P)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D (words .Q)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D (words .R)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D (words .S)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    let P := creationWord D (words .P)
    let Q := creationWord D (words .Q)
    let R := creationWord D (words .R)
    let S := creationWord D (words .S)
    slitChannelA D H K (m + n + r) P Q R S b (parameter .A (x : ℂ)) =
      (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n + r + 2) *
        slitChannelB D H K L m n r P Q R S b (parameter .B (x : ℂ)) := by
  classical
  let : Fintype Puncture :=
    ⟨{.P, .Q, .R, .S}, by intro p; cases p <;> simp⟩
  let : Fintype Chart :=
    ⟨{.A, .B, .D}, by intro c; cases c <;> simp⟩
  let X := Σ p : Puncture, Fin (words p).length
  let slot : X → Puncture := Sigma.fst
  let mode : X → Index D := fun i => (words i.1).get i.2
  let marks (p : Puncture) : List X := List.ofFn fun i => ⟨p, i⟩
  have hwords (p : Puncture) : (marks p).map mode = words p := by
    simp only [marks, List.map_ofFn]
    exact List.ofFn_get (words p)
  have hslot (p : Puncture) (i : X) (hi : i ∈ marks p) : slot i = p := by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hi
    rfl
  have hnodup (p : Puncture) : (marks p).Nodup :=
    List.nodup_ofFn_ofInjective fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hdisj (p q : Puncture) (hpq : p ≠ q) : List.Disjoint (marks p) (marks q) := by
    intro i hi hj
    exact hpq ((hslot p i hi).symm.trans (hslot q i hj))
  have hl : ((punctureWords marks).flatMap Prod.snd).Nodup := by
    change (marks .P ++ (marks .Q ++ (marks .R ++ (marks .S ++ [])))).Nodup
    simp only [List.append_nil, List.nodup_append', hnodup, List.disjoint_append_right,
      true_and]
    repeat' first | exact hdisj _ _ (by intro h; cases h) | constructor
  choose cutoff hcut using fun p => exists_lowering_cutoff D hu (creationWord D (words p))
  obtain ⟨maxMode, hmode⟩ := exists_nat_bound fun i : X => (mode i).2
  obtain ⟨maxInverse, hinverse⟩ := exists_nat_bound fun z : Chart × Puncture =>
    modeCeiling D (inverseLoweredWord D z.1 x z.2 (words z.2))
  let lowerCeiling (p : Puncture) (j : ℕ) :=
    modeCeiling D ((oscillatorLower D ^ j) (creationWord D (words p)))
  obtain ⟨maxLower, hlower⟩ := exists_nat_bound fun p : Puncture =>
    (Finset.range (cutoff p)).sup (lowerCeiling p)
  let M := maxMode + maxInverse + maxLower
  have hM₁ : maxMode ≤ M := by dsimp only [M]; omega
  have hM₂ : maxInverse ≤ M := by dsimp only [M]; omega
  have hM₃ : maxLower ≤ M := by dsimp only [M]; omega
  have bound (i : X) : (mode i).2 ≤ M := (hmode i).trans hM₁
  have hbox (c : Chart) (p : Puncture) :
      modesBounded D M (inverseLoweredWord D c x p ((marks p).map mode)) := by
    rw [hwords]
    exact modesBounded_of_ceiling D _ ((hinverse (c, p)).trans hM₂)
  have hsupp (p : Puncture) (j : ℕ) :
      modesBounded D M ((oscillatorLower D ^ j) (Word D mode marks p)) := by
    change modesBounded D M ((oscillatorLower D ^ j) (creationWord D ((marks p).map mode)))
    rw [hwords]
    by_cases hj : j < cutoff p
    · have h := Finset.le_sup (f := lowerCeiling p) (Finset.mem_range.mpr hj)
      exact modesBounded_of_ceiling D _ (h.trans ((hlower p).trans hM₃))
    · rw [hcut p j (Nat.le_of_not_gt hj)]
      simp [modesBounded]
  have hmark (p : Puncture) : Word D mode marks p = creationWord D (words p) :=
    congrArg (creationWord D) (hwords p)
  simpa only [hmark] using radial_AB_slit_crossing D hu hD h24 b M H K L m n r hx hx₁
    upperA hwA hwB hsA hsB hNomeA hNomeB slot mode bound marks hslot hl hbox hsupp
    (by rwa [hmark]) (by rwa [hmark]) (by rwa [hmark]) (by rwa [hmark])

#print axioms radial_AB_word_crossing

open OriginalFourMEnergyCoefficient (leftExponent selector)
open FactorialFockMetric (weight)
open private monomialWord monomialWord_prod from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

private def occupationForm (D : LatticeData)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    (Exponent D →₀ ℂ) →ₗ[ℂ] (Exponent D →₀ ℂ) →ₗ[ℂ]
      (Exponent D →₀ ℂ) →ₗ[ℂ] (Exponent D →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun d =>
    Finsupp.linearCombination ℂ fun g =>
      Finsupp.linearCombination ℂ fun r =>
        Finsupp.linearCombination ℂ fun s => F d g r s

private abbrev FourForm (D : LatticeData) :=
  MultilinearMap ℂ (fun _ : Fin 4 => Oscillator D) ℂ

private def occupationMultilinear (D : LatticeData)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) : FourForm D where
  toFun v := occupationForm D F (v 0).coeff (v 1).coeff (v 2).coeff (v 3).coeff
  map_update_add' v i p q := by
    fin_cases i <;>
      simp [Function.update, Fin.ext_iff, AddMonoidAlgebra.coeff_add,
        map_add, LinearMap.add_apply]
  map_update_smul' v i t p := by
    fin_cases i <;>
      simp [Function.update, Fin.ext_iff, AddMonoidAlgebra.coeff_smul,
        map_smul, LinearMap.smul_apply]

private theorem occupationMultilinear_apply (D : LatticeData)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ)
    (v : Fin 4 → Oscillator D) :
    occupationMultilinear D F v =
      ∑ d ∈ (v 0).support, ∑ g ∈ (v 1).support, ∑ r ∈ (v 2).support,
        ∑ s ∈ (v 3).support,
          ((v 0).coeff d * (v 1).coeff g * (v 2).coeff r * (v 3).coeff s) * F d g r s := by
  classical
  change occupationForm D F (v 0).coeff (v 1).coeff (v 2).coeff (v 3).coeff = _
  simp only [occupationForm, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, MvPolynomial.support]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

private def projectForm (D : LatticeData) (H K : ℕ) (t : ℤ)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) : FourForm D :=
  ∑ i ∈ Finset.range (K - 1), ∑ j ∈ Finset.range (H - 1),
    ((-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) /
      ((i.factorial : ℂ) * (j.factorial : ℂ))) •
      (occupationMultilinear D (fun d g r s =>
        (weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ) *
          selector D 0 (leftExponent H K 0 i j) 0 d g * selector D 0 (-2 * t - 2) 0 r s *
          F d g r s)).compLinearMap
        ![oscillatorLower D ^ j, oscillatorLower D ^ i, LinearMap.id, LinearMap.id]

set_option maxHeartbeats 1000000 in
-- Expanding the four nested sums requires elaborating the four lowering maps.
private theorem projectForm_apply (D : LatticeData) (H K : ℕ) (t : ℤ)
    (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ)
    (v : Fin 4 → Oscillator D) :
    projectForm D H K t F v = projectOccupations D H K 0 t (v 0) (v 1) (v 2) (v 3) F := by
  classical
  simp only [projectForm, sum_apply, smul_apply,
    MultilinearMap.compLinearMap_apply, occupationMultilinear_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.id_apply, projectOccupations, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

private def laurentForm (D : LatticeData) (H K : ℕ) (s : ℤ) (a : ModTwoCharge D)
    (t : ℂ) : FourForm D :=
  (-t) ^ (-((H : ℤ) + K)) •
    projectForm D H K (s - H - K + 1) (fun d g r u => slitChargeSector D a d g r u t)

private theorem laurentForm_apply (D : LatticeData) (H K : ℕ) (s : ℤ) (a : ModTwoCharge D)
    (t : ℂ) (v : Fin 4 → Oscillator D) :
    laurentForm D H K s a t v = slitLaurent D H K s (v 0) (v 1) (v 2) (v 3) a t := by
  simp only [laurentForm, smul_apply, smul_eq_mul, projectForm_apply,
    slitLaurent, slitDiagonal]

private def slitAForm (D : LatticeData) (H K : ℕ) (s : ℤ) (b : ModTwoCharge D)
    (t : ℂ) : FourForm D :=
  ∑ a, (quadraticSign D a * fourierSign D a b) • laurentForm D H K s a t

private def permB : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def slitBForm (D : LatticeData) (H K L : ℕ) (m n r : ℤ) (b : ModTwoCharge D)
    (t : ℂ) : FourForm D :=
  ∑ ell ∈ Finset.range (loweringCutoff H K L m n r), loweringWeight (m + n + r) ell •
    ((laurentForm D K L (m + n + r + ell) b t).compLinearMap
      ![LinearMap.id, LinearMap.id, LinearMap.id, oscillatorLower D ^ ell]).domDomCongr permB

private theorem slitAForm_apply (D : LatticeData) (H K : ℕ) (s : ℤ) (a : ModTwoCharge D)
    (t : ℂ) (v : Fin 4 → Oscillator D) :
    slitAForm D H K s a t v = slitChannelA D H K s (v 0) (v 1) (v 2) (v 3) a t := by
  simp only [slitAForm, slitChannelA, sum_apply, smul_apply,
    smul_eq_mul, laurentForm_apply, mul_assoc]

private theorem slitBForm_apply (D : LatticeData) (H K L : ℕ) (m n r : ℤ) (a : ModTwoCharge D)
    (t : ℂ) (v : Fin 4 → Oscillator D) :
    slitBForm D H K L m n r a t v = slitChannelB D H K L m n r (v 0) (v 1) (v 2) (v 3) a t := by
  have hp0 : permB 0 = 1 := by decide
  have hp1 : permB 1 = 2 := by decide
  have hp2 : permB 2 = 0 := by decide
  have hp3 : permB 3 = 3 := by decide
  simp only [slitBForm, slitChannelB, slitLowered, sum_apply,
    smul_apply, MultilinearMap.domDomCongr, MultilinearMap.coe_mk,
    MultilinearMap.compLinearMap_apply, smul_eq_mul, laurentForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.id_apply, hp0, hp1, hp2, hp3]

/-- Exact interior A/B crossing for all four homogeneous original oscillators,
including zero inputs and arbitrary signed modes. -/
theorem radial_AB_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (b : ModTwoCharge D)
    (H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1)
    (upperA : Bool) {wA wB : ℂ} (hwA : ‖wA‖ < 1) (hwB : ‖wB‖ < 1)
    (hsA : wA ^ 2 = parameter .A (x : ℂ)) (hsB : wB ^ 2 = parameter .B (x : ℂ))
    (hNomeA : exp ((Real.pi : ℂ) * I * chartTau upperA .A x) = Q0 (wA ^ 2))
    (hNomeB : exp ((Real.pi : ℂ) * I * chartTau upperA .B x) = Q0 (wB ^ 2))
    (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    slitChannelA D H K (m + n + r) P Q R S b (parameter .A (x : ℂ)) =
      (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n + r + 2) *
        slitChannelB D H K L m n r P Q R S b (parameter .B (x : ℂ)) := by
  classical
  let v : Fin 4 → Oscillator D := ![P, Q, R, S]
  let d : Fin 4 → ℤ := ![2 * (H : ℤ) - 3, 2 * (K : ℤ) - 3, 2 * (L : ℤ) - 3,
    2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3]
  have hv (i : Fin 4) : (v i).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (d i) := by
    fin_cases i <;> assumption
  let A := slitAForm D H K (m + n + r) b (parameter .A (x : ℂ))
  let c := (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n + r + 2)
  let B := c • slitBForm D H K L m n r b (parameter .B (x : ℂ))
  suffices A v = B v by
    simpa only [A, B, c, slitAForm_apply, slitBForm_apply, smul_apply, smul_eq_mul,
      v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
      using this
  conv_lhs => rw [show v = (fun i => ∑ e ∈ (v i).support, monomial e ((v i).coeff e)) by
    funext i; exact (v i).as_sum, A.map_sum_finset]
  conv_rhs => rw [show v = (fun i => ∑ e ∈ (v i).support, monomial e ((v i).coeff e)) by
    funext i; exact (v i).as_sum, B.map_sum_finset]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' (i : Fin 4) : e i ∈ (v i).support := (Fintype.mem_piFinset.mp he) i
  have hm (i : Fin 4) :
      (monomial (e i) (1 : ℂ)).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (d i) :=
    isWeightedHomogeneous_monomial _ _ _ (hv i (mem_support_iff.mp (he' i)))
  have hs (i : Fin 4) :
      monomial (e i) ((v i).coeff (e i)) = (v i).coeff (e i) • monomial (e i) (1 : ℂ) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  simp_rw [hs, MultilinearMap.map_smul_univ]
  congr 1
  let words : Puncture → List (Index D)
    | .P => monomialWord (e 0)
    | .Q => monomialWord (e 1)
    | .R => monomialWord (e 2)
    | .S => monomialWord (e 3)
  have hp : creationWord D (words .P) = monomial (e 0) 1 := monomialWord_prod _
  have hq : creationWord D (words .Q) = monomial (e 1) 1 := monomialWord_prod _
  have hr : creationWord D (words .R) = monomial (e 2) 1 := monomialWord_prod _
  have ht : creationWord D (words .S) = monomial (e 3) 1 := monomialWord_prod _
  simpa only [A, B, c, slitAForm_apply, slitBForm_apply, smul_apply, smul_eq_mul,
    hp, hq, hr, ht] using radial_AB_word_crossing D hu hD h24 b H K L m n r hx hx₁
      upperA hwA hwB hsA hsB hNomeA hNomeB words
      (by rw [hp]; exact hm 0) (by rw [hq]; exact hm 1)
      (by rw [hr]; exact hm 2) (by rw [ht]; exact hm 3)

#print axioms radial_AB_crossing

private theorem radial_openings {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1) :
    ∃ wA wB : ℂ, ‖wA‖ < 1 ∧ ‖wB‖ < 1 ∧
      wA ^ 2 = parameter .A (x : ℂ) ∧ wB ^ 2 = parameter .B (x : ℂ) := by
  let y : ℝ := x⁻¹ - 1
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 ≤ y := by
    dsimp [y]
    linarith [(one_lt_inv₀ hx₀).mpr hx₁]
  have hxi : x⁻¹ < 2 := by
    rw [inv_eq_one_div, div_lt_iff₀ hx₀]
    linarith
  have hy₁ : y < 1 := by dsimp [y]; linarith
  have hnA : Real.sqrt y < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hy₁)
  have hnB : Real.sqrt x < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hx₁)
  refine ⟨I * (Real.sqrt y : ℂ), (Real.sqrt x : ℂ), ?_, ?_, ?_, ?_⟩
  · simpa only [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hnA
  · simpa only [norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hnB
  · rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt hy₀, neg_one_mul]
    simp only [y, parameter, ofReal_sub, ofReal_inv, ofReal_one]
    ring
  · rw [← ofReal_pow, Real.sq_sqrt hx₀.le, parameter]

/-- On the entire real overlap the original channels cross with the native
nome identifications as the radial analytic hypotheses. -/
theorem radial_AB_crossing_on_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (b : ModTwoCharge D)
    (H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1)
    (upperA : Bool)
    (hNomeA : exp ((Real.pi : ℂ) * I * chartTau upperA .A x) = Q0 (parameter .A (x : ℂ)))
    (hNomeB : exp ((Real.pi : ℂ) * I * chartTau upperA .B x) = Q0 (parameter .B (x : ℂ)))
    (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    slitChannelA D H K (m + n + r) P Q R S b (parameter .A (x : ℂ)) =
      (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m + n + r + 2) *
        slitChannelB D H K L m n r P Q R S b (parameter .B (x : ℂ)) := by
  obtain ⟨wA, wB, hwA, hwB, hsA, hsB⟩ := radial_openings hx hx₁
  exact radial_AB_crossing D hu hD h24 b H K L m n r hx hx₁ upperA hwA hwB hsA hsB
    (by simpa only [hsA] using hNomeA) (by simpa only [hsB] using hNomeB) P Q R S hP hQ hR hS

#print axioms radial_AB_crossing_on_overlap

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMRadialChannels
