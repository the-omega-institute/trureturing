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


end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMRadialChannels
