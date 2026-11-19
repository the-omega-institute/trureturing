/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSignedProjector
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipSignedProjector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact signed Laurent projection at the original D boundary. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipProjection

/-! The signed diagonal selectors act on the actual D Gaussian. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open LatticeGeneratingFieldLocality LatticeHalfFock MvPolynomial
open LatticeHalfFockChargedCoefficients (omega)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMActualChart (Chart Puncture scaleRoot parameter)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open OriginalFourMProjectionModes (project_occupations_on_signed_diagonal)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMPhysicalProduct (physicalProduct)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMSectorContinuation (dLipChargeSector)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (lowering_after_energy_cutoff)
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private boxedOscillator modesBounded loweringSum creationWord inverse_word_active
  inverse_word_inactive punctureWords from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private wordScale incomingScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private lowered_support_weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes
open private dLipReadout dLipChargeTerm dLipChargeTerm_hasSum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipProjection
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

private theorem dLip_signed_diagonal_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N H K E : ℕ) (t dR dS : ℤ) (z : ℝ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dR)
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dS)
    (ht : 2 * (t - (E : ℤ) + 1) = dR - dS)
    (hPb : ∀ j ∈ Finset.range (H - 1), modesBounded D N ((oscillatorLower D ^ j) P))
    (hQb : ∀ i ∈ Finset.range (K - 1), modesBounded D N ((oscillatorLower D ^ i) Q))
    (hRb : modesBounded D N R) (hSb : modesBounded D N S) :
    (-1 : ℂ) ^ (K : ℤ) * dLipReadout D q N z
      (boxedOscillator D N false false (loweringSum D (H - 1) P) *
        boxedOscillator D N false true (loweringSum D (K - 1) Q) *
        boxedOscillator D N true false R * boxedOscillator D N true true S) =
      projectOccupations D H K E t P Q R S (fun d g r s => dLipChargeTerm D q d g r s z) := by
  classical
  rw [project_occupations_on_signed_diagonal D hu H K E t dR dS P Q R S hP hQ hR hS ht]
  congr 1
  simp only [loweringSum, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  rw [dLip_four_charge_projection D q N z _ _ _ _ (hPb j hj) (hQb i hi) hRb hSb]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- The common D lowering cutoff preserves the signed detector shift
at each term of the original Laurent projector. -/
theorem dLip_lowered_detector_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N H K L E C : ℕ) (m n r : ℤ) (z : ℝ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3))
    (hPb : ∀ j ∈ Finset.range (H - 1), modesBounded D N ((oscillatorLower D ^ j) P))
    (hQb : ∀ i ∈ Finset.range (K - 1), modesBounded D N ((oscillatorLower D ^ i) Q))
    (hRb : modesBounded D N R)
    (hSb : ∀ ell ∈ Finset.range C, modesBounded D N ((oscillatorLower D ^ ell) S)) :
    (-1 : ℂ) ^ (K : ℤ) * dLipReadout D q N z
      (boxedOscillator D N false false (loweringSum D (H - 1) P) *
        boxedOscillator D N false true (loweringSum D (K - 1) Q) *
        boxedOscillator D N true false R *
        boxedOscillator D N true true (loweringSum D C S)) =
      ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
        projectOccupations D H K E ((E : ℤ) + m + n + r + ell - H - K + 1)
          P Q R ((oscillatorLower D ^ ell) S) (fun d g r s => dLipChargeTerm D q d g r s z) := by
  classical
  have hsum : boxedOscillator D N true true (loweringSum D C S) =
      ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) •
        boxedOscillator D N true true ((oscillatorLower D ^ ell) S) := by
    simp only [loweringSum, map_sum, map_smul]
  rw [hsum]
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  let T := (oscillatorLower D ^ ell) S
  let d := 2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3 - 2 * (ell : ℤ)
  have hT : T.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d := by
    intro i hi
    exact lowered_support_weight D hu S _ hS ell i (mem_support_iff.mpr hi)
  have h := dLip_signed_diagonal_readout D hu q N H K E
    ((E : ℤ) + m + n + r + ell - H - K + 1) (2 * (L : ℤ) - 3) d z P Q R T
    hP hQ hR hT (by dsimp [d]; ring) hPb hQb hRb (hSb ell hell)
  rw [← h]
  simp only [T, mul_smul_comm, map_smul, smul_eq_mul]
  ring

/-- The four actual D inverse words evaluate to the signed Laurent
projector with the original D order and detector cutoff. -/
theorem dLip_inverse_words_projector (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N H K L : ℕ) (m n r : ℤ) (z : ℝ) (words : Puncture → List (Index D))
    (hP : (creationWord D (words .P)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D (words .R)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hR : (creationWord D (words .Q)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hS : (creationWord D (words .S)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3))
    (hsupp : ∀ s j, modesBounded D N ((oscillatorLower D ^ j) (creationWord D (words s)))) :
    let C := ((H : ℤ) + K + L - m - n - r - 3).toNat
    let P := creationWord D (words .P)
    let Q := creationWord D (words .R)
    let R := creationWord D (words .Q)
    let S := creationWord D (words .S)
    let W := fun s => inverseLoweredWord D .D z s (words s)
    let scale := fun s => wordScale D .D z s (words s)
    (-1 : ℂ) ^ (L : ℤ) * dLipReadout D q N z
      (boxedOscillator D N false false (W .P) *
        boxedOscillator D N false true (W .R) *
        boxedOscillator D N true false (W .Q) * boxedOscillator D N true true (W .S)) =
      (scale .P * scale .R * scale .Q * scale .S) *
        ∑ ell ∈ Finset.range C, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
          projectOccupations D H L 0 (m + n + r + ell - H - L + 1)
            P Q R ((oscillatorLower D ^ ell) S) (fun d g r s => dLipChargeTerm D q d g r s z) := by
  classical
  dsimp only
  have hp (j : ℕ) (hj : H - 1 ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words .P)) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hP
    omega
  have hq (j : ℕ) (hj : L - 1 ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words .R)) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hQ
    omega
  have hs (j : ℕ) (hj : ((H : ℤ) + K + L - m - n - r - 3).toNat ≤ j) :
      (oscillatorLower D ^ j) (creationWord D (words .S)) = 0 := by
    apply lowering_after_energy_cutoff D hu _ _ hS
    omega
  rw [inverse_word_active D hu .D z .P _ _ rfl hp,
    inverse_word_active D hu .D z .R _ _ rfl hq,
    inverse_word_inactive D hu .D z .Q _ rfl,
    inverse_word_active D hu .D z .S _ _ rfl hs]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_eq_mul]
  have hK : modesBounded D N (creationWord D (words .Q)) := by
    simpa only [pow_zero, Module.End.one_apply] using hsupp .Q 0
  have h := dLip_lowered_detector_readout D hu q N H L K 0
    ((H : ℤ) + K + L - m - n - r - 3).toNat m n r z _ _ _ _
    hP hQ hR (by convert hS using 2; ring)
    (fun j _ => hsupp .P j) (fun j _ => hsupp .R j) hK (fun j _ => hsupp .S j)
  simp only [Nat.cast_zero, zero_add] at h
  linear_combination (wordScale D .D z .P (words .P) *
    wordScale D .D z .R (words .R) * wordScale D .D z .Q (words .Q) *
    wordScale D .D z .S (words .S)) * h

private theorem dLip_projector_hasSum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (H K E : ℕ) (j : ℤ) (P Q R S : Oscillator D)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      projectOccupations D H K E j P Q R S (fun d g r s => dLipChargeTerm D q.val d g r s z))
      (projectOccupations D H K E j P Q R S (fun d g r s =>
        dLipChargeSector D true a d g r s (parameter .D (z : ℂ)))) := by
  unfold projectOccupations
  apply hasSum_sum
  intro i _
  apply hasSum_sum
  intro j _
  apply HasSum.mul_left
  apply hasSum_sum
  intro d _
  apply hasSum_sum
  intro g _
  apply hasSum_sum
  intro r _
  apply hasSum_sum
  intro s _
  exact (dLipChargeTerm_hasSum D hD a d g r s hz hz₁).mul_left _

/-- The physical sector jet in D reads out the original signed projectors
against the locally holomorphic D-boundary charge sectors. -/
theorem dLip_chart_signed_projector (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (N H K L : ℕ) (m n r : ℤ) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (marks : Puncture → List X) (hslot : ∀ s j, j ∈ marks s → slot j = s)
    (hl : ((punctureWords marks).flatMap Prod.snd).Nodup)
    (hbox : ∀ s, modesBounded D N (inverseLoweredWord D .D z s ((marks s).map mode)))
    (hsupp : ∀ s j, modesBounded D N
      ((oscillatorLower D ^ j) (creationWord D ((marks s).map mode))))
    (hP : (creationWord D ((marks .P).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D ((marks .R).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hR : (creationWord D ((marks .Q).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hS : (creationWord D ((marks .S).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    let words := fun s => (marks s).map mode
    let P := creationWord D (words .P)
    let Q := creationWord D (words .R)
    let R := creationWord D (words .Q)
    let S := creationWord D (words .S)
    let l := (punctureWords marks).flatMap Prod.snd
    let t := parameter .D (z : ℂ)
    let scale := fun s => wordScale D .D z s (words s)
    let c := (l.map fun i => relative .D (slot i)).prod * (1-t) ^ (3 : ℕ)
    (-1 : ℂ) ^ (L : ℤ) *
      spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
        (l.map Sum.inr ++ l.map Sum.inl) (fun u =>
          physicalProduct D hu slot (fun i => (mode i).1) true z .D a
            (u ∘ Sum.inl) (u ∘ Sum.inr)) 0 =
      c * (scale .P * scale .R * scale .Q * scale .S) *
        ∑ ell ∈ Finset.range ((H : ℤ) + K + L - m - n - r - 3).toNat,
          ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
            projectOccupations D H L 0 (m+n+r+ell-H-L+1)
              P Q R ((oscillatorLower D ^ ell) S)
              (fun d g r s => dLipChargeSector D true a d g r s t) := by
  classical
  dsimp only
  let words := fun s => (marks s).map mode
  let P := creationWord D (words .P)
  let Q := creationWord D (words .R)
  let R := creationWord D (words .Q)
  let S := creationWord D (words .S)
  let W := fun s => inverseLoweredWord D .D z s (words s)
  let l := (punctureWords marks).flatMap Prod.snd
  let t := parameter .D (z : ℂ)
  let scale := fun s => wordScale D .D z s (words s)
  let c := (l.map fun i => relative .D (slot i)).prod * (1-t) ^ (3 : ℕ)
  let factor (d g r s : Index D →₀ ℕ) :=
    ((W .P).coeff d * (W .R).coeff g * (W .Q).coeff r * (W .S).coeff s) *
      ((FactorialFockMetric.weight d : ℂ) * (FactorialFockMetric.weight g : ℂ) *
        (FactorialFockMetric.weight r : ℂ) * (FactorialFockMetric.weight s : ℂ))
  rw [dLip_sector_four_occupation D hu hD a N hz hz₁ slot mode bound marks hslot hl hbox]
  have hs := ((hasSum_sum (s := (W .P).support) fun d _ =>
    hasSum_sum (s := (W .R).support) fun g _ =>
      hasSum_sum (s := (W .Q).support) fun r _ =>
        hasSum_sum (s := (W .S).support) fun s _ =>
          (dLipChargeTerm_hasSum D hD a d g r s hz hz₁).mul_left (factor d g r s)).mul_left c
    ).mul_left ((-1 : ℂ) ^ (L : ℤ))
  have hp := (hasSum_sum
    (s := Finset.range ((H : ℤ) + K + L - m - n - r - 3).toNat) fun ell _ =>
      (dLip_projector_hasSum D hD a H L 0 (m+n+r+ell-H-L+1)
        P Q R ((oscillatorLower D ^ ell) S) hz hz₁).mul_left
        ((-1 : ℂ) ^ ell / (ell.factorial : ℂ))).mul_left
      (c * (scale .P * scale .R * scale .Q * scale .S))
  refine hs.unique (hp.congr_fun ?_)
  intro q
  have he := dLip_inverse_words_projector D hu q.val N H K L m n r z words hP hQ hR hS hsupp
  dsimp only at he
  rw [dLip_four_charge_projection D q.val N z (W .P) (W .R) (W .Q) (W .S)
    (hbox _) (hbox _) (hbox _) (hbox _)] at he
  change (-1 : ℂ) ^ (L : ℤ) *
    (∑ d ∈ (W .P).support, ∑ g ∈ (W .R).support, ∑ r ∈ (W .Q).support,
      ∑ s ∈ (W .S).support, factor d g r s * dLipChargeTerm D q.val d g r s z) =
      (scale .P * scale .R * scale .Q * scale .S) *
        ∑ ell ∈ Finset.range ((H : ℤ) + K + L - m - n - r - 3).toNat,
          ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
            projectOccupations D H L 0 (m+n+r+ell-H-L+1)
              P Q R ((oscillatorLower D ^ ell) S)
              (fun d g r s => dLipChargeTerm D q.val d g r s z) at he
  linear_combination c * he

/-- On a homogeneous creation word the product of the chosen inverse
half-current scales is the inverse scale to its doubled weight. -/
theorem wordScale_of_homogeneous (D : LatticeData) (c : Chart) (z : ℝ)
    (s : Puncture) (xs : List (Index D)) (w : ℤ) (hroot : scaleRoot c z s ≠ 0)
    (hw : (creationWord D xs).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) w) :
    wordScale D c z s xs = (scaleRoot c z s)⁻¹ ^ w := by
  let deg (l : List (Index D)) := (l.map fun i => (omega D i : ℤ)).sum
  have hhom (l : List (Index D)) :
      (creationWord D l).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (deg l) := by
    induction l with
    | nil => exact isWeightedHomogeneous_one (R := ℂ) (fun i : Index D => (omega D i : ℤ))
    | cons i l ih =>
      exact (isWeightedHomogeneous_X (R := ℂ) (fun i => (omega D i : ℤ)) i).mul ih
  have hnz (l : List (Index D)) : creationWord D l ≠ 0 := by
    induction l with
    | nil => exact one_ne_zero
    | cons i l ih => exact mul_ne_zero (X_ne_zero i) ih
  have hd := MvPolynomial.IsWeightedHomogeneous.inj_right (hnz xs) (hhom xs) hw
  rw [← hd]
  clear hd hw
  induction xs with
  | nil => simp [wordScale, deg]
  | cons i l ih =>
    rw [show wordScale D c z s (i :: l) =
      incomingScale c z s i.2 * wordScale D c z s l from rfl, ih]
    change (scaleRoot c z s)⁻¹ ^ (2 * i.2 + 1) * (scaleRoot c z s)⁻¹ ^ deg l =
      (scaleRoot c z s)⁻¹ ^ ((omega D i : ℤ) + deg l)
    rw [zpow_add₀ (inv_ne_zero hroot), zpow_natCast]
    rfl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
