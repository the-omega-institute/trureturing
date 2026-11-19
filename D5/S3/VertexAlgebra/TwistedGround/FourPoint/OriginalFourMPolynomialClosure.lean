/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPolynomialClosure
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPolynomialClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite multilinear extension of the original radial A and D comparison. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialClosure

/-! The signed D-channel readout is multilinear in its original oscillator
slots, including the lowered detector. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open Complex MvPolynomial
open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedCoefficients (omega)
open OriginalFourMSectorContinuation (dLipChargeSector)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open OriginalFourMActualChart (Puncture)
open OriginalFourPointChartGluing (rA)
open LatticeHalfFockChargedTensorCoefficients (chargeNorm)
open OriginalFourMEnergyCoefficient (doubledWeight selector)
open OriginalFourMChargeCoset (oscillatorLower quadraticSign slitChannelA slitChannelB dLipChannel)
open FourPoint.FourPointChannelCoefficients (loweringWeight loweringCutoff)
open private creationWord from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private monomialWord monomialWord_prod from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
open private FourForm projectForm projectForm_apply slitAForm slitAForm_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialChannels
open private dLipLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private projectOccupations from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private lowered_support_weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes
open private slitDiagonal slitLaurent slitLowered from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

private theorem project_off_detector_degree (D : LatticeData) (hu : IsUnit D.G.det)
    (H K E ell : ℕ) (t dR dS : ℤ) (P Q R S : Oscillator D)
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dR)
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dS)
    (hne : 2 * (t - (E : ℤ) + 1) ≠ dR - dS + 2 * (ell : ℤ))
    (F : (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → ℂ) :
    projectOccupations D H K E t P Q R ((oscillatorLower D ^ ell) S) F = 0 := by
  classical
  unfold projectOccupations
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => mul_eq_zero.mpr (Or.inr ?_)
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ =>
    Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun s hs => ?_
  have hzero : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  have hr' : doubledWeight D r = dR := hR (mem_support_iff.mp hr)
  have hs' := lowered_support_weight D hu S dS hS ell s hs
  have hselect : selector D 0 (-2 * t - 2) E r s = 0 := by
    unfold selector
    rw [hzero, add_zero, hr', hs', ite_eq_right]
    omega
  rw [hselect, mul_zero, zero_mul]

set_option maxHeartbeats 2000000 in
private theorem radial_channels_off_detector_degree
    (D : LatticeData) (hu : IsUnit D.G.det) (H K L : ℕ) (m n r d : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (zA zB zD : ℂ)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d)
    (hne : d ≠ 2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3) :
    slitChannelA D H K (m+n+r) P Q R S a zA = 0 ∧
    slitChannelB D H K L m n r P Q R S a zB = 0 ∧
    dLipChannel D true H K L m n r P Q R S a zD = 0 := by
  classical
  have hz (J M T : ℕ) (ell : ℕ) (p q u : Oscillator D)
      (hT : u.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (T : ℤ) - 3))
      (hSum : (J : ℤ) + M + T = (H : ℤ) + K + L)
      (F : (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → ℂ) :
      projectOccupations D J M 0 (m + n + r + ell - J - M + 1) p q u
        ((oscillatorLower D ^ ell) S) F = 0 := by
    apply project_off_detector_degree D hu J M 0 ell _ _ d p q u S hT hS _ F
    omega
  refine ⟨?_, ?_, ?_⟩
  · unfold slitChannelA
    refine Finset.sum_eq_zero fun b _ => ?_
    unfold slitLaurent slitDiagonal
    have zero := hz H K L 0 P Q R hR rfl
      (fun d g r s => OriginalFourMSectorContinuation.slitChargeSector D b d g r s zA)
    simp only [Nat.cast_zero, add_zero, pow_zero, Module.End.one_apply] at zero
    rw [zero, mul_zero, mul_zero]
  · unfold slitChannelB slitLowered
    refine Finset.sum_eq_zero fun ell _ => ?_
    unfold slitLaurent slitDiagonal
    rw [hz K L H ell Q R P hP (by ring), mul_zero, mul_zero]
  · unfold dLipChannel
    refine Finset.sum_eq_zero fun b _ => mul_eq_zero.mpr (Or.inr ?_)
    refine Finset.sum_eq_zero fun ell _ => ?_
    unfold dLipLaurent
    rw [hz H L K ell P R Q hQ (by ring), mul_zero, mul_zero]

private def dLipLaurentForm (D : LatticeData) (H K : ℕ) (s : ℤ)
    (a : ModTwoCharge D) (t : ℂ) : FourForm D :=
  (-t) ^ (-((H : ℤ) + K)) •
    projectForm D H K (s - H - K + 1) (fun p q r u => dLipChargeSector D true a p q r u t)

private theorem dLipLaurentForm_apply (D : LatticeData) (H K : ℕ) (s : ℤ)
    (a : ModTwoCharge D) (t : ℂ) (v : Fin 4 → Oscillator D) :
    dLipLaurentForm D H K s a t v =
      dLipLaurent D true H K s (v 0) (v 1) (v 2) (v 3) a t := by
  simp only [dLipLaurentForm, smul_apply, smul_eq_mul,
    projectForm_apply, dLipLaurent]

private def dLipForm (D : LatticeData) (H K L : ℕ) (m n r : ℤ)
    (b : ModTwoCharge D) (t : ℂ) : FourForm D :=
  ∑ a, quadraticSign D (a + b) •
    ∑ ell ∈ Finset.range (loweringCutoff H K L m n r), loweringWeight (m + n + r) ell •
      ((dLipLaurentForm D H L (m + n + r + ell) a t).compLinearMap
        ![LinearMap.id, LinearMap.id, LinearMap.id, oscillatorLower D ^ ell]).domDomCongr
          (Equiv.swap 1 2)

set_option maxHeartbeats 1000000 in
private theorem dLipForm_apply (D : LatticeData) (H K L : ℕ) (m n r : ℤ)
    (b : ModTwoCharge D) (t : ℂ) (v : Fin 4 → Oscillator D) :
    dLipForm D H K L m n r b t v =
      dLipChannel D true H K L m n r (v 0) (v 1) (v 2) (v 3) b t := by
  have h₀ : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have h₁ : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have h₂ : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have h₃ : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  simp only [dLipForm, dLipChannel, sum_apply, smul_apply,
    MultilinearMap.domDomCongr, MultilinearMap.coe_mk, MultilinearMap.compLinearMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, LinearMap.id_apply, smul_eq_mul,
    dLipLaurentForm_apply, h₀, h₁, h₂, h₃]

set_option maxHeartbeats 2000000 in
/-- Equality on homogeneous creation words gives the full homogeneous A/D
comparison, using the same signed charge sum and lowered detector. -/
theorem radial_AD_crossing_of_words (D : LatticeData) (H K L : ℕ) (m n r : ℤ)
    (a : ModTwoCharge D) (x : ℝ)
    (hwords : ∀ words : Puncture → List (Index D),
      let P := creationWord D (words .P)
      let Q := creationWord D (words .Q)
      let R := creationWord D (words .R)
      let S := creationWord D (words .S)
      P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3) →
      Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3) →
      R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3) →
      S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
        (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3) →
      slitChannelA D H K (m + n + r) P Q R S a (rA (x : ℂ)) =
        dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹)
    (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    slitChannelA D H K (m + n + r) P Q R S a (rA (x : ℂ)) =
      dLipChannel D true H K L m n r P Q R S a (x : ℂ)⁻¹ := by
  classical
  let v : Fin 4 → Oscillator D := ![P, Q, R, S]
  let d : Fin 4 → ℤ := ![2 * (H : ℤ) - 3, 2 * (K : ℤ) - 3, 2 * (L : ℤ) - 3,
    2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3]
  have hv (i : Fin 4) : (v i).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (d i) := by
    fin_cases i <;> assumption
  let A := slitAForm D H K (m + n + r) a (rA (x : ℂ))
  let F := dLipForm D H K L m n r a (x : ℂ)⁻¹
  suffices A v = F v by simpa [A, F, v, slitAForm_apply, dLipForm_apply] using this
  have expand : v = (fun i => ∑ e ∈ (v i).support, monomial e ((v i).coeff e)) := by
    funext i
    exact (v i).as_sum
  conv_lhs => rw [expand, A.map_sum_finset]
  conv_rhs => rw [expand, F.map_sum_finset]
  refine Finset.sum_congr rfl fun e he => ?_
  have hm (i : Fin 4) :
      (monomial (e i) (1 : ℂ)).IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (d i) :=
    isWeightedHomogeneous_monomial _ _ _ (hv i (mem_support_iff.mp ((Fintype.mem_piFinset.mp he) i)))
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
  simpa only [A, F, slitAForm_apply, dLipForm_apply, hp, hq, hr, ht] using
    hwords words (by rw [hp]; exact hm 0) (by rw [hq]; exact hm 1)
      (by rw [hr]; exact hm 2) (by rw [ht]; exact hm 3)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
