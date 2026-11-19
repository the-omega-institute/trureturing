/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipRadialChannel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipRadialChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original D Laurent channel is the normalized physical Taylor readout. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipScales
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialScalars

/-! The real D boundary uses the original Laurent amplitude, including
the signed lowering weights and cutoff. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open Complex Filter LatticeGeneratingFieldLocality
open scoped Topology
open LatticeHalfFockChargedCoefficients (omega)
open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMChargeCoset (oscillatorLower fourierSign quadraticSign quadraticSign_add)
open OriginalFourMProjectionModes (physical_chart_coefficient_overlap_normalized)
open OriginalFourMRadialScalars (radial_factors)
open OriginalFourMSectorContinuation (dLipChargeSector)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open FourPoint.FourPointChannelCoefficients (loweringWeight loweringCutoff)
open private punctureWords creationWord modesBounded from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private dLipLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private wordScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private fourier_from_D fourierRow from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private quadraticSign_square from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

private theorem fourierSign_comm (D : LatticeData) (a b : ModTwoCharge D) :
    fourierSign D a b = fourierSign D b a := by
  have ha : quadraticSign D a ≠ 0 := fun h => by
    have hs := quadraticSign_square D a
    rw [h, zero_mul] at hs
    exact zero_ne_one hs
  have hb : quadraticSign D b ≠ 0 := fun h => by
    have hs := quadraticSign_square D b
    rw [h, zero_mul] at hs
    exact zero_ne_one hs
  apply mul_left_cancel₀ (mul_ne_zero ha hb)
  rw [← quadraticSign_add D a b, mul_comm (quadraticSign D a), ← quadraticSign_add D b a, add_comm]

/-- The A and D sector combinations agree with the normalized B jet.
The two rows are the actual ones used in the original Laurent channels. -/
theorem physical_weighted_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    {X : Type*} [Fintype X] [DecidableEq X] (slot : X → Puncture)
    (colour : X → Fin D.rank) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (n : X ⊕ X → ℕ) (l : List (X ⊕ X)) (a : ModTwoCharge D) :
    let jet := fun c a => spatialCoefficient n l (fun z : (X ⊕ X) → ℂ =>
      physicalProduct D hu slot colour true x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
    (∑ b, quadraticSign D b * fourierSign D b a * jet .A b) =
      (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * jet .B a ∧
    (∑ b, quadraticSign D (b + a) * jet .D b) =
      (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * jet .B a := by
  classical
  dsimp only
  let jet := fun c a => spatialCoefficient n l (fun z : (X ⊕ X) → ℂ =>
    physicalProduct D hu slot colour true x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
  let A := jet .A
  have h (b : ModTwoCharge D) := physical_chart_coefficient_overlap_normalized
    D hu hD h24 slot colour true hx hx₁ hwA hw n l b
  have hD' (b : ModTwoCharge D) : jet .D b = fourierRow D b A := by
    have h₂ : (2 : ℂ) ^ (12 : ℕ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h₂
    rw [fourierRow, ← mul_assoc, mul_inv_cancel₀ h₂, one_mul]
    exact (h b).1
  have hB : (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * jet .B a =
      ∑ b, fourierSign D a b * quadraticSign D b * A b := (h a).2
  change (∑ b, quadraticSign D b * fourierSign D b a * A b) = _ ∧
    (∑ b, quadraticSign D (b + a) * jet .D b) = _
  rw [hB]
  constructor
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [fourierSign_comm D b a, mul_comm (quadraticSign D b)]
  · simp only [hD', add_comm _ a]
    have he := fourier_from_D D hu hD h24 A a
    have h₂ : (2 : ℂ) ^ (12 : ℕ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ (inv_ne_zero h₂)
    simpa only [fourierRow, mul_assoc] using he.symm

/-- At a fixed D-sector charge, the physical jet equals the literal real
boundary Laurent readout with the common four-point normalization. -/
theorem dLip_radial_channel (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (N H K L : ℕ) (m n r : ℤ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (marks : Puncture → List X) (hslot : ∀ s j, j ∈ marks s → slot j = s)
    (hl : ((punctureWords marks).flatMap Prod.snd).Nodup)
    (hbox : ∀ s, modesBounded D N (inverseLoweredWord D .D x s ((marks s).map mode)))
    (hsupp : ∀ s j, modesBounded D N
      ((oscillatorLower D ^ j) (creationWord D ((marks s).map mode))))
    (hP : (creationWord D ((marks .P).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : (creationWord D ((marks .Q).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : (creationWord D ((marks .R).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : (creationWord D ((marks .S).map mode)).IsWeightedHomogeneous
      (fun i => (omega D i : ℤ)) (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3)) :
    let l := (punctureWords marks).flatMap Prod.snd
    let P := creationWord D ((marks .P).map mode)
    let Q := creationWord D ((marks .Q).map mode)
    let R := creationWord D ((marks .R).map mode)
    let S := creationWord D ((marks .S).map mode)
    let t := parameter .D (x : ℂ)
    let s := m+n+r
    let common := (x : ℂ) ^ (-s-5) * (1 - (x : ℂ)) ^ (3 : ℕ)
    spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
      (l.map Sum.inr ++ l.map Sum.inl) (fun u =>
        physicalProduct D hu slot (fun i => (mode i).1) true x .D a
          (u ∘ Sum.inl) (u ∘ Sum.inr)) 0 =
      (-I * common) * ∑ ell ∈ Finset.range (loweringCutoff H K L m n r),
        loweringWeight s ell * dLipLaurent D true H L (s + ell)
          P R Q ((oscillatorLower D ^ ell) S) a t := by
  classical
  dsimp only
  let l := (punctureWords marks).flatMap Prod.snd
  let s := m+n+r
  let w := (H : ℤ)+K+L-s-2
  let t := parameter .D (x : ℂ)
  let scale := fun p => wordScale D .D x p ((marks p).map mode)
  let phase := (-1 : ℂ) ^ (L : ℤ)
  let c := (l.map fun i => relative .D (slot i)).prod * (1-t) ^ (3 : ℕ)
  let common := (x : ℂ) ^ (-s-5) * (1 - (x : ℂ)) ^ (3 : ℕ)
  have hp : phase * phase = 1 := by
    dsimp only [phase]
    rw [← mul_zpow]
    norm_num
  have hx₀ : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hx₁' : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]
    exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hx₁.ne')
  have hScale := dLip_marked_scale_factor D H K L w hx hx₁ slot mode marks
    hslot hP hQ hR hS
  dsimp only at hScale
  have hRadial := (radial_factors H K L s w rfl hx₀ hx₁').2.2
  have hcoef :
      phase * c * (scale .P * scale .R * scale .Q * scale .S) =
      (-I * common) * ((-1 : ℂ) ^ (s+2) * (-t) ^ (-((H : ℤ)+L))) := by
    rw [show phase * c * (scale .P * scale .R * scale .Q * scale .S) =
      phase * (l.map fun i => relative .D (slot i)).prod *
        (1-t) ^ (3 : ℕ) * (scale .P * scale .R * scale .Q * scale .S) by
          dsimp only [c]; ring, hScale]
    rw [show -((H : ℤ)+L) = -(H : ℤ)-L by ring]
    have eq := congrArg ((-I) * ·) hRadial
    dsimp only [common, t, parameter]
    simpa only [mul_assoc] using eq
  have hj := dLip_chart_signed_projector D hu hD a N H K L m n r hx hx₁
    slot mode bound marks hslot hl hbox hsupp hP hR hQ hS
  dsimp only at hj
  have hph : phase ≠ 0 := zpow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hph
  rw [hj]
  apply mul_left_cancel₀ hph
  rw [← mul_assoc phase phase, hp, one_mul]
  unfold dLipLaurent loweringWeight loweringCutoff
  simp only [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  rw [show s + (ell : ℤ) + 2 = (s+2) + (ell : ℤ) by ring, zpow_add₀ (by norm_num),
    zpow_natCast]
  linear_combination ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
    projectOccupations D H L 0 (s+ell-H-L+1)
      (creationWord D ((marks .P).map mode)) (creationWord D ((marks .R).map mode))
      (creationWord D ((marks .Q).map mode)) ((oscillatorLower D ^ ell)
        (creationWord D ((marks .S).map mode)))
      (fun d g r s => dLipChargeSector D true a d g r s t) * hcoef

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open Complex Filter LatticeGeneratingFieldLocality
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open OriginalFourPointChartGluing (rA rB)

/-- The two literal chart comparisons on the common real interval close
the original signed four-point identity by the slit continuation. -/
theorem identityK_of_real_interval_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D)
    (hAB : ∀ (b : ModTwoCharge D) (x : ℝ), 1/2 < x → x < 1 →
      slitChannelA D H K (m+n+r) P Q R S b (rA (x : ℂ)) =
        (2 : ℂ) ^ 12 * (x : ℂ) ^ (m+n+r+2) *
          slitChannelB D H K L m n r P Q R S b (rB (x : ℂ)))
    (hAD : ∀ (b : ModTwoCharge D) (x : ℝ), 1/2 < x → x < 1 →
      slitChannelA D H K (m+n+r) P Q R S b (rA (x : ℂ)) =
        dLipChannel D true H K L m n r P Q R S b (x : ℂ)⁻¹) :
    identityK D hu H K L m n r P Q R S := by
  apply identityK_of_radial_crossings D hu hD h24 true H K L m n r P Q R S
    (x := (3/4 : ℝ)) (t := (4/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  · intro b
    filter_upwards [eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 3/4),
      eventually_lt_nhds (by norm_num : (3/4 : ℝ) < 1)] with x hx hx₁
    exact hAB b x hx hx₁
  · intro b
    filter_upwards [eventually_gt_nhds (by norm_num : (1 : ℝ) < 4/3),
      eventually_lt_nhds (by norm_num : (4/3 : ℝ) < 2)] with t ht ht₂
    have hp : 0 < t := by linarith
    have hx : (1/2 : ℝ) < t⁻¹ := by
      rw [← one_div, lt_div_iff₀ hp]
      linarith
    have hx₁ : t⁻¹ < 1 := (inv_lt_one₀ hp).2 ht
    simpa only [rA, ofReal_inv, inv_inv] using hAD b t⁻¹ hx hx₁

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
