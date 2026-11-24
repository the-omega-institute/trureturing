/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureFirstBox
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact joint enclosure on the first compact short-gap subbox. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureScore
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMarginalBoxError

/-! The short-gap subbox near lower coordinate four and gap one, at spacing at most 3/22. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureFirstBox

open CompactTaylorModel (Model InBox)

open private neg neg_sound inverse inverse_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox
open private CompactTaylorModel.Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

private def U : Model := Model.affineCoordinate 0 (127 / 32) (1 / 32)
private def D : Model := Model.affineCoordinate 1 (15 / 16) (1 / 16)
private def H : Model := Model.affineCoordinate 2 (3 / 44) (3 / 44)
private def midpointOffset : Model :=
  (Model.affineCoordinate 0 0 (-1 / 32)).add (Model.affineCoordinate 1 0 (-1 / 32))

private def jointDensity (i : Fin 3) : Model :=
  shortJointClosedQuadratureModel i (3 / 22) (9 / 2) (1 / 16) (-71 / 16) 36 5 H midpointOffset

def joint : Model :=
  let D₂ := D.mul D
  (jointDensity 0).add (D₂.mul ((jointDensity 1).add (D₂.mul (jointDensity 2))))

private theorem jointDensity_sound (i : Fin 3) {s t z u v h : ℝ}
    (hb : InBox s t z) (hh : 0 ≤ h) (hhmax : h ≤ 3 / 22)
    (hH : H.Encloses s t z h) (hs : s = 32 * u - 127) (ht : t = 16 * (v - u) - 15) :
    (jointDensity i).Encloses s t z (shortJointClosedQuadrature i h (-((u + v) / 2))) := by
  let offset := -(s / 32) - t / 32
  have hx : midpointOffset.Encloses s t z offset := by
    unfold midpointOffset
    convert Model.add_sound (Model.affineCoordinate_sound hb 0 0 (-1 / 32))
      (Model.affineCoordinate_sound hb 1 0 (-1 / 32)) using 1
    norm_num [offset]
    ring
  have hw : |offset| ≤ 1 / 16 := by
    refine (abs_sub _ _).trans ?_
    have hs₀ := hb.1
    have ht₀ := hb.2.1
    simp only [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hmodel := shortJointClosedQuadratureModel_sound (upper := 3 / 22) (center := -71 / 16)
    (radius := 9 / 2) (width := 1 / 16) (terms := 36) (order := 5)
    i hb hH hx hh (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhmax)
    (by decide) (by decide) (by norm_num; linarith) (by simpa using hw) (by norm_num)
  have hc : ((-71 / 16 : ℚ) : ℝ) + offset = -((u + v) / 2) := by
    norm_num [offset, hs, ht]
    ring
  simpa only [jointDensity, hc] using hmodel

theorem joint_sound {s t z u v h : ℝ} (hb : InBox s t z)
    (hh : 0 ≤ h) (hhmax : h ≤ 3 / 22)
    (hs : s = 32 * u - 127) (ht : t = 16 * (v - u) - 15) (hz : z = 44 * h / 3 - 1) :
    joint.Encloses s t z ((3 + h) * (3 + 2 * h) / 2 *
      shortJointFourthQuadrature h ((u + v) / 2) (v - u)) := by
  have hH : H.Encloses s t z h := by
    unfold H
    convert Model.affineCoordinate_sound hb 2 (3 / 44) (3 / 44) using 1
    norm_num [hz]
    ring
  have hD : D.Encloses s t z (v - u) := by
    unfold D
    convert Model.affineCoordinate_sound hb 1 (15 / 16) (1 / 16) using 1
    norm_num [ht]
    ring
  exact shortJointFourthQuadrature_model_sound hb hh hD
    (jointDensity_sound 0 hb hh hhmax hH hs ht) (jointDensity_sound 1 hb hh hhmax hH hs ht)
    (jointDensity_sound 2 hb hh hhmax hH hs ht)

private def V : Model := U.add D
private def offsetU : Model := Model.affineCoordinate 0 0 (1 / 32)
private def offsetD : Model := Model.affineCoordinate 1 0 (1 / 16)
private def offsetV : Model := offsetU.add offsetD

private def marginal (j : Fin 3) (center radius width : ℚ) (cap : ℕ) (X : Model) : Model :=
  (marginalClosedQuadratureModel (3 / 22) radius width center j 36 5 H X).widen
    (shortMarginalMeshError (3 / 22) radius cap j)

private def reflectedLower (j : Fin 3) : Model := marginal j (-127 / 32) 4 (1 / 32) 4 (neg offsetU)
private def reflectedUpper (j : Fin 3) : Model := marginal j (-157 / 32) 5 (3 / 32) 5 (neg offsetV)
private def directUpper (j : Fin 3) : Model := marginal j (157 / 32) 5 (3 / 32) 10 offsetV
private def directGap (j : Fin 3) : Model := marginal j (15 / 16) 1 (1 / 16) 2 offsetD

private def rateGap : Model := neg (CompactTaylorModel.positiveRateGapModel H (neg U))
private def decayInput : Model := neg (((Model.ofRat 1).add H).mul U)

private def rootCandidate (m : Model) : Model :=
  let S : ℚ := CompactTaylorModel.scale
  let c := CompactTaylorModel.Model.center m
  let r := (Nat.sqrt (⌊c * S ^ 2⌋ : ℤ).toNat : ℚ) / S
  let δ := (m.sub (Model.ofRat c)).mul (Model.ofRat c⁻¹)
  (Model.horner [1, 1 / 2, -1 / 8, 1 / 16, -5 / 128, 7 / 256,
    -21 / 1024, 33 / 2048, -429 / 32768] δ).mul (Model.ofRat r)

private def radicand : Model := (directUpper 0).mul (directGap 0)
private def rootPolynomial : DimThree.Certificate.Sparse := (rootCandidate radicand).polynomial
private def rootLower : ℕ := Nat.sqrt (radicand.lower.toNat * CompactTaylorModel.scale)

private theorem root_sound {A : Model} {s t z x : ℝ} (hb : InBox s t z)
    (hx : A.Encloses s t z x) (P : DimThree.Certificate.Sparse)
    (hA : 0 ≤ A.lower) (hP : 0 < (⟨P, 0⟩ : Model).lower) :
    (CompactTaylorModel.radicalFrom A P (Nat.sqrt (A.lower.toNat * CompactTaylorModel.scale))
      (⟨P, 0⟩ : Model).lower.toNat).Encloses s t z (Real.sqrt x) :=
  CompactTaylorModel.radicalFrom_lower_sound hb hx P hA hP
    (Nat.sqrt_le' (A.lower.toNat * CompactTaylorModel.scale))

private def inputs : ShortQuadratureScoreInputs where
  lowerCoordinate := U
  gap := D
  spacing := H
  inverseLower := inverse U
  inverseUpper := inverse V
  reflectedLowerSlope := (reflectedLower 1).mul (inverse (reflectedLower 0))
  reflectedUpperSlope := (reflectedUpper 1).mul (inverse (reflectedUpper 0))
  upperSlope := (directUpper 1).mul (inverse (directUpper 0))
  gapSlope := (directGap 1).mul (inverse (directGap 0))
  gapSecondRatio := (directGap 2).mul (inverse (directGap 0))
  inverseRateGap := inverse rateGap
  decay := decayInput.centeredExp
  growth := U.centeredExp
  joint := joint
  upperMarginal := directUpper 0
  gapMarginal := directGap 0
  gapMarginalDeriv := directGap 1
  root := CompactTaylorModel.radicalFrom radicand rootPolynomial rootLower
    (⟨rootPolynomial, 0⟩ : Model).lower.toNat

private theorem marginal_sound {p : ℕ} (hp : 0 < p) {s t z x offset : ℝ}
    {center radius width : ℚ} {cap : ℕ} (j : Fin 3) {X : Model} (hb : InBox s t z)
    (hH : H.Encloses s t z (3 / (p : ℝ))) (hhmax : 3 / (p : ℝ) ≤ 3 / 22)
    (hX : X.Encloses s t z offset) (hx : (center : ℝ) + offset = x)
    (hr : |(center : ℝ)| + |offset| ≤ (radius : ℝ)) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (36 : ℝ) - 2)
    (hneg : -(cap : ℝ) ≤ x) (hpos : 2 * x ≤ (cap : ℝ)) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    (marginal j center radius width cap X).Encloses s t z
      (iteratedDeriv (j : ℕ) (fun a ↦ (J * compactKappa p) * compactZ p a) x) := by
  have h := marginalClosedQuadratureModel_widen_meshError_sound (upper := 3 / 22)
    (N := cap) (terms := 36)
    (order := 5) j hb hp hH hX (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhmax)
    (by decide) (by decide) hr hw hratio (by rw [hx]; exact hneg) (by rw [hx]; exact hpos)
  simpa only [marginal, hx] using h

private structure Checks : Prop where
  lowerPos : 0 < U.lower
  upperPos : 0 < V.lower
  reflectedLowerPos : 0 < (reflectedLower 0).lower
  reflectedUpperPos : 0 < (reflectedUpper 0).lower
  directUpperPos : 0 < (directUpper 0).lower
  directGapPos : 0 < (directGap 0).lower
  rateGapPos : 0 < rateGap.lower
  rateGapSmall : (H.mul (neg U)).argumentRadius ≤ 2
  decayOk : decayInput.expChecks
  growthOk : U.expChecks
  radicandNonneg : 0 ≤ radicand.lower
  rootPos : 0 < (⟨rootPolynomial, 0⟩ : Model).lower
  sign : 0 < inputs.score.lower

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem sign_of_checks {p : ℕ} {u v : ℝ} (checks : Checks)
    (hp : 22 ≤ p) (hu₀ : 63 / 16 ≤ u) (hu₁ : u ≤ 4)
    (hd₀ : 7 / 8 ≤ v - u) (hd₁ : v - u ≤ 1) :
    0 < shortQuadratureNegativeScore p u v := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let s := 32 * u - 127
  let t := 16 * d - 15
  let z := 44 * h / 3 - 1
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (x : ℝ) := (J * compactKappa p) * compactZ p x
  have hp₀ : 0 < p := by omega
  have hpR : (22 : ℝ) ≤ p := by exact_mod_cast hp
  have hpP : (0 : ℝ) < p := by linarith
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h ≤ 3 / 22 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hv₀ : (77 : ℝ) / 16 ≤ v := by linarith
  have hv₁ : v ≤ 5 := by linarith
  have hb : InBox s t z := by
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
      dsimp only [s, t, d, z] <;> linarith
  have hU : U.Encloses s t z u := by
    unfold U
    convert Model.affineCoordinate_sound hb 0 (127 / 32) (1 / 32) using 1
    norm_num [s]
    ring
  have hD : D.Encloses s t z d := by
    unfold D
    convert Model.affineCoordinate_sound hb 1 (15 / 16) (1 / 16) using 1
    norm_num [t]
    ring
  have hH : H.Encloses s t z h := by
    unfold H
    convert Model.affineCoordinate_sound hb 2 (3 / 44) (3 / 44) using 1
    norm_num [z]
    ring
  have hV : V.Encloses s t z v := by
    simpa only [V, d, add_sub_cancel] using Model.add_sound hU hD
  have hxU : offsetU.Encloses s t z (u - 127 / 32) := by
    unfold offsetU
    convert Model.affineCoordinate_sound hb 0 0 (1 / 32) using 1
    norm_num [s]
    ring
  have hxD : offsetD.Encloses s t z (d - 15 / 16) := by
    unfold offsetD
    convert Model.affineCoordinate_sound hb 1 0 (1 / 16) using 1
    norm_num [t]
    ring
  have hxV : offsetV.Encloses s t z (v - 157 / 32) := by
    unfold offsetV
    convert Model.add_sound hxU hxD using 1
    dsimp only [d]
    ring
  have huWidth : |u - 127 / 32| ≤ (1 / 32 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdWidth : |d - 15 / 16| ≤ (1 / 16 : ℝ) := abs_le.mpr ⟨by
    dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hvWidth : |v - 157 / 32| ≤ (3 / 32 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hru (j : Fin 3) : (reflectedLower j).Encloses s t z (iteratedDeriv (j : ℕ) q (-u)) := by
    unfold reflectedLower
    apply marginal_sound hp₀ j hb hH hhmax (neg_sound hxU)
    all_goals norm_num [abs_neg] <;> linarith [show |127 / 32 - u| ≤ (1 / 32 : ℝ) from
      (abs_sub_comm u (127 / 32)) ▸ huWidth]
  have hrv (j : Fin 3) : (reflectedUpper j).Encloses s t z (iteratedDeriv (j : ℕ) q (-v)) := by
    unfold reflectedUpper
    apply marginal_sound hp₀ j hb hH hhmax (neg_sound hxV)
    all_goals norm_num [abs_neg] <;> linarith [show |157 / 32 - v| ≤ (3 / 32 : ℝ) from
      (abs_sub_comm v (157 / 32)) ▸ hvWidth]
  have hvq (j : Fin 3) : (directUpper j).Encloses s t z (iteratedDeriv (j : ℕ) q v) := by
    unfold directUpper
    apply marginal_sound hp₀ j hb hH hhmax hxV
    all_goals norm_num <;> linarith
  have hdq (j : Fin 3) : (directGap j).Encloses s t z (iteratedDeriv (j : ℕ) q d) := by
    unfold directGap
    apply marginal_sound hp₀ j hb hH hhmax hxD
    all_goals norm_num [d] <;> linarith
  have hRate : rateGap.Encloses s t z (upperTailGap h u) := by
    unfold rateGap
    have hM := neg_sound (CompactTaylorModel.positiveRateGapModel_sound hb hH (neg_sound hU)
      hh.ne' (show -u ≠ 0 by linarith) checks.rateGapSmall)
    convert hM using 1
    unfold upperTailGap
    rw [mul_neg, ← neg_div]
    ring
  have hC (a : ℚ) := Model.ofRat_sound a s t z
  have hDecay : decayInput.Encloses s t z (-(1 + h) * u) := by
    simpa only [decayInput, Rat.cast_one, neg_mul] using neg_sound
      (Model.mul_sound hb (Model.add_sound (hC 1) hH) hU)
  have hqv₀ : (directUpper 0).Encloses s t z (q v) := by
    simpa only [Fin.val_zero, iteratedDeriv_zero] using hvq 0
  have hqd₀ : (directGap 0).Encloses s t z (q d) := by
    simpa only [Fin.val_zero, iteratedDeriv_zero] using hdq 0
  have hradicand : radicand.Encloses s t z (q v * q d) := Model.mul_sound hb hqv₀ hqd₀
  have hroot : inputs.root.Encloses s t z (Real.sqrt (q v * q d)) := by
    simpa only [inputs, rootLower] using
      root_sound hb hradicand rootPolynomial checks.radicandNonneg checks.rootPos
  have hslope {P Q : Model} {x y : ℝ} (hP : P.Encloses s t z x) (hQ : Q.Encloses s t z y)
      (hpos : 0 < Q.lower) : (P.mul (inverse Q)).Encloses s t z (x / y) := by
    simpa only [div_eq_mul_inv, one_mul] using
      Model.mul_sound hb hP (inverse_sound hb hQ hpos)
  have hgapDeriv : (directGap 1).Encloses s t z (deriv q d) := by
    simpa only [Fin.val_one, iteratedDeriv_one] using hdq 1
  have hJoint : inputs.joint.Encloses s t z (J * shortJointFourthQuadrature h ((u + v) / 2) d) :=
    joint_sound (u := u) (v := v) (h := h) hb hh.le hhmax rfl rfl rfl
  have hbound : inputs.score.Encloses s t z (shortQuadratureNegativeScore p u v) := by
    refine ShortQuadratureScoreInputs.score_sound (m := inputs) (p := p) (u := u) (v := v)
      (s := s) (t := t) (z := z) hb hU hD hH
      (inverse_sound hb hU checks.lowerPos) (inverse_sound hb hV checks.upperPos)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hJoint ?_ ?_ ?_ hroot
    · exact hslope (by
          simpa [q, J, h, iteratedDeriv_one, deriv_const_mul_field] using hru 1)
        (by simpa using hru 0) checks.reflectedLowerPos
    · exact hslope (by
          simpa [q, J, h, iteratedDeriv_one, deriv_const_mul_field] using hrv 1)
        (by simpa using hrv 0) checks.reflectedUpperPos
    · exact hslope (by
          simpa [q, J, h, iteratedDeriv_one, deriv_const_mul_field] using hvq 1)
        hqv₀ checks.directUpperPos
    · exact hslope hgapDeriv hqd₀ checks.directGapPos
    · exact hslope (by
          simpa [q, J, h, d, iteratedDeriv_const_mul_field] using hdq 2)
        hqd₀ checks.directGapPos
    · exact inverse_sound hb hRate checks.rateGapPos
    · exact Model.expChecks_sound hb hDecay checks.decayOk
    · exact Model.expChecks_sound hb hU checks.growthOk
    · simpa only [inputs, q, J, h] using hqv₀
    · simpa only [inputs, q, J, h, d] using hqd₀
    · simpa only [inputs, q, J, h, d] using hgapDeriv
  exact (div_pos (Int.cast_pos.mpr checks.sign) CompactTaylorModel.scale_real_pos).trans_le
    (Model.lower_sound hb hbound)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem firstBoxChecks : Checks := by
  constructor <;> (try unfold Model.expChecks) <;> decide +kernel

/-- The mixed logarithmic derivative is strictly negative on the first
short-gap subbox for spacings at most 3/22. -/
theorem logKernel_mixed_lt {p : ℕ} {u v : ℝ} (hp : 22 ≤ p)
    (hu₀ : 63 / 16 ≤ u) (hu₁ : u ≤ 4) (hd₀ : 7 / 8 ≤ v - u) (hd₁ : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  logKernel_mixed_neg_of_shortQuadratureNegativeScore (by omega) (by linarith)
    (by linarith) hd₁ (sign_of_checks firstBoxChecks hp hu₀ hu₁ hd₀ hd₁)

end RefinedBMV.PositiveCenter.CompactShortQuadratureFirstBox
