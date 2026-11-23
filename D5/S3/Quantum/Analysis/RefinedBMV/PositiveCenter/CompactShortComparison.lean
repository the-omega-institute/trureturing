/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortComparison
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regularized radical and linear mixed terms on the short central strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMoments
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMidpoint
import Batteries.Tactic.OpenPrivate

/-! The mixed comparison computed from the elementary enclosures. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open private hasDerivAt_compactZ_family from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical

private theorem deriv_compositionMoment_eq {p : ℕ} (hp : 0 < p) (d : ℝ) :
    deriv (compositionMoment p 0) d =
      compactKappa p * d * compactZ p d * (2 + d * compactZSlope p d) := by
  have hz : HasDerivAt (compactZ p) (deriv (compactZ p) d) d :=
    (hasDerivAt_compactZ_family hp 0 d).differentiableAt.hasDerivAt
  have hpoly : HasDerivAt (fun x : ℝ => compactKappa p * x ^ 2)
      (compactKappa p * (2 * d)) d := by
    simpa using (hasDerivAt_pow 2 d).const_mul (compactKappa p)
  have hder := (hasDerivAt_compactZ_family hp 0 d).deriv
  change deriv (compactZ p) d =
    SmallCorner.integralMarginalDerivative p (compactKappa p) 1 d at hder
  rw [show compositionMoment p 0 = fun x => compactKappa p * x ^ 2 * compactZ p x
      from funext (compositionMoment_eq_compactZ hp), (hpoly.fun_mul hz).deriv,
    compactZSlope_eq hp, hder]
  field_simp [(compactZ_pos hp d).ne'] <;> ring

private theorem compactMixedT_eq_cutoff {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (J : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let a := 1 / u - compactZSlope p (-u) / 2
    let b := 1 / v - compactZSlope p (-v) / 2
    let k := 1 / upperTailGap h u
    let gamma := 1 + k + a
    compactMixedT p u v J =
      (-gamma) * (2 + h - b) * J - gamma * k * Real.exp (-(1 + h) * u) *
        (1 + compactKappa p * v ^ 2 * compactZ p v) +
      k * Real.exp u * ((gamma - b) * (1 + compactKappa p * d ^ 2 * compactZ p d) +
        compactKappa p * d * compactZ p d * (2 + d * compactZSlope p d)) - a * b := by
  dsimp only [compactMixedT]
  rw [reflectedHalfLogSlope_eq_compactZSlope hp hu.ne',
    reflectedHalfLogSlope_eq_compactZSlope hp hv.ne',
    compositionMoment_eq_compactZ hp v, compositionMoment_eq_compactZ hp (v - u),
    deriv_compositionMoment_eq hp]
  have hk : (3 / (p : ℝ)) / (1 - Real.exp (-(3 / (p : ℝ)) * u)) =
      1 / upperTailGap (3 / (p : ℝ)) u := by
    unfold upperTailGap
    rw [neg_mul, one_div_div]
  change (-_) * _ * J - _ + _ - _ = _
  rw [← hk]
  rfl

def shortRootMultiplier (D SU SV TV TD WD IU : Model) : Model := Id.run do
  let half := Model.ofRat (1 / 2)
  let quarter := Model.ofRat (1 / 4)
  let x := TD.sub SU
  let y := (TV.add TD).add SV
  let curvature := (y.mul (IU.mul half)).add ((x.mul y).mul quarter) |>.add (WD.mul half)
  return (IU.add ((x.add y).mul half)).add (D.mul curvature)

private noncomputable def shortRootMultiplierReal (p : ℕ) (u v : ℝ) : ℝ :=
  let d := v - u
  let s := compactZSlope p
  let x := s d - s (-u)
  let y := s v + s d + s (-v)
  1 / u + (x + y) / 2 + d * (y / (2 * u) + x * y / 4 + deriv s d / 2)

theorem shortRootMultiplier_sound {p : ℕ} {s t z u v : ℝ}
    {D SU SV TV TD WD IU : Model} (hb : InBox s t z)
    (hD : D.Encloses s t z (v - u)) (hSU : SU.Encloses s t z (compactZSlope p (-u)))
    (hSV : SV.Encloses s t z (compactZSlope p (-v)))
    (hTV : TV.Encloses s t z (compactZSlope p v))
    (hTD : TD.Encloses s t z (compactZSlope p (v - u)))
    (hWD : WD.Encloses s t z (deriv (compactZSlope p) (v - u)))
    (hIU : IU.Encloses s t z (1 / u)) :
    (shortRootMultiplier D SU SV TV TD WD IU).Encloses s t z
      (shortRootMultiplierReal p u v) := by
  have hHalf : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hQuarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 4) s t z
  have hX := Model.sub_sound hTD hSU
  have hY := Model.add_sound (Model.add_sound hTV hTD) hSV
  have hCurvature := Model.add_sound (Model.add_sound
    (Model.mul_sound hb hY (Model.mul_sound hb hIU hHalf))
    (Model.mul_sound hb (Model.mul_sound hb hX hY) hQuarter)) (Model.mul_sound hb hWD hHalf)
  unfold shortRootMultiplierReal
  convert Model.add_sound (Model.add_sound hIU
    (Model.mul_sound hb (Model.add_sound hX hY) hHalf)) (Model.mul_sound hb hD hCurvature)
    using 1 <;> first | rfl | (simp only [div_eq_mul_inv]; ring)

open private shortWeightedMoment from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMidpoint

/-- The scalar fourth-order score after taking a tangent upper bound for the square root. -/
noncomputable def shortMidpointTangentScore (p : ℕ) (u v radius root : ℝ) : ℝ :=
  let R := compositionMoment p 0
  let a := reflectedHalfLogSlope R u
  let b := reflectedHalfLogSlope R v
  let w := (u + v) / 2
  let r := (v - u) / 2
  let c := (b - a) / 2
  let B := fun j ↦ shortWeightedMoment p j w a b
  let A := fun j ↦ shortMidpointMoment p j 0 w
  let tail := (1 + a) * (1 + b) * (r ^ 6 / 720 / (1 - radius ^ 2 / 56)) +
    max 0 c * (r ^ 5 / 120 / (1 - radius ^ 2 / 42))
  let tangent := (compactZ p v * compactZ p (v - u) / root + root) / 2
  B 0 + (r ^ 2 / 2) * B 1 + (r ^ 4 / 24) * B 2 +
    (c * r) * A 1 + (c * (r ^ 3 / 6)) * A 2 + tail * A 3 - a * b -
    (-compactKappa p * v * tangent * shortRootMultiplierReal p u v)

/-- A negative fourth-order tangent score gives the desired short-gap kernel sign. -/
theorem logKernel_mixed_neg_of_shortMidpointTangent {p : ℕ} (hp : 0 < p)
    {u v radius root : ℝ} (hu : 0 < u) (huv : u < v) (hroot : 0 < root)
    (hr : 3 * ((v - u) / 2) ≤ radius) (hR : radius ^ 2 / 42 < 1)
    (hmultiplier : 0 ≤ shortRootMultiplierReal p u v)
    (hscore : shortMidpointTangentScore p u v radius root < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have h := logKernel_mixed_le_shortMidpointMajorant hp hu huv hr hR
  dsimp only at h
  rw [shortJointMajorant_eq_moments] at h
  have hq := compactMixedQ_tangent_lower hp hu huv hroot hmultiplier
  have hneg := (h.trans (sub_le_sub_left hq _)).trans_lt hscore
  have hpos : 0 < Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) :=
    Real.sqrt_pos.mpr (mul_pos
      (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
      (compositionMoment_marginal_pos hp (neg_ne_zero.mpr (hu.trans huv).ne')))
  by_contra! hnonneg
  exact hneg.not_ge (mul_nonneg hpos.le hnonneg)

/-- Enclose the fourth-order joint bound using the separation moments of orders zero to six. -/
def shortMidpointJointModel (A B HalfGap MaxSkew : Model) (radius : ℚ)
    (Moment : Fin 4 → Fin 3 → Model) : Model :=
  let half := Model.ofRat (1 / 2)
  let quarter := Model.ofRat (1 / 4)
  let skew := (B.sub A).mul half
  let sum := (A.add B).mul half
  let product := A.mul B
  let weighted := fun i : Fin 3 ↦
    let j := i.castLE (by decide : 3 ≤ 4)
    (((Moment j 2).sub (Moment i.succ 0)).mul quarter).sub (sum.mul (Moment j 1))
      |>.add (product.mul (Moment j 0))
  let evenTail := (((Model.ofRat 1).add A).mul ((Model.ofRat 1).add B)).mul
    ((HalfGap.pow 6).mul (Model.ofRat (1 / 720 / (1 - radius ^ 2 / 56))))
  let oddTail := MaxSkew.mul
    ((HalfGap.pow 5).mul (Model.ofRat (1 / 120 / (1 - radius ^ 2 / 42))))
  (weighted 0)
    |>.add (((HalfGap.pow 2).mul half).mul (weighted 1))
    |>.add (((HalfGap.pow 4).mul (Model.ofRat (1 / 24))).mul (weighted 2))
    |>.add ((skew.mul HalfGap).mul (Moment 1 0))
    |>.add ((skew.mul ((HalfGap.pow 3).mul (Model.ofRat (1 / 6)))).mul (Moment 2 0))
    |>.add ((evenTail.add oddTail).mul (Moment 3 0))

theorem shortMidpointJointModel_sound {p : ℕ} {s t z a b r w : ℝ} {radius : ℚ}
    {A B HalfGap MaxSkew : Model} {Moment : Fin 4 → Fin 3 → Model} (hb : InBox s t z)
    (ha : A.Encloses s t z a) (hb' : B.Encloses s t z b) (hr : HalfGap.Encloses s t z r)
    (hmax : MaxSkew.Encloses s t z (max 0 ((b - a) / 2)))
    (hm : ∀ j k, (Moment j k).Encloses s t z (shortMidpointMoment p j k w)) :
    (shortMidpointJointModel A B HalfGap MaxSkew radius Moment).Encloses s t z
      (shortJointAverage p (fun x y ↦ Real.exp (w * (x + y)) *
        shortPairMajorant r radius a b x y)) := by
  have hone : (Model.ofRat 1).Encloses s t z 1 := by simpa using Model.ofRat_sound 1 s t z
  have hhalf : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hquarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 4) s t z
  have h24 : (Model.ofRat (1 / 24)).Encloses s t z (1 / 24 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 24) s t z
  have h6 : (Model.ofRat (1 / 6)).Encloses s t z (1 / 6 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 6) s t z
  have heven : (Model.ofRat (1 / 720 / (1 - radius ^ 2 / 56))).Encloses s t z
      (1 / 720 / (1 - (radius : ℝ) ^ 2 / 56)) := by
    have h := Model.ofRat_sound (1 / 720 / (1 - radius ^ 2 / 56)) s t z
    rw [Rat.cast_div (1 / 720) (1 - radius ^ 2 / 56)] at h
    push_cast at h
    exact h
  have hodd : (Model.ofRat (1 / 120 / (1 - radius ^ 2 / 42))).Encloses s t z
      (1 / 120 / (1 - (radius : ℝ) ^ 2 / 42)) := by
    have h := Model.ofRat_sound (1 / 120 / (1 - radius ^ 2 / 42)) s t z
    rw [Rat.cast_div (1 / 120) (1 - radius ^ 2 / 42)] at h
    push_cast at h
    exact h
  have hweight (j : Fin 3) :
      let J := j.castLE (by decide : 3 ≤ 4)
      ((((Moment J 2).sub (Moment j.succ 0)).mul (Model.ofRat (1 / 4))).sub
        (((A.add B).mul (Model.ofRat (1 / 2))).mul (Moment J 1))).add
          ((A.mul B).mul (Moment J 0))
        |>.Encloses s t z (shortWeightedMoment p j w a b) := by
    rw [shortWeightedMoment]
    let J := j.castLE (by decide : 3 ≤ 4)
    have h := Model.add_sound
      (Model.sub_sound (Model.mul_sound hb (Model.sub_sound (hm J 2) (hm j.succ 0)) hquarter)
        (Model.mul_sound hb (Model.mul_sound hb (Model.add_sound ha hb') hhalf) (hm J 1)))
      (Model.mul_sound hb (Model.mul_sound hb ha hb') (hm J 0))
    convert h using 1 <;> ring
  have hskew := Model.mul_sound hb (Model.sub_sound hb' ha) hhalf
  have he := Model.mul_sound hb
    (Model.mul_sound hb (Model.add_sound hone ha) (Model.add_sound hone hb'))
    (Model.mul_sound hb (Model.pow_sound hb hr 6) heven)
  have ho := Model.mul_sound hb hmax (Model.mul_sound hb (Model.pow_sound hb hr 5) hodd)
  rw [shortJointMajorant_eq_moments]
  have h := Model.add_sound
    (Model.add_sound
      (Model.add_sound
        (Model.add_sound
          (Model.add_sound (hweight 0)
            (Model.mul_sound hb (Model.mul_sound hb (Model.pow_sound hb hr 2) hhalf) (hweight 1)))
          (Model.mul_sound hb (Model.mul_sound hb (Model.pow_sound hb hr 4) h24) (hweight 2)))
        (Model.mul_sound hb (Model.mul_sound hb hskew hr) (hm 1 0)))
      (Model.mul_sound hb (Model.mul_sound hb hskew
        (Model.mul_sound hb (Model.pow_sound hb hr 3) h6)) (hm 2 0)))
    (Model.mul_sound hb (Model.add_sound he ho) (hm 3 0))
  convert h using 1 <;> first | rfl | (norm_num [Fin.val_ofNat, Fin.val_natCast] <;> ring)

/-- The polynomial arithmetic for the regularized score, given the elementary functions. -/
def shortScore (U D H ZV ZD SU SV TV TD WD IU IV K ExpU Decay Joint Radical : Model) : Model := Id.run do
  let O := Model.ofRat 1
  let F := Model.ofRat (1 / 2)
  let quarter := Model.ofRat (1 / 4)
  let Two := Model.ofRat 2
  let V := U.add D
  let varianceHalf := (O.add H).mul quarter
  let alpha := IU.sub (SU.mul F)
  let beta := IV.sub (SV.mul F)
  let radical := (((Model.zero.sub varianceHalf).mul V).mul Radical).mul
    (shortRootMultiplier D SU SV TV TD WD IU)
  let defectD := (varianceHalf.mul (D.pow 2)).mul ZD
  let defectV := (varianceHalf.mul (V.pow 2)).mul ZV
  let derivativeD := ((varianceHalf.mul D).mul ZD).mul (Two.add (D.mul TD))
  let gamma := (O.add K).add alpha
  let linear := ((Model.zero.sub gamma).mul ((Two.add H).sub beta)).mul Joint
    |>.sub (((gamma.mul K).mul Decay).mul (O.add defectV))
    |>.add ((K.mul ExpU).mul (((gamma.sub beta).mul (O.add defectD)).add derivativeD))
    |>.sub (alpha.mul beta)
  return radical.sub linear

/-- An upper bound on the radical yields a lower bound on the comparison once
the regularized multiplier has been certified nonnegative. -/
theorem shortScore_lower_of_upper_root {p : ℕ} (hp : 0 < p) {s t z u v joint root : ℝ}
    {U D H ZV ZD SU SV TV TD WD IU IV K ExpU Decay Joint Radical : Model}
    (hb : InBox s t z) (hu : 0 < u) (huv : u < v)
    (hU : U.Encloses s t z u) (hD : D.Encloses s t z (v - u))
    (hH : H.Encloses s t z (3 / (p : ℝ)))
    (hZV : ZV.Encloses s t z (compactZ p v)) (hZD : ZD.Encloses s t z (compactZ p (v - u)))
    (hSU : SU.Encloses s t z (compactZSlope p (-u))) (hSV : SV.Encloses s t z (compactZSlope p (-v)))
    (hTV : TV.Encloses s t z (compactZSlope p v))
    (hTD : TD.Encloses s t z (compactZSlope p (v - u)))
    (hWD : WD.Encloses s t z (deriv (compactZSlope p) (v - u)))
    (hIU : IU.Encloses s t z (1 / u)) (hIV : IV.Encloses s t z (1 / v))
    (hK : K.Encloses s t z (1 / upperTailGap (3 / (p : ℝ)) u))
    (hE : ExpU.Encloses s t z (Real.exp u))
    (hDecay : Decay.Encloses s t z (Real.exp (-(1 + 3 / (p : ℝ)) * u)))
    (hJ : Joint.Encloses s t z joint)
    (hR : Radical.Encloses s t z root)
    (hRoot : Real.sqrt (compactZ p v * compactZ p (v - u)) ≤ root)
    (hMultiplier : 0 ≤ (shortRootMultiplier D SU SV TV TD WD IU).lower) :
    ((shortScore U D H ZV ZD SU SV TV TD WD IU IV K ExpU Decay Joint Radical).lower : ℝ) /
      scale ≤ compactMixedQ p u v - compactMixedT p u v joint := by
  have hO : (Model.ofRat 1).Encloses s t z 1 := by simpa using Model.ofRat_sound 1 s t z
  have hTwo : (Model.ofRat 2).Encloses s t z 2 := by simpa using Model.ofRat_sound 2 s t z
  have hF : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hQuarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4) := by
    simpa using Model.ofRat_sound (1 / 4) s t z
  have hzero := Model.zero_sound s t z
  have hV : (U.add D).Encloses s t z v := by
    simpa only [add_sub_cancel] using Model.add_sound hU hD
  have hκ := Model.mul_sound hb (Model.add_sound hO hH) hQuarter
  have hAlpha := Model.sub_sound hIU (Model.mul_sound hb hSU hF)
  have hBeta := Model.sub_sound hIV (Model.mul_sound hb hSV hF)
  have hBracket := shortRootMultiplier_sound hb hD hSU hSV hTV hTD hWD hIU
  have hRad := Model.mul_sound hb
    (Model.mul_sound hb (Model.mul_sound hb (Model.sub_sound hzero hκ) hV) hR) hBracket
  have hDefectD := Model.mul_sound hb (Model.mul_sound hb hκ (Model.pow_sound hb hD 2)) hZD
  have hDefectV := Model.mul_sound hb (Model.mul_sound hb hκ (Model.pow_sound hb hV 2)) hZV
  have hDerivativeD := Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hκ hD) hZD)
    (Model.add_sound hTwo (Model.mul_sound hb hD hTD))
  have hGamma := Model.add_sound (Model.add_sound hO hK) hAlpha
  have hLinear := Model.sub_sound
    (Model.add_sound
      (Model.sub_sound (Model.mul_sound hb (Model.mul_sound hb (Model.sub_sound hzero hGamma)
        (Model.sub_sound (Model.add_sound hTwo hH) hBeta)) hJ)
        (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hGamma hK) hDecay)
          (Model.add_sound hO hDefectV)))
      (Model.mul_sound hb (Model.mul_sound hb hK hE)
        (Model.add_sound (Model.mul_sound hb (Model.sub_sound hGamma hBeta) (Model.add_sound hO hDefectD))
          hDerivativeD))) (Model.mul_sound hb hAlpha hBeta)
  have hEncloses :
      (shortScore U D H ZV ZD SU SV TV TD WD IU IV K ExpU Decay Joint Radical).Encloses s t z
        (-compactKappa p * v * root * shortRootMultiplierReal p u v -
          compactMixedT p u v joint) := by
    rw [compactMixedT_eq_cutoff hp hu (hu.trans huv)]
    convert Model.sub_sound hRad hLinear using 1 <;>
      (try dsimp [shortScore, compactKappa]) <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hValue : 0 ≤ shortRootMultiplierReal p u v :=
    (div_nonneg (by exact_mod_cast hMultiplier) scale_real_pos.le).trans
      (Model.lower_sound hb hBracket)
  have hκpos : 0 ≤ compactKappa p := by
    unfold compactKappa
    positivity
  have hWeight := mul_nonneg (mul_nonneg hκpos (hu.trans huv).le) hValue
  refine (Model.lower_sound hb hEncloses).trans ?_
  rw [compactMixedQ_eq_regularized hp hu huv]
  change -compactKappa p * v * root * shortRootMultiplierReal p u v -
      compactMixedT p u v joint ≤ -compactKappa p * v *
        Real.sqrt (compactZ p v * compactZ p (v - u)) * shortRootMultiplierReal p u v -
      compactMixedT p u v joint
  apply sub_le_sub_right
  calc
    _ = -(compactKappa p * v * shortRootMultiplierReal p u v * root) := by ring
    _ ≤ -(compactKappa p * v * shortRootMultiplierReal p u v *
        Real.sqrt (compactZ p v * compactZ p (v - u))) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hRoot hWeight)
    _ = _ := by ring

end RefinedBMV.PositiveCenter.CompactTaylorModel
