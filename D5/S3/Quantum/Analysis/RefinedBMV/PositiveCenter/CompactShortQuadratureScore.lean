/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureScore
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor model enclosure of the exact refined BMV short-gap score. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortJointLower

/-! The Taylor arithmetic of the short-gap comparison after enclosure of its inputs. -/

namespace RefinedBMV.PositiveCenter

open CompactTaylorModel (Model InBox)

/-- Enclosures entering the arithmetic of the short-gap sign certificate. -/
structure ShortQuadratureScoreInputs where
  lowerCoordinate : Model
  gap : Model
  spacing : Model
  inverseLower : Model
  inverseUpper : Model
  reflectedLowerSlope : Model
  reflectedUpperSlope : Model
  upperSlope : Model
  gapSlope : Model
  gapSecondRatio : Model
  inverseRateGap : Model
  decay : Model
  growth : Model
  joint : Model
  upperMarginal : Model
  gapMarginal : Model
  gapMarginalDeriv : Model
  root : Model

namespace ShortQuadratureScoreInputs

/-- The scaled negative score, with all operations performed on Taylor models. -/
def score (m : ShortQuadratureScoreInputs) : Model :=
  let half := Model.ofRat (1 / 2)
  let quarter := Model.ofRat (1 / 4)
  let one := Model.ofRat 1
  let two := Model.ofRat 2
  let three := Model.ofRat 3
  let v := m.lowerCoordinate.add m.gap
  let J := ((three.add m.spacing).mul (three.add (two.mul m.spacing))).mul half
  let a := m.inverseLower.sub (m.reflectedLowerSlope.mul half)
  let c := m.inverseUpper.sub (m.reflectedUpperSlope.mul half)
  let δ := (m.upperSlope.add m.reflectedUpperSlope).mul half
  let γ := (one.add m.inverseRateGap).add a
  let upperMoment := J.add ((v.mul v).mul m.upperMarginal)
  let gapMoment := J.add ((m.gap.mul m.gap).mul m.gapMarginal)
  let gapMomentDeriv := m.gap.mul ((two.mul m.gapMarginal).add (m.gap.mul m.gapMarginalDeriv))
  let affine := (((Model.zero.sub γ).mul
    (((two.add m.spacing).sub c).mul m.joint |>.add
      ((m.inverseRateGap.mul m.decay).mul upperMoment))).add
    ((m.inverseRateGap.mul m.growth).mul (((γ.sub c).mul gapMoment).add gapMomentDeriv))).sub
    ((J.mul a).mul c)
  let multiplier := ((a.add δ).add m.gapSlope).add (m.gap.mul
    ((((m.gapSecondRatio.mul half).sub ((m.gapSlope.mul m.gapSlope).mul quarter)).add
      (((a.add δ).mul m.gapSlope).mul half)).add (a.mul δ)))
  Model.zero.sub (affine.add ((v.mul m.root).mul multiplier))

set_option maxRecDepth 2048 in
theorem score_sound {m : ShortQuadratureScoreInputs} {p : ℕ} {u v s t z : ℝ}
    (hb : InBox s t z) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (x : ℝ) := (J * compactKappa p) * compactZ p x
    let slope (x : ℝ) := deriv q x / q x
    m.lowerCoordinate.Encloses s t z u →
    m.gap.Encloses s t z d →
    m.spacing.Encloses s t z h →
    m.inverseLower.Encloses s t z (1 / u) →
    m.inverseUpper.Encloses s t z (1 / v) →
    m.reflectedLowerSlope.Encloses s t z (slope (-u)) →
    m.reflectedUpperSlope.Encloses s t z (slope (-v)) →
    m.upperSlope.Encloses s t z (slope v) →
    m.gapSlope.Encloses s t z (slope d) →
    m.gapSecondRatio.Encloses s t z (iteratedDeriv 2 q d / q d) →
    m.inverseRateGap.Encloses s t z (1 / upperTailGap h u) →
    m.decay.Encloses s t z (Real.exp (-(1 + h) * u)) →
    m.growth.Encloses s t z (Real.exp u) →
    m.joint.Encloses s t z (J * shortJointFourthQuadrature h ((u + v) / 2) d) →
    m.upperMarginal.Encloses s t z (q v) →
    m.gapMarginal.Encloses s t z (q d) →
    m.gapMarginalDeriv.Encloses s t z (deriv q d) →
    m.root.Encloses s t z (Real.sqrt (q v * q d)) →
    m.score.Encloses s t z (shortQuadratureNegativeScore p u v) := by
  dsimp only
  intro hu hd hh hiu hiv hsu hsv hsvp hsd h2d hk hdec hg hj hqv hqd hq'd hroot
  have half := Model.ofRat_sound (1 / 2) s t z
  have quarter := Model.ofRat_sound (1 / 4) s t z
  have one := Model.ofRat_sound 1 s t z
  have two := Model.ofRat_sound 2 s t z
  have three := Model.ofRat_sound 3 s t z
  have zero := Model.zero_sound s t z
  have hv : (m.lowerCoordinate.add m.gap).Encloses s t z v := by
    simpa only [add_sub_cancel] using Model.add_sound hu hd
  have hJ := Model.mul_sound hb (Model.mul_sound hb (Model.add_sound three hh)
    (Model.add_sound three (Model.mul_sound hb two hh))) half
  have ha := Model.sub_sound hiu (Model.mul_sound hb hsu half)
  have hc := Model.sub_sound hiv (Model.mul_sound hb hsv half)
  have hδ := Model.mul_sound hb (Model.add_sound hsvp hsv) half
  have hγ := Model.add_sound (Model.add_sound one hk) ha
  have hupperMoment := Model.add_sound hJ (Model.mul_sound hb (Model.mul_sound hb hv hv) hqv)
  have hgapMoment := Model.add_sound hJ (Model.mul_sound hb (Model.mul_sound hb hd hd) hqd)
  have hgapMomentDeriv := Model.mul_sound hb hd (Model.add_sound (Model.mul_sound hb two hqd)
    (Model.mul_sound hb hd hq'd))
  have haffine := Model.sub_sound
    (Model.add_sound
      (Model.mul_sound hb (Model.sub_sound zero hγ)
        (Model.add_sound (Model.mul_sound hb (Model.sub_sound (Model.add_sound two hh) hc) hj)
          (Model.mul_sound hb (Model.mul_sound hb hk hdec) hupperMoment)))
      (Model.mul_sound hb (Model.mul_sound hb hk hg)
        (Model.add_sound (Model.mul_sound hb (Model.sub_sound hγ hc) hgapMoment) hgapMomentDeriv)))
    (Model.mul_sound hb (Model.mul_sound hb hJ ha) hc)
  have hmultiplier := Model.add_sound (Model.add_sound (Model.add_sound ha hδ) hsd)
    (Model.mul_sound hb hd
      (Model.add_sound
        (Model.add_sound
          (Model.sub_sound (Model.mul_sound hb h2d half)
            (Model.mul_sound hb (Model.mul_sound hb hsd hsd) quarter))
          (Model.mul_sound hb (Model.mul_sound hb (Model.add_sound ha hδ) hsd) half))
        (Model.mul_sound hb ha hδ)))
  have hf := Model.sub_sound zero (Model.add_sound haffine
    (Model.mul_sound hb (Model.mul_sound hb hv hroot) hmultiplier))
  convert hf using 1
  · rfl
  · unfold shortQuadratureNegativeScore
    norm_num [div_eq_mul_inv, pow_two]

end ShortQuadratureScoreInputs
end RefinedBMV.PositiveCenter
