/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleAssembly
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Assemble the two enclosing polynomials for the original middle-gap kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleScore

/-! Enclosures of the two endpoint scores, directly in the kernel's coordinates. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open CompactGap
open private rate c X from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
open private quadraticWeight crossDecay crossRate crossProfile crossProfileJet crossDefectJet middleCrossDefect from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel

def middleRadicandModel (G C F Time : Model) : Model :=
  let one := Model.ofRat 1
  let decay := (Model.zero.sub (G.mul Time)).centeredExp
  let decay₂ := ((Model.ofRat (-2)).mul Time).centeredExp
  one.sub (((one.add (G.mul F)).mul decay).add ((C.mul (F.pow 2)).mul decay₂))

theorem middleRadicandModel_sound {G C F Time : Model} {s t z h x : ℝ} (hb : InBox s t z)
    (hg : G.Encloses s t z (3 + h)) (hc : C.Encloses s t z (c h))
    (hf : F.Encloses s t z (upperTailGap h x)) (hx : Time.Encloses s t z x)
    (hE : (Model.zero.sub (G.mul Time)).expChecks)
    (hE₂ : ((Model.ofRat (-2)).mul Time).expChecks) :
    (middleRadicandModel G C F Time).Encloses s t z (X h x) := by
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by
    simpa using Model.ofRat_sound 1 s t z
  have hNegTwo : (Model.ofRat (-2)).Encloses s t z (-2 : ℝ) := by
    simpa using Model.ofRat_sound (-2) s t z
  have hDecay := Model.expChecks_sound hb
    (Model.sub_sound (Model.zero_sound s t z) (Model.mul_sound hb hg hx)) hE
  have hDecay₂ := Model.expChecks_sound hb (Model.mul_sound hb hNegTwo hx) hE₂
  simpa only [middleRadicandModel, X, upperTailLambda, c, zero_sub, neg_mul] using
    Model.sub_sound hOne (Model.add_sound
      (Model.mul_sound hb (Model.add_sound hOne (Model.mul_sound hb hg hf)) hDecay)
      (Model.mul_sound hb (Model.mul_sound hb hc (Model.pow_sound hb hf 2)) hDecay₂))

def middleCrossProfileModels (H G InvFu Eu : Model) : Model × Model :=
  let slope := InvFu.sub H
  let profile := slope.mul ((Model.ofRat 1).sub Eu)
  let derivative := ((G.mul slope).mul Eu).sub (profile.mul InvFu)
  (profile, derivative)

theorem middleCrossProfileModels_sound {H G InvFu Eu : Model} {s t z h u v : ℝ} (hb : InBox s t z)
    (hh : 0 < h) (hu : 0 < u) (hH : H.Encloses s t z h) (hg : G.Encloses s t z (3 + h))
    (hi : InvFu.Encloses s t z (upperTailGap h u)⁻¹) (he : Eu.Encloses s t z (crossDecay h u)) :
    let models := middleCrossProfileModels H G InvFu Eu
    models.1.Encloses s t z (crossProfile h u) ∧
      models.2.Encloses s t z (crossProfileJet h u v).du := by
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by
    simpa using Model.ofRat_sound 1 s t z
  have hslope : (InvFu.sub H).Encloses s t z (upperTailSlope h u) := by
    rw [upperTailSlope_eq_inv_gap_sub_rate hh hu]
    exact Model.sub_sound hi hH
  have hprofile : (middleCrossProfileModels H G InvFu Eu).1.Encloses s t z (crossProfile h u) := by
    exact Model.mul_sound hb hslope (Model.sub_sound hOne he)
  refine ⟨hprofile, ?_⟩
  have hd := Model.sub_sound
    (Model.mul_sound hb (Model.mul_sound hb hg hslope) he) (Model.mul_sound hb hprofile hi)
  convert hd using 1 <;> first | rfl | (simp only [crossProfileJet, crossDecay, div_eq_mul_inv]; ring)

def middleEndpointModels (Weight Upper Lower G K C Fd Fv Id EllD EllV E Q R Eu T T₁
    Alpha Beta Margin : Model) : Model × Model :=
  let defects := middleDefectModels G Fd Fv E Q Eu T
  let parts := middleJetModels Weight Upper Lower G K C Fd Fv Id EllD EllV E Q R Eu T T₁ Alpha Beta
  let cross := (Model.ofRat 1).sub (Weight.mul defects.2.2)
  middleScoreModels Upper Lower Weight defects.1 defects.2.1 defects.2.2 parts.1 cross
    parts.2.1 parts.2.2 Margin

/-- The two model enclosures use the exact endpoint tests of the original mixed derivative. -/
theorem middleEndpointModels_sound {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (huv : u < v) {s t z e q r α β μ : ℝ} (hb : InBox s t z)
    {Weight Upper Lower G K C Fd Fv Id EllD EllV E Q R Eu T T₁ Alpha Beta Margin : Model} :
    let h := rate p
    let d := v - u
    let w := quadraticWeight h d
    Weight.Encloses s t z w →
    Upper.Encloses s t z (X h v) →
    Lower.Encloses s t z (X h d) →
    G.Encloses s t z (3 + h) →
    K.Encloses s t z (3 + 2 * h) →
    C.Encloses s t z (c h) →
    Fd.Encloses s t z (upperTailGap h d) →
    Fv.Encloses s t z (upperTailGap h v) →
    Id.Encloses s t z (upperTailGap h d)⁻¹ →
    EllD.Encloses s t z (upperTailSlope h d) →
    EllV.Encloses s t z (upperTailSlope h v) →
    E.Encloses s t z e →
    Q.Encloses s t z q →
    R.Encloses s t z r →
    Eu.Encloses s t z (crossDecay h u) →
    T.Encloses s t z (crossProfile h u) →
    T₁.Encloses s t z (crossProfileJet h u v).du →
    Alpha.Encloses s t z α →
    Beta.Encloses s t z β →
    Margin.Encloses s t z μ →
    w * e = crossDecay h d →
    w * q = quadraticWeight h v →
    w * r = (leftStripWeight h u v)⁻¹ →
    let models := middleEndpointModels Weight Upper Lower G K C Fd Fv Id EllD EllV E Q R Eu
      T T₁ Alpha Beta Margin
    models.1.Encloses s t z (middleEndpointScores p u v α β μ).1 ∧
      models.2.Encloses s t z (middleEndpointScores p u v α β μ).2 := by
  dsimp only
  intro hw hx hy hg hk hc hd hv hid hld hlv he hq hr heu ht ht₁ hα hβ hμ heq hqq hrq
  let h := rate p
  let d := v - u
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hcurv : profileCurvature h d = upperTailSlope h d * (upperTailGap h d)⁻¹ := by
    unfold profileCurvature
    rw [upperTailSlope_eq_inv_gap_sub_rate hh (sub_pos.mpr huv)]
    ring
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by
    simpa using Model.ofRat_sound 1 s t z
  obtain ⟨hdx, hdy, hdefect⟩ := middleDefectModels_sound hb hg hd hv he hq heu ht
  have hcross : ((Model.ofRat 1).sub (Weight.mul
        (middleDefectModels G Fd Fv E Q Eu T).2.2)).Encloses s t z
      (1 - quadraticWeight h d * (e * (1 + upperTailGap h d * crossProfile h u))) :=
    Model.sub_sound hOne (Model.mul_sound hb hw hdefect)
  have hcrossValue : 1 - quadraticWeight h d * (e * (1 + upperTailGap h d * crossProfile h u)) =
      (crossDefectJet h u v).value := by
    rw [← mul_assoc, heq, ← middleCrossDefect]
    ring
  rw [hcrossValue] at hcross
  obtain ⟨hj, hm, hradical⟩ :=
    middleJetModels_sound hb hw hx hy hg hk hc hd hv hid hld hlv he hq hr heu ht ht₁ hα hβ
  have hmodels := middleScoreModels_sound hb hx hy hw hdx hdy hdefect hj hcross hm hradical hμ
  rw [middleEndpointScores_eq_replay p u v α β μ heq hqq hrq]
  dsimp only [h, d] at hcurv
  simpa only [middleEndpointModels, profileSlope, hcurv, h, d, crossRate, crossDecay] using hmodels

/-- The zero-margin endpoint models after clearing the upper gap inverse.
The upper model also omits the outer quadratic weight. -/
def middleClearedEndpointModels (H Weight Upper Lower G K C Fd Fv Id EllD E Q R Eu T T₁
    Alpha Beta : Model) : Model × Model :=
  let defects := middleDefectModels G Fd Fv E Q Eu T
  let parts := middleClearedJetModels H Weight Upper Lower G K C Fd Fv Id EllD E Q R Eu
    T T₁ Alpha Beta
  let cross := (Model.ofRat 1).sub (Weight.mul defects.2.2)
  middleScoreCoreModels Upper Lower Weight defects.1 defects.2.1 defects.2.2 parts.1 cross
    parts.2.1 parts.2.2

/-- The cleared models enclose the rescaled zero-margin scores of the exact
kernel. The upper enclosure carries its weight as an equality. -/
theorem middleClearedEndpointModels_sound {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hv₀ : 0 < v) (huv : u < v) {s t z e q r α β : ℝ} (hb : InBox s t z)
    {H Weight Upper Lower G K C Fd Fv Id EllD E Q R Eu T T₁ Alpha Beta : Model} :
    let h := rate p
    let d := v - u
    let w := quadraticWeight h d
    let fv := upperTailGap h v
    H.Encloses s t z h →
    Weight.Encloses s t z w →
    Upper.Encloses s t z (X h v) →
    Lower.Encloses s t z (X h d) →
    G.Encloses s t z (3 + h) →
    K.Encloses s t z (3 + 2 * h) →
    C.Encloses s t z (c h) →
    Fd.Encloses s t z (upperTailGap h d) →
    Fv.Encloses s t z fv →
    Id.Encloses s t z (upperTailGap h d)⁻¹ →
    EllD.Encloses s t z (upperTailSlope h d) →
    E.Encloses s t z e →
    Q.Encloses s t z q →
    R.Encloses s t z r →
    Eu.Encloses s t z (crossDecay h u) →
    T.Encloses s t z (crossProfile h u) →
    T₁.Encloses s t z (crossProfileJet h u v).du →
    Alpha.Encloses s t z α →
    Beta.Encloses s t z β →
    w * e = crossDecay h d →
    w * q = quadraticWeight h v →
    w * r = (leftStripWeight h u v)⁻¹ →
    let models := middleClearedEndpointModels H Weight Upper Lower G K C Fd Fv Id EllD
      E Q R Eu T T₁ Alpha Beta
    models.1.Encloses s t z (fv * (middleEndpointScores p u v α β 0).1) ∧
      ∃ upperScore : ℝ, models.2.Encloses s t z upperScore ∧
        w * upperScore = fv * (middleEndpointScores p u v α β 0).2 := by
  dsimp only
  intro hH hw hx hy hg hk hc hd hv hid hld he hq hr heu ht ht₁ hα hβ heq hqq hrq
  let h := rate p
  let d := v - u
  let fv := upperTailGap h v
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hcurv : profileCurvature h d = upperTailSlope h d * (upperTailGap h d)⁻¹ := by
    unfold profileCurvature
    rw [upperTailSlope_eq_inv_gap_sub_rate hh (sub_pos.mpr huv)]
    ring
  have hSlope : fv * (1 - upperTailSlope h v) = (1 + h) * fv - 1 := by
    change upperTailGap h v * (1 - upperTailSlope h v) = _
    rw [mul_comm (upperTailGap h v), upperTailSlope_eq_inv_gap_sub_rate hh hv₀,
      sub_mul, sub_mul, inv_mul_cancel₀ (tail_gap_pos hh hv₀).ne']
    dsimp only [fv]
    ring
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by
    simpa using Model.ofRat_sound 1 s t z
  obtain ⟨hdx, hdy, hdefect⟩ := middleDefectModels_sound hb hg hd hv he hq heu ht
  have hcross : ((Model.ofRat 1).sub (Weight.mul
        (middleDefectModels G Fd Fv E Q Eu T).2.2)).Encloses s t z
      (1 - quadraticWeight h d * (e * (1 + upperTailGap h d * crossProfile h u))) :=
    Model.sub_sound hOne (Model.mul_sound hb hw hdefect)
  have hcrossValue : 1 - quadraticWeight h d * (e * (1 + upperTailGap h d * crossProfile h u)) =
      (crossDefectJet h u v).value := by
    rw [← mul_assoc, heq, ← middleCrossDefect]
    ring
  rw [hcrossValue] at hcross
  obtain ⟨hj, hm, hradical⟩ :=
    middleClearedJetModels_sound hb hH hw hx hy hg hk hc hd hv hid hld he hq hr heu ht ht₁
      hα hβ hSlope
  obtain ⟨hzero, hupper⟩ := middleScoreCoreModels_sound (factor := fv) hb hx hy hw
    hdx hdy hdefect hj hcross hm hradical
  rw [middleEndpointScores_eq_replay p u v α β 0 heq hqq hrq]
  dsimp only [h, d] at hcurv
  simp only [profileSlope, hcurv, crossRate, crossDecay, mul_zero, add_zero]
  exact ⟨hzero, _, hupper, mul_left_comm _ _ _⟩

end RefinedBMV.PositiveCenter.CompactTaylorModel
