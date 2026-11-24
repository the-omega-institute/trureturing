/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleScore
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor enclosures for the two polynomial endpoint scores of the compact middle gap. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

/-! Arithmetic of the two endpoint scores, with their common decay factor kept explicit. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

def middleGapModel (H X : Model) : Model :=
  let half := X.mul (Model.ofRat (-1 / 2))
  let decay := (H.mul half).centeredExp
  ((Model.ofRat 1).add decay).mul (Model.zero.sub (positiveRateGapModel H half))

/-- Halving the argument keeps the regularized exponential quotient in the proven range. -/
theorem middleGapModel_sound {H X : Model} {s t z h x : ℝ} (hb : InBox s t z)
    (hh : H.Encloses s t z h) (hx : X.Encloses s t z x)
    (hh₀ : h ≠ 0) (hx₀ : x ≠ 0)
    (hsize : (H.mul (X.mul (Model.ofRat (-1 / 2)))).argumentRadius ≤ 2)
    (hcheck : (H.mul (X.mul (Model.ofRat (-1 / 2)))).expChecks) :
    (middleGapModel H X).Encloses s t z (upperTailGap h x) := by
  have hHalf : (X.mul (Model.ofRat (-1 / 2))).Encloses s t z (-x / 2) := by
    have hm := Model.mul_sound hb hx (Model.ofRat_sound (-1 / 2) s t z)
    convert hm using 1 <;> norm_num <;> ring
  have hExp := Model.expChecks_sound hb (Model.mul_sound hb hh hHalf) hcheck
  have hGap := positiveRateGapModel_sound hb hh hHalf hh₀
    (div_ne_zero (neg_ne_zero.mpr hx₀) (by norm_num)) hsize
  have hEncloses := Model.mul_sound hb (Model.add_sound (Model.ofRat_sound 1 s t z) hExp)
    (Model.sub_sound (Model.zero_sound s t z) hGap)
  have hEq : (1 + Real.exp (h * (-x / 2))) * (0 - (Real.exp (h * (-x / 2)) - 1) / h) =
      upperTailGap h x := by
    unfold upperTailGap
    have hDouble : Real.exp (-(h * x)) = Real.exp (h * (-x / 2)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hDouble]
    field_simp [hh₀]
    ring
  simpa only [middleGapModel, Rat.cast_one, hEq] using hEncloses

def middleWeightModels (H U D Fd Fv invFd invC : Model) : Model × Model × Model × Model :=
  let one := Model.ofRat 1
  let two := Model.ofRat 2
  let three := Model.ofRat 3
  let half := Model.ofRat (1 / 2)
  let negativeTwo := Model.ofRat (-2)
  let c := ((three.add H).mul (three.add (two.mul H))).mul half
  let uDecay := (Model.zero.sub U).centeredExp
  let dDecay := (negativeTwo.mul D).centeredExp
  let crossDecay := (Model.zero.sub ((one.add H).mul D)).centeredExp
  let ratio := Fv.mul invFd
  ((c.mul (Fd.pow 2)).mul dDecay,
    (crossDecay.mul (invFd.pow 2)).mul invC,
    (uDecay.pow 2).mul (ratio.pow 2), uDecay.mul ratio)

/-- The common weight and the three ratios preserve the small decay factors
in the middle-gap endpoint tests. -/
theorem middleWeightModels_sound {H U D Fd Fv invFd invC : Model}
    {s t z h u d fd fv : ℝ} (hb : InBox s t z)
    (hh : H.Encloses s t z h) (hu : U.Encloses s t z u) (hd : D.Encloses s t z d)
    (hfd : Fd.Encloses s t z fd) (hfv : Fv.Encloses s t z fv)
    (hId : invFd.Encloses s t z fd⁻¹)
    (hIc : invC.Encloses s t z (((3 + h) * (3 + 2 * h) / 2)⁻¹))
    (hEU : (Model.zero.sub U).expChecks) (hED : ((Model.ofRat (-2)).mul D).expChecks)
    (hCross : (Model.zero.sub (((Model.ofRat 1).add H).mul D)).expChecks) :
    let c := (3 + h) * (3 + 2 * h) / 2
    let result := middleWeightModels H U D Fd Fv invFd invC
    result.1.Encloses s t z (c * fd ^ 2 * Real.exp (-(2 * d))) ∧
      result.2.1.Encloses s t z (Real.exp (-((1 + h) * d)) / (c * fd ^ 2)) ∧
      result.2.2.1.Encloses s t z (Real.exp (-(2 * u)) * (fv / fd) ^ 2) ∧
      result.2.2.2.Encloses s t z (Real.exp (-u) * (fv / fd)) := by
  have hZero := Model.zero_sound s t z
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by simpa using Model.ofRat_sound 1 s t z
  have hTwo : (Model.ofRat 2).Encloses s t z (2 : ℝ) := by simpa using Model.ofRat_sound 2 s t z
  have hThree : (Model.ofRat 3).Encloses s t z (3 : ℝ) := by simpa using Model.ofRat_sound 3 s t z
  have hHalf : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hNegTwo : (Model.ofRat (-2)).Encloses s t z (-2 : ℝ) := by
    simpa using Model.ofRat_sound (-2) s t z
  have hc := Model.mul_sound hb
    (Model.mul_sound hb (Model.add_sound hThree hh)
      (Model.add_sound hThree (Model.mul_sound hb hTwo hh))) hHalf
  have heU := Model.expChecks_sound hb (Model.sub_sound hZero hu) hEU
  have heD := Model.expChecks_sound hb (Model.mul_sound hb hNegTwo hd) hED
  have heCross := Model.expChecks_sound hb
    (Model.sub_sound hZero (Model.mul_sound hb (Model.add_sound hOne hh) hd)) hCross
  have hRatio := Model.mul_sound hb hfv hId
  have hExpSq : Real.exp (0 - u) ^ 2 = Real.exp (-(2 * u)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [middleWeightModels, neg_mul, mul_one_div] using
      Model.mul_sound hb (Model.mul_sound hb hc (Model.pow_sound hb hfd 2)) heD
  · simpa only [middleWeightModels, div_eq_mul_inv, mul_inv_rev, inv_pow, zero_sub, mul_assoc] using
      Model.mul_sound hb (Model.mul_sound hb heCross (Model.pow_sound hb hId 2)) hIc
  · simpa only [middleWeightModels, hExpSq, div_eq_mul_inv] using
      Model.mul_sound hb (Model.pow_sound hb heU 2) (Model.pow_sound hb hRatio 2)
  · simpa only [middleWeightModels, zero_sub, div_eq_mul_inv] using Model.mul_sound hb heU hRatio

/-- The two radicand defects and the cross defect share the small gap weight. -/
def middleDefectModels (g Fd Fv e q Eu T : Model) : Model × Model × Model :=
  let one := Model.ofRat 1
  let dx := q.add ((e.mul Eu).mul (one.add (g.mul Fv)))
  let dy := one.add (e.mul (one.add (g.mul Fd)))
  let cross := e.mul (one.add (Fd.mul T))
  (dx, dy, cross)

theorem middleDefectModels_sound {G Fd Fv E Q Eu T : Model}
    {s t z g fd fv e q eu τ : ℝ} (hb : InBox s t z)
    (hg : G.Encloses s t z g) (hfd : Fd.Encloses s t z fd) (hfv : Fv.Encloses s t z fv)
    (he : E.Encloses s t z e) (hq : Q.Encloses s t z q)
    (heu : Eu.Encloses s t z eu) (htau : T.Encloses s t z τ) :
    let models := middleDefectModels G Fd Fv E Q Eu T
    models.1.Encloses s t z (q + e * eu * (1 + g * fv)) ∧
      models.2.1.Encloses s t z (1 + e * (1 + g * fd)) ∧
      models.2.2.Encloses s t z (e * (1 + fd * τ)) := by
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by simpa using Model.ofRat_sound 1 s t z
  exact ⟨Model.add_sound hq (Model.mul_sound hb (Model.mul_sound hb he heu)
    (Model.add_sound hOne (Model.mul_sound hb hg hfv))),
    Model.add_sound hOne (Model.mul_sound hb he (Model.add_sound hOne (Model.mul_sound hb hg hfd))),
    Model.mul_sound hb he (Model.add_sound hOne (Model.mul_sound hb hfd htau))⟩

def middleJetModels (W X Y G K C Fd Fv invFd EllD EllV E Q R Eu T T₁ Alpha Beta : Model) :
    Model × Model × Model :=
  let one := Model.ofRat 1
  let two := Model.ofRat 2
  let dSlope := one.sub EllD
  let vSlope := one.sub EllV
  let u := dSlope.add Alpha
  let v := (vSlope.add dSlope).sub Beta
  let curvature := EllD.mul invFd
  let j := curvature.add (u.mul v)
  let m := (K.mul Fd).sub one
  let a := dSlope.add ((C.mul Fd).mul E)
  let b := (Q.mul vSlope).add (((C.mul Fv).mul E).mul Eu)
  let k := (curvature.sub (two.mul (dSlope.pow 2))).sub ((C.mul E).mul m)
  let wv := E.mul (G.add (m.mul T))
  let wu := (Model.zero.sub E).mul (((Fd.mul T₁).add G).add (m.mul T))
  let wuv := E.mul (((m.mul T₁).add (G.pow 2)).sub ((G.sub (K.mul m)).mul T))
  let main := (((wuv.sub (u.mul wv)).add (v.mul wu)).sub ((Alpha.mul Beta).mul R))
  let radical := ((((k.add ((u.add v).mul a)).mul Y).mul X).add ((u.mul b).mul (Y.pow 2))).add
    ((W.mul a).mul ((b.mul Y).sub (a.mul X)))
  (j, main, radical)

/-- The model bounds the three coefficients of the endpoint polynomial. -/
theorem middleJetModels_sound {W X Y G K C Fd Fv invFd EllD EllV E Q R Eu T T₁ Alpha Beta : Model}
    {s t z w x y g κ c fd fv idf ℓd ℓv e q r eu τ τ₁ α β : ℝ}
    (hb : InBox s t z)
    (hw : W.Encloses s t z w) (hx : X.Encloses s t z x) (hy : Y.Encloses s t z y)
    (hg : G.Encloses s t z g) (hκ : K.Encloses s t z κ) (hc : C.Encloses s t z c)
    (hFd : Fd.Encloses s t z fd) (hFv : Fv.Encloses s t z fv) (hId : invFd.Encloses s t z idf)
    (hld : EllD.Encloses s t z ℓd) (hlv : EllV.Encloses s t z ℓv)
    (he : E.Encloses s t z e) (hq : Q.Encloses s t z q) (hr : R.Encloses s t z r)
    (heu : Eu.Encloses s t z eu) (hτ : T.Encloses s t z τ) (hτ₁ : T₁.Encloses s t z τ₁)
    (hα : Alpha.Encloses s t z α) (hβ : Beta.Encloses s t z β) :
    let dSlope := 1 - ℓd
    let vSlope := 1 - ℓv
    let u := dSlope + α
    let v := vSlope + dSlope - β
    let curvature := ℓd * idf
    let m := κ * fd - 1
    let a := dSlope + c * fd * e
    let b := q * vSlope + c * fv * e * eu
    let k := curvature - 2 * dSlope ^ 2 - c * e * m
    let wv := e * (g + m * τ)
    let wu := -e * (fd * τ₁ + g + m * τ)
    let wuv := e * (m * τ₁ + g ^ 2 - (g - κ * m) * τ)
    let scores := middleJetModels W X Y G K C Fd Fv invFd EllD EllV E Q R Eu T T₁ Alpha Beta
    scores.1.Encloses s t z (curvature + u * v) ∧
      scores.2.1.Encloses s t z (wuv - u * wv + v * wu - α * β * r) ∧
      scores.2.2.Encloses s t z
        ((k + (u + v) * a) * y * x + u * b * y ^ 2 + w * a * (b * y - a * x)) := by
  have hZero := Model.zero_sound s t z
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by simpa using Model.ofRat_sound 1 s t z
  have hTwo : (Model.ofRat 2).Encloses s t z (2 : ℝ) := by simpa using Model.ofRat_sound 2 s t z
  have hD := Model.sub_sound hOne hld
  have hV := Model.sub_sound hOne hlv
  have hu := Model.add_sound hD hα
  have hv := Model.sub_sound (Model.add_sound hV hD) hβ
  have hCurv := Model.mul_sound hb hld hId
  have hm := Model.sub_sound (Model.mul_sound hb hκ hFd) hOne
  have ha := Model.add_sound hD (Model.mul_sound hb (Model.mul_sound hb hc hFd) he)
  have hb' := Model.add_sound (Model.mul_sound hb hq hV)
    (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hc hFv) he) heu)
  have hk := Model.sub_sound (Model.sub_sound hCurv (Model.mul_sound hb hTwo (Model.pow_sound hb hD 2)))
    (Model.mul_sound hb (Model.mul_sound hb hc he) hm)
  have hwv := Model.mul_sound hb he (Model.add_sound hg (Model.mul_sound hb hm hτ))
  have hwu := Model.mul_sound hb (Model.sub_sound hZero he)
    (Model.add_sound (Model.add_sound (Model.mul_sound hb hFd hτ₁) hg) (Model.mul_sound hb hm hτ))
  have hwuv := Model.mul_sound hb he
    (Model.sub_sound (Model.add_sound (Model.mul_sound hb hm hτ₁) (Model.pow_sound hb hg 2))
      (Model.mul_sound hb (Model.sub_sound hg (Model.mul_sound hb hκ hm)) hτ))
  refine ⟨Model.add_sound hCurv (Model.mul_sound hb hu hv), ?_, ?_⟩
  · simpa only [middleJetModels, zero_sub] using
      Model.sub_sound (Model.add_sound (Model.sub_sound hwuv (Model.mul_sound hb hu hwv))
        (Model.mul_sound hb hv hwu)) (Model.mul_sound hb (Model.mul_sound hb hα hβ) hr)
  · exact Model.add_sound
      (Model.add_sound (Model.mul_sound hb (Model.mul_sound hb
          (Model.add_sound hk (Model.mul_sound hb (Model.add_sound hu hv) ha)) hy) hx)
        (Model.mul_sound hb (Model.mul_sound hb hu hb') (Model.pow_sound hb hy 2)))
      (Model.mul_sound hb (Model.mul_sound hb hw ha)
        (Model.sub_sound (Model.mul_sound hb hb' hy) (Model.mul_sound hb ha hx)))

/-- The three jet coefficients multiplied by the upper gap. The cleared
upper slope is evaluated as a polynomial in the gap and the rate. -/
def middleClearedJetModels (H W X Y G K C Fd Fv invFd EllD E Q R Eu T T₁ Alpha Beta : Model) :
    Model × Model × Model :=
  let one := Model.ofRat 1
  let two := Model.ofRat 2
  let dSlope := one.sub EllD
  let vSlope := ((one.add H).mul Fv).sub one
  let u := dSlope.add Alpha
  let v := vSlope.add ((dSlope.sub Beta).mul Fv)
  let curvature := EllD.mul invFd
  let j := (Fv.mul curvature).add (u.mul v)
  let m := (K.mul Fd).sub one
  let a := dSlope.add ((C.mul Fd).mul E)
  let b := (Q.mul vSlope).add ((((C.mul Fv).mul E).mul Eu).mul Fv)
  let k := (curvature.sub (two.mul (dSlope.pow 2))).sub ((C.mul E).mul m)
  let wv := E.mul (G.add (m.mul T))
  let wu := (Model.zero.sub E).mul (((Fd.mul T₁).add G).add (m.mul T))
  let wuv := E.mul (((m.mul T₁).add (G.pow 2)).sub ((G.sub (K.mul m)).mul T))
  let main := (Fv.mul ((wuv.sub (u.mul wv)).sub ((Alpha.mul Beta).mul R))).add (v.mul wu)
  let first := (((Fv.mul (k.add (u.mul a))).add (v.mul a)).mul Y).mul X
  let radical := (first.add ((u.mul b).mul (Y.pow 2))).add
    ((W.mul a).mul ((b.mul Y).sub ((Fv.mul a).mul X)))
  (j, main, radical)

/-- The cleared jet coefficients enclose the original replay coefficients
scaled by the upper gap. The upper slope occurs only in the real identities. -/
theorem middleClearedJetModels_sound
    {H W X Y G K C Fd Fv invFd EllD E Q R Eu T T₁ Alpha Beta : Model}
    {s t z h w x y g κ c fd fv idf ℓd ℓv e q r eu τ τ₁ α β : ℝ}
    (hb : InBox s t z) (hh : H.Encloses s t z h)
    (hw : W.Encloses s t z w) (hx : X.Encloses s t z x) (hy : Y.Encloses s t z y)
    (hg : G.Encloses s t z g) (hκ : K.Encloses s t z κ) (hc : C.Encloses s t z c)
    (hFd : Fd.Encloses s t z fd) (hFv : Fv.Encloses s t z fv) (hId : invFd.Encloses s t z idf)
    (hld : EllD.Encloses s t z ℓd) (he : E.Encloses s t z e)
    (hq : Q.Encloses s t z q) (hr : R.Encloses s t z r)
    (heu : Eu.Encloses s t z eu) (hτ : T.Encloses s t z τ) (hτ₁ : T₁.Encloses s t z τ₁)
    (hα : Alpha.Encloses s t z α) (hβ : Beta.Encloses s t z β)
    (hSlope : fv * (1 - ℓv) = (1 + h) * fv - 1) :
    let dSlope := 1 - ℓd
    let vSlope := 1 - ℓv
    let u := dSlope + α
    let v := vSlope + dSlope - β
    let curvature := ℓd * idf
    let m := κ * fd - 1
    let a := dSlope + c * fd * e
    let b := q * vSlope + c * fv * e * eu
    let k := curvature - 2 * dSlope ^ 2 - c * e * m
    let wv := e * (g + m * τ)
    let wu := -e * (fd * τ₁ + g + m * τ)
    let wuv := e * (m * τ₁ + g ^ 2 - (g - κ * m) * τ)
    let parts := middleClearedJetModels H W X Y G K C Fd Fv invFd EllD E Q R Eu T T₁ Alpha Beta
    parts.1.Encloses s t z (fv * (curvature + u * v)) ∧
      parts.2.1.Encloses s t z (fv * (wuv - u * wv + v * wu - α * β * r)) ∧
      parts.2.2.Encloses s t z
        (fv * ((k + (u + v) * a) * y * x + u * b * y ^ 2 + w * a * (b * y - a * x))) := by
  have hOne : (Model.ofRat 1).Encloses s t z (1 : ℝ) := by simpa using Model.ofRat_sound 1 s t z
  have hTwo : (Model.ofRat 2).Encloses s t z (2 : ℝ) := by simpa using Model.ofRat_sound 2 s t z
  have hD := Model.sub_sound hOne hld
  have hV : ((((Model.ofRat 1).add H).mul Fv).sub (Model.ofRat 1)).Encloses s t z
      (fv * (1 - ℓv)) := by
    rw [hSlope]
    exact Model.sub_sound (Model.mul_sound hb (Model.add_sound hOne hh) hFv) hOne
  have hu := Model.add_sound hD hα
  have hv := Model.add_sound hV (Model.mul_sound hb (Model.sub_sound hD hβ) hFv)
  have hCurv := Model.mul_sound hb hld hId
  have hm := Model.sub_sound (Model.mul_sound hb hκ hFd) hOne
  have ha := Model.add_sound hD (Model.mul_sound hb (Model.mul_sound hb hc hFd) he)
  have hb' := Model.add_sound (Model.mul_sound hb hq hV)
    (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hc hFv) he)
      heu) hFv)
  have hk := Model.sub_sound (Model.sub_sound hCurv (Model.mul_sound hb hTwo (Model.pow_sound hb hD 2)))
    (Model.mul_sound hb (Model.mul_sound hb hc he) hm)
  have hwv := Model.mul_sound hb he (Model.add_sound hg (Model.mul_sound hb hm hτ))
  have hwu := Model.mul_sound hb (Model.sub_sound (Model.zero_sound s t z) he)
    (Model.add_sound (Model.add_sound (Model.mul_sound hb hFd hτ₁) hg) (Model.mul_sound hb hm hτ))
  simp only [zero_sub] at hwu
  have hwuv := Model.mul_sound hb he
    (Model.sub_sound (Model.add_sound (Model.mul_sound hb hm hτ₁) (Model.pow_sound hb hg 2))
      (Model.mul_sound hb (Model.sub_sound hg (Model.mul_sound hb hκ hm)) hτ))
  have hj := Model.add_sound (Model.mul_sound hb hFv hCurv) (Model.mul_sound hb hu hv)
  have hmain := Model.add_sound
    (Model.mul_sound hb hFv (Model.sub_sound (Model.sub_sound hwuv (Model.mul_sound hb hu hwv))
      (Model.mul_sound hb (Model.mul_sound hb hα hβ) hr))) (Model.mul_sound hb hv hwu)
  have hfirst := Model.add_sound
    (Model.mul_sound hb hFv (Model.add_sound hk (Model.mul_sound hb hu ha)))
    (Model.mul_sound hb hv ha)
  have hradical := Model.add_sound
    (Model.add_sound (Model.mul_sound hb (Model.mul_sound hb hfirst hy) hx)
      (Model.mul_sound hb (Model.mul_sound hb hu hb') (Model.pow_sound hb hy 2)))
    (Model.mul_sound hb (Model.mul_sound hb hw ha)
      (Model.sub_sound (Model.mul_sound hb hb' hy)
        (Model.mul_sound hb (Model.mul_sound hb hFv ha) hx)))
  dsimp only [middleClearedJetModels]
  refine ⟨?_, ?_, ?_⟩
  · convert hj using 1 <;> first | rfl | ring
  · convert hmain using 1 <;> first | rfl | ring
  · convert hradical using 1 <;> first | rfl | ring

/-- The zero-margin test and the upper test with its outer gap weight removed. -/
def middleScoreCoreModels (X Y W DX DY E J C M R : Model) : Model × Model :=
  let half := Model.ofRat (1 / 2)
  let quarter := Model.ofRat (1 / 4)
  let sum := X.add Y
  let denominator := (Y.pow 2).mul X
  let correction := (W.mul ((DY.sub DX).pow 2)).mul quarter
  let majorant := ((sum.pow 2).mul half).sub (W.mul correction)
  let offset := ((E.sub ((DX.add DY).mul half)).mul sum).sub correction
  let zeroScore := (W.mul M).sub (J.mul C)
  let upperScore := (denominator.mul ((sum.mul M).add (offset.mul J))).add (majorant.mul R)
  (zeroScore, upperScore)

/-- A common factor in the three coefficients is a common factor in both
zero-margin scores. -/
theorem middleScoreCoreModels_sound {X Y W DX DY E J C M R : Model}
    {s t z x y w δx δy e j c m r factor : ℝ}
    (hb : InBox s t z)
    (hx : X.Encloses s t z x) (hy : Y.Encloses s t z y) (hw : W.Encloses s t z w)
    (hdx : DX.Encloses s t z δx) (hdy : DY.Encloses s t z δy) (he : E.Encloses s t z e)
    (hj : J.Encloses s t z (factor * j)) (hc : C.Encloses s t z c)
    (hm : M.Encloses s t z (factor * m)) (hr : R.Encloses s t z (factor * r)) :
    let S := x + y
    let H := y ^ 2 * x
    let B := (e - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4
    let A := S ^ 2 / 2 - w ^ 2 * (δy - δx) ^ 2 / 4
    let scores := middleScoreCoreModels X Y W DX DY E J C M R
    scores.1.Encloses s t z (factor * (w * m - j * c)) ∧
      scores.2.Encloses s t z (factor * (H * (S * m + B * j) + A * r)) := by
  have hhalf : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hquarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 4) s t z
  have hsum := Model.add_sound hx hy
  have hdenominator := Model.mul_sound hb (Model.pow_sound hb hy 2) hx
  have hcorrection := Model.mul_sound hb
    (Model.mul_sound hb hw (Model.pow_sound hb (Model.sub_sound hdy hdx) 2)) hquarter
  have hmajorant := Model.sub_sound (Model.mul_sound hb (Model.pow_sound hb hsum 2) hhalf)
    (Model.mul_sound hb hw hcorrection)
  have hoffset := Model.sub_sound (Model.mul_sound hb
    (Model.sub_sound he (Model.mul_sound hb (Model.add_sound hdx hdy) hhalf)) hsum) hcorrection
  dsimp only [middleScoreCoreModels]
  refine ⟨?_, ?_⟩
  · convert Model.sub_sound (Model.mul_sound hb hw hm) (Model.mul_sound hb hj hc) using 1
    <;> first | rfl | ring
  · convert Model.add_sound
      (Model.mul_sound hb hdenominator
        (Model.add_sound (Model.mul_sound hb hsum hm) (Model.mul_sound hb hoffset hj)))
      (Model.mul_sound hb hmajorant hr) using 1 <;> first | rfl | ring

def middleScoreModels (X Y W DX DY E J C M R Margin : Model) : Model × Model :=
  let scores := middleScoreCoreModels X Y W DX DY E J C M R
  let sum := X.add Y
  let denominator := (Y.pow 2).mul X
  (scores.1.add Margin, (W.mul scores.2).add ((denominator.mul sum).mul Margin))

/-- Certified elementary inputs enclose both endpoint scores in the same box. -/
theorem middleScoreModels_sound {X Y W DX DY E J C M R Margin : Model}
    {s t z x y w δx δy e j c m r μ : ℝ}
    (hb : InBox s t z)
    (hx : X.Encloses s t z x) (hy : Y.Encloses s t z y) (hw : W.Encloses s t z w)
    (hdx : DX.Encloses s t z δx) (hdy : DY.Encloses s t z δy) (he : E.Encloses s t z e)
    (hj : J.Encloses s t z j) (hc : C.Encloses s t z c)
    (hm : M.Encloses s t z m) (hr : R.Encloses s t z r) (hμ : Margin.Encloses s t z μ) :
    let S := x + y
    let H := y ^ 2 * x
    let B := (e - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4
    let A := S ^ 2 / 2 - w ^ 2 * (δy - δx) ^ 2 / 4
    let scores := middleScoreModels X Y W DX DY E J C M R Margin
    scores.1.Encloses s t z (w * m - j * c + μ) ∧
      scores.2.Encloses s t z (w * (H * (S * m + B * j) + A * r) + H * S * μ) := by
  have hcore := middleScoreCoreModels_sound (J := J) (M := M) (R := R)
    (j := j) (m := m) (r := r) (factor := 1) hb hx hy hw hdx hdy he
    (by simpa only [one_mul] using hj) hc
    (by simpa only [one_mul] using hm) (by simpa only [one_mul] using hr)
  simp only [one_mul] at hcore
  have hdenominator := Model.mul_sound hb (Model.pow_sound hb hy 2) hx
  exact ⟨Model.add_sound hcore.1 hμ, Model.add_sound (Model.mul_sound hb hw hcore.2)
    (Model.mul_sound hb (Model.mul_sound hb hdenominator (Model.add_sound hx hy)) hμ)⟩

end RefinedBMV.PositiveCenter.CompactTaylorModel
