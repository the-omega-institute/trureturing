/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Bounds/Slopes
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds from derivatives in the gap and reciprocal degree. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Bounds.Analytic
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Parameter

namespace RefinedBMV.FourSpectrumLift

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open ZeroCenterRectangle

private theorem value_6 {n : ℕ} (x : Fin n → ℝ) : value x (6 : Expr n) = 6 := by
  change ((6 : ℚ) : ℝ) = 6
  norm_num

private def slopeExpr (box : Fin 7 → ℚ × ℚ) : Expr 7 :=
  let v := inputExpr box
  zeroCenterCurvatureSlope (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)

private theorem slopeExpr_value (box : Fin 7 → ℚ × ℚ) (c h : ℝ) :
    value (analyticPoint c h) (slopeExpr box) = zeroCenterCurvatureSlopeAt h c := by
  simp only [slopeExpr, inputExpr, value, zeroCenterCurvatureSlope, zeroCenterCurvatureSlopeAt,
    zeroCenterQuotientCubic, zeroCenterGeometricJet,
    CurvatureCubic.const, CurvatureCubic.add, CurvatureCubic.sub, CurvatureCubic.scale,
    CurvatureCubic.mul, CurvatureCubic.quot, CurvatureCubic.root, CurvatureCubic.exp,
    CurvatureJet.quot, CurvatureJet.sqrtFrom, CurvatureJet.sub, CurvatureJet.mul,
    CurvatureJet.add, CurvatureJet.scale, CurvatureJet.const, CurvatureJet.exponential,
    value_zero, value_1, value_2, value_3, value_4, value_6, value_9,
    value_add, value_neg, value_sub, value_mul, value_div]
  rfl

private def centerRectangle (b : ZeroCenterRectangle) : ZeroCenterRectangle :=
  let m := (b.cLo + b.cHi)/2
  {b with cLo := m, cHi := m}

def meanValueValid (b : ZeroCenterRectangle) (center whole : Fin 7 → ℚ × ℚ) : Prop :=
  let low := (bounds (curvatureExpr center)).1
  let slope := bounds (slopeExpr whole)
  let M := max |slope.1| |slope.2|
  0 < b.cLo ∧ analyticLeafValid (centerRectangle b) center ∧
    analyticLeafValid b whole ∧ check center (curvatureExpr center) = true ∧
    check whole (slopeExpr whole) = true ∧ M * ((b.cHi-b.cLo)/2) < low

private instance (b : ZeroCenterRectangle) (center whole : Fin 7 → ℚ × ℚ) :
    Decidable (meanValueValid b center whole) := by
  unfold meanValueValid
  infer_instance

theorem meanValue_positive {b : ZeroCenterRectangle} {center whole : Fin 7 → ℚ × ℚ}
    (hb : meanValueValid b center whole) {c h : ℝ} (hm : b.Holds c h) (hh : 0 < h) :
    0 < zeroCenterCurvatureAt h c := by
  rcases hb with ⟨ha, hcenter, hwhole, hcCheck, hsCheck, hsep⟩
  let m := ((b.cLo : ℝ) + b.cHi)/2
  have hcast : (((b.cLo+b.cHi)/2 : ℚ) : ℝ) = m := by simp [m]
  have hct : (centerRectangle b).Holds m h := by
    refine ⟨?_, ?_, hm.2.2.1, hm.2.2.2⟩
    · exact hcast.le
    · exact hcast.ge
  have hcl := checked_expression_encloses center _ (analyticLeaf_sound hcenter hct hh) _ hcCheck
  rw [curvatureExpr_value] at hcl
  let t := bounds (slopeExpr whole)
  let M := max |(t.1 : ℝ)| |(t.2 : ℝ)|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hs (x : ℝ) (hx : x ∈ Set.Icc (b.cLo : ℝ) (b.cHi : ℝ)) :
      |zeroCenterCurvatureSlopeAt h x| ≤ M := by
    have hs' := checked_expression_encloses whole _ (analyticLeaf_sound hwhole
      ⟨hx.1, hx.2, hm.2.2.1, hm.2.2.2⟩ hh) _ hsCheck
    rw [slopeExpr_value] at hs'
    apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hs'.1),
      hs'.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  apply zeroCenterCurvatureAt_pos_of_slope hh (by exact_mod_cast ha) ⟨hm.1, hm.2.1⟩
    hcl.1 hM hs
  have hsepReal := (Rat.cast_lt (K := ℝ)).mpr hsep
  push_cast at hsepReal
  exact hsepReal


private def momentPoint (x : ℚ) : ℚ × ℚ :=
  if x = 0 then (1/2, 1/2) else
    let z := compactExpBounds (-x) (-x)
    ((1-(1+x)*z.2)/x^2, (1-(1+x)*z.1)/x^2)

private theorem momentPoint_sound {x : ℚ} (h₀ : 0 ≤ x) (hx : |x| ≤ 256) :
    ((momentPoint x).1 : ℝ) ≤ zeroCenterFirstMoment (x : ℝ) ∧
      zeroCenterFirstMoment (x : ℝ) ≤ ((momentPoint x).2 : ℝ) := by
  by_cases hz : x = 0
  · subst x
    norm_num [momentPoint, zeroCenterFirstMoment_zero]
  have hn : (x : ℝ) ≠ 0 := by exact_mod_cast hz
  have hpos : 0 ≤ (x : ℝ) := by exact_mod_cast h₀
  have hq : |-x| ≤ 256 := (abs_neg x).trans_le hx
  have hExp := compactExpBounds_sound hq hq
    (show ((-x : ℚ) : ℝ) ≤ -(x : ℝ) ∧ -(x : ℝ) ≤ ((-x : ℚ) : ℝ) by simp)
  rw [zeroCenterFirstMoment_eq hn]
  simp only [momentPoint, ite_eq_right hz, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_add, Rat.cast_one]
  constructor
  · exact div_le_div_of_nonneg_right (sub_le_sub_left
      (mul_le_mul_of_nonneg_left hExp.2 (by positivity)) _) (sq_nonneg _)
  · exact div_le_div_of_nonneg_right (sub_le_sub_left
      (mul_le_mul_of_nonneg_left hExp.1 (by positivity)) _) (sq_nonneg _)

private def momentBox (b : ZeroCenterRectangle) : ℚ × ℚ :=
  let a := argument b 0 3
  ((momentPoint (-a.1)).1, (momentPoint (-a.2)).2)

private theorem momentBox_sound {b : ZeroCenterRectangle} {c h : ℝ}
    (hd : parametersValid b) (hb : b.Holds c h) :
    ((momentBox b).1 : ℝ) ≤ zeroCenterFirstMoment (3*h*c) ∧
      zeroCenterFirstMoment (3*h*c) ≤ ((momentBox b).2 : ℝ) := by
  obtain ⟨hc, hh, hhi, _, _, hargs⟩ := hd
  have hcu : 0 ≤ b.cHi := hc.trans (by exact_mod_cast hb.1.trans hb.2.1)
  have hneg := argument_sound hb hc hh (a := 0) (k := 3) (by norm_num) (by norm_num)
  push_cast at hneg
  simp only [zero_add] at hneg
  have hlo : 0 ≤ -(argument b 0 3).1 := by unfold argument; simp; positivity
  have hup : 0 ≤ -(argument b 0 3).2 := by unfold argument; simp; positivity
  have hab := hargs 0
  have hab₁ : |-(argument b 0 3).1| ≤ 256 := (abs_neg _).trans_le hab.1
  have hab₂ : |-(argument b 0 3).2| ≤ 256 := (abs_neg _).trans_le hab.2
  have hm₁ := (momentPoint_sound hlo hab₁).1
  have hm₂ := (momentPoint_sound hup hab₂).2
  push_cast at hm₁ hm₂
  refine ⟨hm₁.trans (zeroCenterFirstMoment_anti ?_), (zeroCenterFirstMoment_anti ?_).trans hm₂⟩
  · linarith [hneg.1]
  · linarith [hneg.2]

private def parameterInputBox (b : ZeroCenterRectangle) (whole : Fin 7 → ℚ × ℚ)
    (moment : ℚ × ℚ) : Fin 9 → ℚ × ℚ :=
  Fin.append whole ![(b.cLo,b.cHi), moment]

private noncomputable def parameterPoint (c h : ℝ) : Fin 9 → ℝ :=
  Fin.append (analyticPoint c h) ![c,zeroCenterFirstMoment (3*h*c)]

private def parameterSlopeExpr (box : Fin 9 → ℚ × ℚ) : Expr 9 :=
  let v := inputExpr box
  zeroCenterParameterSlopeFrom (v 7) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 8)

private theorem tangent_add_value {R : Type} [Add R] (a b : ParameterTangent R) :
    (a+b).value = a.value+b.value := rfl

private theorem tangent_add_deriv {R : Type} [Add R] (a b : ParameterTangent R) :
    (a+b).deriv = a.deriv+b.deriv := rfl

private theorem tangent_sub_value {R : Type} [Sub R] (a b : ParameterTangent R) :
    (a-b).value = a.value-b.value := rfl

private theorem tangent_sub_deriv {R : Type} [Sub R] (a b : ParameterTangent R) :
    (a-b).deriv = a.deriv-b.deriv := rfl

private theorem tangent_mul_value {R : Type} [Add R] [Mul R] (a b : ParameterTangent R) :
    (a*b).value = a.value*b.value := rfl

private theorem tangent_mul_deriv {R : Type} [Add R] [Mul R] (a b : ParameterTangent R) :
    (a*b).deriv = a.deriv*b.value+a.value*b.deriv := rfl

private theorem tangent_div_value {R : Type} [Sub R] [Mul R] [Div R] (a b : ParameterTangent R) :
    (a/b).value = a.value/b.value := rfl

private theorem tangent_div_deriv {R : Type} [Sub R] [Mul R] [Div R] (a b : ParameterTangent R) :
    (a/b).deriv = (a.deriv-(a.value/b.value)*b.deriv)/b.value := rfl

private theorem tangent_nat_value {R : Type} [Zero R] {k : ℕ} [OfNat R k] :
    (OfNat.ofNat k : ParameterTangent R).value = OfNat.ofNat k := rfl

private theorem tangent_neg_value {R : Type} [Neg R] (a : ParameterTangent R) :
    (-a).value = -a.value := rfl

private theorem tangent_zero_value {R : Type} [Zero R] :
    (0 : ParameterTangent R).value = 0 := rfl

private theorem tangent_nat_deriv {R : Type} [Zero R] {k : ℕ} [OfNat R k] :
    (OfNat.ofNat k : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_neg_deriv {R : Type} [Neg R] (a : ParameterTangent R) :
    (-a).deriv = -a.deriv := rfl

private theorem tangent_zero_deriv {R : Type} [Zero R] :
    (0 : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_1_value {R : Type} [Zero R] [OfNat R 1] :
    (1 : ParameterTangent R).value = 1 := rfl

private theorem tangent_1_deriv {R : Type} [Zero R] [OfNat R 1] :
    (1 : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_2_value {R : Type} [Zero R] [OfNat R 2] :
    (2 : ParameterTangent R).value = 2 := rfl

private theorem tangent_2_deriv {R : Type} [Zero R] [OfNat R 2] :
    (2 : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_3_value {R : Type} [Zero R] [OfNat R 3] :
    (3 : ParameterTangent R).value = 3 := rfl

private theorem tangent_3_deriv {R : Type} [Zero R] [OfNat R 3] :
    (3 : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_4_value {R : Type} [Zero R] [OfNat R 4] :
    (4 : ParameterTangent R).value = 4 := rfl

private theorem tangent_4_deriv {R : Type} [Zero R] [OfNat R 4] :
    (4 : ParameterTangent R).deriv = 0 := rfl

private theorem tangent_9_value {R : Type} [Zero R] [OfNat R 9] :
    (9 : ParameterTangent R).value = 9 := rfl

private theorem tangent_9_deriv {R : Type} [Zero R] [OfNat R 9] :
    (9 : ParameterTangent R).deriv = 0 := rfl

private theorem parameterSlopeExpr_value (box : Fin 9 → ℚ × ℚ) {c h : ℝ} (hh : 0 < h) :
    value (parameterPoint c h) (parameterSlopeExpr box) = zeroCenterCurvatureParameterSlope c h := by
  rw [zeroCenterCurvatureParameterSlope_eq hh]
  simp only [parameterSlopeExpr, inputExpr, value, zeroCenterParameterSlopeFrom,
    zeroCenterCurvature, zeroCenterQuotientJet, zeroCenterRadicandJet, zeroCenterAB, zeroCenterV,
    zeroCenterGeometricJet, CurvatureJet.quot, CurvatureJet.sqrtFrom, CurvatureJet.sub,
    CurvatureJet.mul, CurvatureJet.add, CurvatureJet.scale, CurvatureJet.const,
    CurvatureJet.exponential, ParameterTangent.sqrtFrom, ParameterTangent.constant,
    tangent_add_value, tangent_add_deriv, tangent_sub_value, tangent_sub_deriv,
    tangent_mul_value, tangent_mul_deriv, tangent_div_value, tangent_div_deriv,
    tangent_1_value, tangent_1_deriv, tangent_2_value, tangent_2_deriv,
    tangent_3_value, tangent_3_deriv, tangent_4_value, tangent_4_deriv,
    tangent_9_value, tangent_9_deriv, tangent_neg_value, tangent_neg_deriv,
    tangent_zero_value, tangent_zero_deriv, value_zero, value_1, value_2, value_3, value_4,
    value_9, value_add, value_sub, value_mul, value_div, value_neg]
  rfl

private def centerPointRectangle (b : ZeroCenterRectangle) : ZeroCenterRectangle :=
  let cm := (b.cLo+b.cHi)/2
  let hm := (b.hLo+b.hHi)/2
  ⟨cm,cm,hm,hm⟩

def twoSlopeValid (b : ZeroCenterRectangle) (center whole : Fin 7 → ℚ × ℚ)
    (moment : ℚ × ℚ) : Prop :=
  let low := (bounds (curvatureExpr center)).1
  let sc := bounds (slopeExpr whole)
  let hp := parameterInputBox b whole moment
  let sh := bounds (parameterSlopeExpr hp)
  let Mc := max |sc.1| |sc.2|
  let Mh := max |sh.1| |sh.2|
  0 < b.cLo ∧ analyticLeafValid (centerPointRectangle b) center ∧ analyticLeafValid b whole ∧
    moment.1 ≤ (momentBox b).1 ∧ (momentBox b).2 ≤ moment.2 ∧
    check center (curvatureExpr center) = true ∧
    check whole (slopeExpr whole) = true ∧
    check hp (parameterSlopeExpr hp) = true ∧
    Mc*((b.cHi-b.cLo)/2) + Mh*((b.hHi-b.hLo)/2) < low

private instance (b : ZeroCenterRectangle) (center whole : Fin 7 → ℚ × ℚ)
    (moment : ℚ × ℚ) : Decidable (twoSlopeValid b center whole moment) := by
  unfold twoSlopeValid
  infer_instance

private theorem abs_le_bound_of_mem {v a b : ℝ} (h : a ≤ v ∧ v ≤ b) :
    |v| ≤ max |a| |b| :=
  abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans h.1),
    h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

theorem twoSlope_positive {b : ZeroCenterRectangle} {center whole : Fin 7 → ℚ × ℚ}
    {moment : ℚ × ℚ} (hb : twoSlopeValid b center whole moment)
    {c h : ℝ} (hx : b.Holds c h) (hh : 0 < h) : 0 < zeroCenterCurvatureAt h c := by
  rcases hb with ⟨ha, hcenter, hwhole, hml, hmu, hcheck, hcCheck, hpCheck, hsep⟩
  have hd : 0 ≤ (b.hLo : ℝ) := by exact_mod_cast hwhole.1.2.1
  let cm := ((b.cLo : ℝ)+b.cHi)/2
  let hm := ((b.hLo : ℝ)+b.hHi)/2
  have hcm : cm ∈ Set.Icc (b.cLo : ℝ) (b.cHi : ℝ) :=
    ⟨by dsimp [cm]; linarith [hx.1,hx.2.1], by dsimp [cm]; linarith [hx.1,hx.2.1]⟩
  have hhm : 0 < hm := by
    have hhi := hh.trans_le hx.2.2.2
    dsimp [hm]
    linarith
  have hct : (centerPointRectangle b).Holds cm hm := by
    simp [centerPointRectangle, Holds, cm, hm]
  have hlo := checked_expression_encloses center _ (analyticLeaf_sound hcenter hct hhm) _ hcheck
  rw [curvatureExpr_value] at hlo
  let sc := bounds (slopeExpr whole)
  let hBox := parameterInputBox b whole moment
  let sh := bounds (parameterSlopeExpr hBox)
  let Mc := max |(sc.1 : ℝ)| |(sc.2 : ℝ)|
  let Mh := max |(sh.1 : ℝ)| |(sh.2 : ℝ)|
  have hMc : 0 ≤ Mc := (abs_nonneg _).trans (le_max_left _ _)
  have hMh : 0 ≤ Mh := (abs_nonneg _).trans (le_max_left _ _)
  have hcs (y : ℝ) (hy : y ∈ Set.Icc (b.cLo : ℝ) (b.cHi : ℝ)) :
      |zeroCenterCurvatureSlopeAt h y| ≤ Mc := by
    have he := checked_expression_encloses whole _ (analyticLeaf_sound hwhole
      ⟨hy.1, hy.2, hx.2.2.1, hx.2.2.2⟩ hh) _ hcCheck
    rw [slopeExpr_value] at he
    exact abs_le_bound_of_mem he
  have hhs (y : ℝ) (hy : y ∈ Set.Icc (b.hLo : ℝ) (b.hHi : ℝ)) (hy₀ : 0 < y) :
      |zeroCenterCurvatureParameterSlope cm y| ≤ Mh := by
    have hrect : b.Holds cm y := ⟨hcm.1, hcm.2, hy.1, hy.2⟩
    have hb₀ := analyticLeaf_sound hwhole hrect hy₀
    have hb₁ := momentBox_sound hwhole.1 hrect
    have hin (i : Fin 9) :
        ((hBox i).1 : ℝ) ≤ parameterPoint cm y i ∧
          parameterPoint cm y i ≤ ((hBox i).2 : ℝ) := by
      fin_cases i
      · exact hb₀ 0
      · exact hb₀ 1
      · exact hb₀ 2
      · exact hb₀ 3
      · exact hb₀ 4
      · exact hb₀ 5
      · exact hb₀ 6
      · exact hcm
      · exact ⟨((Rat.cast_le (K := ℝ)).mpr hml).trans hb₁.1,
          hb₁.2.trans ((Rat.cast_le (K := ℝ)).mpr hmu)⟩
    have he := checked_expression_encloses hBox (parameterPoint cm y) hin _ hpCheck
    rw [parameterSlopeExpr_value _ hy₀] at he
    exact abs_le_bound_of_mem he
  apply zeroCenterCurvatureAt_pos_of_two_slopes (by exact_mod_cast ha) hh ⟨hx.1,hx.2.1⟩
    ⟨hx.2.2.1,hx.2.2.2⟩ hd hlo.1 hMc hMh hcs hhs
  have hsepReal := (Rat.cast_lt (K := ℝ)).mpr hsep
  push_cast at hsepReal
  exact hsepReal

theorem transferTwoSlope {r s : ZeroCenterRectangle}
    {center whole : Fin 7 → ℚ × ℚ} {moment : ℚ × ℚ} (h : twoSlopeValid r center whole moment)
    (he : r = s) : twoSlopeValid s center whole moment := he ▸ h

end RefinedBMV.FourSpectrumLift
