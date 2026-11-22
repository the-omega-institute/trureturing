/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Bounds/Near
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regularized series and radical bounds at gaps up to one. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Bounds.Analytic
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Near

namespace RefinedBMV.FourSpectrumLift

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

private def nearEvenMomentExpr {box : Fin 9 → ℚ × ℚ}
    (c h : IntervalExpr box) : IntervalExpr box :=
  let Q := intervalConstant (box := box)
  let h₂ := h*h
  let h₃ := h₂*h
  let h₄ := h₂*h₂
  let h₅ := h₄*h
  let h₆ := h₃*h₃
  let m₂ := Q (3/4) * (1 + 2*h)
  let m₄ := Q (27/80) * (1 + 2*h) * (3 + 6*h - 4*h₂)
  let m₆ := Q (243/448) * (1 + 2*h) * (3 + 12*h - 24*h₃ + 16*h₄)
  let m₈ := Q (729/1280) * (1 + 2*h) *
    (5 + 30*h + 20*h₂ - 120*h₃ - 16*h₄ + 288*h₅ - 192*h₆)
  let c₂ := c*c
  m₂ + c₂*(m₄/2 + c₂*(m₆*Q (1/24) + c₂*m₈*Q (1/720)))

private theorem nearEvenMomentExpr_value {box : Fin 9 → ℚ × ℚ}
    (x : Fin 9 → ℝ) (c h : IntervalExpr box) :
    intervalValue x (nearEvenMomentExpr c h) =
      zeroCenterEvenMomentLower (intervalValue x c) (intervalValue x h) := by
  have hc (q : ℚ) : intervalValue x (intervalConstant (box := box) q) = (q : ℝ) := rfl
  have hnat (k : ℕ) : intervalValue x (OfNat.ofNat k : IntervalExpr box) = ((k : ℕ) : ℝ) := by
    change ((k : ℚ) : ℝ) = (k : ℝ)
    exact Rat.cast_natCast _
  simp only [nearEvenMomentExpr, zeroCenterEvenMomentLower, hc, hnat, value_add, value_sub,
    value_mul, value_div]
  norm_num
  ring

private def nearRadicandExpr (box : Fin 9 → ℚ × ℚ) : IntervalExpr box :=
  let v := inputExpr box
  intervalConstant 27 * (1 + v 1) * (1 + 2*v 1) * (1 + 3*v 1) * v 2

private def nearLowerExpr (box : Fin 9 → ℚ × ℚ) : IntervalExpr box :=
  let v := inputExpr box
  let c := v 0
  let h := v 1
  let M := intervalConstant 27 * (1+h) * (1+2*h) * (1+3*h)
  let rad := CurvatureJet.scale M (⟨v 2,v 3,v 4/2⟩ : CurvatureJet (IntervalExpr box))
  let k := 3*h
  let den := CurvatureJet.scale (3*(1+h)) (⟨v 5,k*v 6,k*k*v 7/2⟩ : CurvatureJet (IntervalExpr box))
  let V := CurvatureJet.quot (CurvatureJet.sqrtFrom rad (v 8)) den
  nearEvenMomentExpr c h - (2*V.first + 2*c*V.second)

private noncomputable def nearPoint (c h : ℝ) : Fin 9 → ℝ :=
  let t := 3*h*c
  let B := zeroCenterRegularizingDerivative h 0 c
  ![c, h, B, zeroCenterRegularizingDerivative h 1 c, zeroCenterRegularizingDerivative h 2 c,
    phi t, deriv phi t, deriv (deriv phi) t, Real.sqrt (27*(1+h)*(1+2*h)*(1+3*h)*B)]

private theorem nearLowerExpr_value (box : Fin 9 → ℚ × ℚ) (c h : ℝ) :
    intervalValue (nearPoint c h) (nearLowerExpr box) =
      zeroCenterNearExpression c h
        (nearPoint c h 2) (nearPoint c h 3) (nearPoint c h 4)
        (nearPoint c h 5) (nearPoint c h 6) (nearPoint c h 7) (nearPoint c h 8) := by
  have hc (q : ℚ) : intervalValue (nearPoint c h) (intervalConstant (box := box) q) = (q : ℝ) := rfl
  simp only [nearLowerExpr, intervalValue_input, zeroCenterNearExpression, CurvatureJet.quot,
    CurvatureJet.sqrtFrom, CurvatureJet.scale, nearEvenMomentExpr_value,
    value_add, value_sub, value_mul, value_div, value_1, value_2, value_3, hc]
  norm_num
  have hk : (3*(nearPoint c h 1))*(3*(nearPoint c h 1)) = (3*(nearPoint c h 1))^2 := by ring
  simp only [hk]
  rfl

private def nearSeriesBoxes (b : ZeroCenterRectangle) : Fin 6 → ℚ × ℚ :=
  let Tlo := regularizingEndpointTable b.hLo
  let Thi := regularizingEndpointTable b.hHi
  let r k := (endpointPartial Tlo b.cLo k, endpointPartial Thi b.cHi k + (2 : ℚ)⁻¹ ^ 100)
  let p k := (phiPartialRat (3*b.hLo*b.cLo) k,
    phiPartialRat (3*b.hHi*b.cHi) k + 1/(2 : ℚ)^128)
  ![r 0, r 1, r 2, p 0, p 1, p 2]

private def nearAdmissible (b : ZeroCenterRectangle) : Prop :=
  0 ≤ b.cLo ∧ b.cHi ≤ 1 ∧ 0 ≤ b.hLo ∧ b.hHi ≤ 3/32

private instance (b : ZeroCenterRectangle) : Decidable (nearAdmissible b) := by
  unfold nearAdmissible
  infer_instance

private def nearInputsValid (b : ZeroCenterRectangle) (box : Fin 9 → ℚ × ℚ) : Prop :=
  (box 0).1 ≤ b.cLo ∧ b.cHi ≤ (box 0).2 ∧
  (box 1).1 ≤ b.hLo ∧ b.hHi ≤ (box 1).2 ∧
    ∀ i : Fin 6, (box ⟨i.val+2, by omega⟩).1 ≤ (nearSeriesBoxes b i).1 ∧
      (nearSeriesBoxes b i).2 ≤ (box ⟨i.val+2, by omega⟩).2

private instance (b : ZeroCenterRectangle) (box : Fin 9 → ℚ × ℚ) :
    Decidable (nearInputsValid b box) := by
  unfold nearInputsValid
  infer_instance

private theorem nearSeriesBoxes_sound {b : ZeroCenterRectangle} (hd : nearAdmissible b)
    {c h : ℝ} (hb : b.Holds c h) (hc : 0 < c) (hh : 0 < h) :
    ∀ i : Fin 6, ((nearSeriesBoxes b i).1 : ℝ) ≤ nearPoint c h ⟨i.val+2, by omega⟩ ∧
      nearPoint c h ⟨i.val+2, by omega⟩ ≤ ((nearSeriesBoxes b i).2 : ℝ) := by
  have hc₀ : 0 ≤ (b.cLo : ℝ) := by exact_mod_cast hd.1
  have hc₁ : c ≤ 1 := hb.2.1.trans (by exact_mod_cast hd.2.1)
  have hh₀ : 0 ≤ (b.hLo : ℝ) := by exact_mod_cast hd.2.2.1
  have hdhi := (Rat.cast_le (K := ℝ)).mpr hd.2.2.2
  push_cast at hdhi
  have hh₁ : h ≤ 3/32 := hb.2.2.2.trans hdhi
  have h₁ : h ≤ 1 := by linarith
  have hT {k : ℕ} (hk : k ≤ 2) := regularizingDerivative_enclosed
    (regularizingEndpointTable b.hLo) (regularizingEndpointTable b.hHi) hh₀
    hb.2.2.1 hb.2.2.2 h₁ hc₀ hb.1 hb.2.1 hc₁ hk
  have hxh : 0 < 3*h*c := by positivity
  have hmax : 3*h*c ≤ 9/32 := by
    calc
      _ ≤ (3 : ℝ)*(3/32)*1 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hh₁ (by norm_num)) hc₁ hc.le (by norm_num)
      _ = _ := by norm_num
  have hlo : ((3*b.hLo*b.cLo : ℚ) : ℝ) ≤ 3*h*c := by
    push_cast
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb.2.2.1 (by norm_num)) hb.1 hc₀ (by positivity)
  have hhi : 3*h*c ≤ ((3*b.hHi*b.cHi : ℚ) : ℝ) := by
    push_cast
    have hhi' : 0 ≤ (b.hHi : ℝ) := hh.le.trans hb.2.2.2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb.2.2.2 (by norm_num)) hb.2.1 hc.le (by positivity)
  have hP := phi_enclosed (by push_cast; positivity) hlo hhi hxh hmax
  intro i
  fin_cases i
  · exact hT (k := 0) (by decide)
  · exact hT (k := 1) (by decide)
  · exact hT (k := 2) (by decide)
  · exact hP 0
  · exact hP 1
  · exact hP 2

def nearValid (b : ZeroCenterRectangle) (box : Fin 9 → ℚ × ℚ) : Prop :=
  let root := box 8
  let rad := nearRadicandExpr box
  nearAdmissible b ∧ nearInputsValid b box ∧ rad.guards = true ∧
    root.1 ≤ root.2 ∧ 0 ≤ root.1 ∧ 0 ≤ root.2 ∧ root.1^2 ≤ (intervalBounds rad).1 ∧
    (intervalBounds rad).2 ≤ root.2^2 ∧ (nearLowerExpr box).guards = true ∧
      0 < (intervalBounds (nearLowerExpr box)).1

private instance (b : ZeroCenterRectangle) (box : Fin 9 → ℚ × ℚ) :
    Decidable (nearValid b box) := by
  unfold nearValid
  infer_instance

theorem near_positive {b : ZeroCenterRectangle} {box : Fin 9 → ℚ × ℚ}
    (hd : nearValid b box) {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c)
    (hb : b.Holds c (1 / (p : ℝ))) : 0 < deriv^[2] (zeroProfile p) c := by
  let h : ℝ := 1 / p
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  rcases hd with ⟨hcBox, ⟨hcl,hcu,hhl,hhu,ht⟩, hrCheck, hru, hr₀, hr₁,
    hrl, hrh, hCheck, hpos⟩
  have hc₁ : c < 2 := (hb.2.1.trans (by exact_mod_cast hcBox.2.1 : (b.cHi : ℝ) ≤ 1)).trans_lt
    (by norm_num)
  have hseries := nearSeriesBoxes_sound hcBox hb hc hh
  have ht' (i : Fin 6) :
      let j : Fin 9 := ⟨i.val+2, by omega⟩
      ((box j).1 : ℝ) ≤ nearPoint c h j ∧ nearPoint c h j ≤ ((box j).2 : ℝ) :=
    ⟨((Rat.cast_le (K := ℝ)).mpr (ht i).1).trans (hseries i).1,
      (hseries i).2.trans ((Rat.cast_le (K := ℝ)).mpr (ht i).2)⟩
  have hin (r : ℝ) (hr : ((box 8).1 : ℝ) ≤ r ∧ r ≤ ((box 8).2 : ℝ)) :
      ∀ i, ((box i).1 : ℝ) ≤ Function.update (nearPoint c h) 8 r i ∧
        Function.update (nearPoint c h) 8 r i ≤ ((box i).2 : ℝ) := by
    intro i
    fin_cases i
    · exact ⟨((Rat.cast_le (K := ℝ)).mpr hcl).trans hb.1,
        hb.2.1.trans ((Rat.cast_le (K := ℝ)).mpr hcu)⟩
    · exact ⟨((Rat.cast_le (K := ℝ)).mpr hhl).trans hb.2.2.1,
        hb.2.2.2.trans ((Rat.cast_le (K := ℝ)).mpr hhu)⟩
    · exact ht' 0
    · exact ht' 1
    · exact ht' 2
    · exact ht' 3
    · exact ht' 4
    · exact ht' 5
    · simpa using hr
  have hrOut := guarded_expression_encloses box _
    (hin ((box 8).1 : ℝ) ⟨le_rfl, (Rat.cast_le (K := ℝ)).mpr hru⟩) (nearRadicandExpr box) hrCheck
  have hra : intervalValue (Function.update (nearPoint c h) 8 ((box 8).1 : ℝ)) (nearRadicandExpr box) =
      27*(1+h)*(1+2*h)*(1+3*h)*zeroCenterRegularizingDerivative h 0 c := by
    have hc27 : intervalValue (Function.update (nearPoint c h) 8 ((box 8).1 : ℝ))
        (intervalConstant (box := box) 27) = 27 := by
      change ((27 : ℚ) : ℝ) = 27
      norm_num
    simp only [nearRadicandExpr, intervalValue_input, value_add, value_mul, value_1, value_2,
      value_3, hc27]
    norm_num <;> rfl
  rw [hra] at hrOut
  have hsqrt := sqrt_box_of_square_bounds hr₀ hr₁ hrl hrh hrOut
  have hpoint : Function.update (nearPoint c h) 8
      (Real.sqrt (27*(1+h)*(1+2*h)*(1+3*h)*zeroCenterRegularizingDerivative h 0 c)) =
      nearPoint c h := Function.update_eq_self _ _
  have hout := guarded_expression_encloses box _ (hin _ hsqrt) (nearLowerExpr box) hCheck
  rw [hpoint, nearLowerExpr_value] at hout
  exact ((by exact_mod_cast hpos : (0 : ℝ) < _).trans_le hout.1).trans_le
    (zeroCenterNearExpression_le_deriv2 hp hc hc₁)

theorem transferNear {r s : ZeroCenterRectangle} {box : Fin 9 → ℚ × ℚ}
    (h : nearValid r box) (he : r = s) : nearValid s box := he ▸ h

end RefinedBMV.FourSpectrumLift
